"""候補2: nauty (`geng`|`directg`) をストリーミングで流し、n=8,9 の (P,R) 統計を

**全件をメモリに保持せずに**集計する。時間予算つき・チェックポイント再開可能。

## 設計

`geng -c n | directg -a -o -T -q` の出力（1行=1有向グラフ）を Python の
subprocess パイプで受け取り、1行ずつ:

1. パースして単一シンク判定（`docs/idea02_separation_onset.md` §3-1 の議論により
   単一シンクなら全頂点到達可能が自動的に従う）。
2. シンクでなければ捨てる。シンクならトポロジカル順に再ラベルし `(P,R)` を計算。
3. 集計（分布・最大ギャップ・合流コスト上界の違反チェック）だけを保持し、
   個々のグラフは（最大ギャップの実例など「特筆すべき1個」を除いて）捨てる
   — n=8,9 は全件保持すると数百万〜数千万件になりメモリを圧迫するため。

**再開**: チェックポイントに「これまでに読んだ生の行数」を保存し、再実行時は
その行数だけ出力を読み捨ててから続きを処理する（`geng`/`directg` は決定的なので
同じ行が同じ順序で再生される）。読み捨て自体は軽い（フル処理の1/200程度の コスト）。

## 実行

```bash
python3 scripts/exp02_n8_stream.py --n 8 --budget 480   # 完了するまで繰り返し実行
python3 scripts/exp02_n8_stream.py --n 8 --status
```

**正しさの前提**: nauty 経路は `tests/test_exp02_nauty.py` で n<=6 の自作全数探索と
完全一致することを確認済み（`scripts/exp02_nauty.py`）。この n=8,9 ストリーミング版は
同じフィルタ・再ラベル処理を使う（`exp02_nauty` のロジックをインライン化・簡略化）。
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp02_confluence import chain_r, depth_edges, num_confluent  # noqa: E402
from exp02_dags import edges_to_dag  # noqa: E402
from revpebble import pmin as pmin_rev  # noqa: E402
from stdpebble import pmin_std  # noqa: E402

DATA_DIR = Path(__file__).resolve().parents[1] / "data"


def checkpoint_path(n: int) -> Path:
    return DATA_DIR / f"exp02_n{n}_stream_checkpoint.json"


def _parse_line(line: str) -> list[tuple[int, int]]:
    parts = [int(x) for x in line.split()]
    ne = parts[1]
    rest = parts[2:]
    return [(rest[2 * k], rest[2 * k + 1]) for k in range(ne)]


def _topo_relabel(edges: list[tuple[int, int]], n: int, sink: int) -> frozenset[tuple[int, int]]:
    succs: list[list[int]] = [[] for _ in range(n)]
    indeg = [0] * n
    for i, j in edges:
        succs[i].append(j)
        indeg[j] += 1
    order: list[int] = []
    queue = [v for v in range(n) if indeg[v] == 0]
    iw = indeg[:]
    while queue:
        v = queue.pop()
        order.append(v)
        for w in succs[v]:
            iw[w] -= 1
            if iw[w] == 0:
                queue.append(w)
    relabel = {old: new for new, old in enumerate(order)}
    return frozenset((relabel[i], relabel[j]) for i, j in edges)


def _open_pipe(n: int) -> subprocess.Popen:
    directg = subprocess.Popen(
        ["directg", "-a", "-o", "-T", "-q"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
    )
    subprocess.Popen(["geng", "-c", str(n)], stdout=directg.stdin, stderr=subprocess.DEVNULL)
    directg.stdin.close()  # type: ignore[union-attr]
    return directg


def load_checkpoint(n: int) -> dict:
    path = checkpoint_path(n)
    if path.exists():
        with open(path) as f:
            return json.load(f)
    return {
        "raw_processed": 0,
        "kept_processed": 0,
        "dist": {},
        "eq_count": 0,
        "gt_count": 0,
        "max_gap": -1,
        "max_gap_edges": None,
        "max_gap_p": None,
        "max_gap_r": None,
        "confluence_bound_violations": [],
        "done": False,
    }


def save_checkpoint(n: int, state: dict) -> None:
    DATA_DIR.mkdir(exist_ok=True)
    path = checkpoint_path(n)
    tmp = path.with_suffix(".json.tmp")
    with open(tmp, "w") as f:
        json.dump(state, f)
    tmp.replace(path)


def run_chunk(n: int, budget_sec: float, *, quiet: bool = False) -> dict:
    state = load_checkpoint(n)
    if state["done"]:
        if not quiet:
            print("既に完了済み。")
        return state

    proc = _open_pipe(n)
    assert proc.stdout is not None
    t0 = time.time()

    skip = state["raw_processed"]
    if not quiet and skip:
        print(f"resume: 生の行を{skip}件読み捨ててから続行")

    raw_i = 0
    it = iter(proc.stdout)
    # 読み捨てフェーズ（軽い: パースしない）。
    while raw_i < skip:
        line = next(it, None)
        if line is None:
            break
        raw_i += 1

    processed_this_chunk = 0
    while True:
        line = next(it, None)
        if line is None:
            state["done"] = True
            break
        raw_i += 1
        edges = _parse_line(line.decode())
        outdeg = [0] * n
        for i, _j in edges:
            outdeg[i] += 1
        sinks = [v for v in range(n) if outdeg[v] == 0]
        if len(sinks) == 1:
            edges_fs = _topo_relabel(edges, n, sinks[0])
            g = edges_to_dag(edges_fs, n)
            p = pmin_std(g, n - 1)
            r = pmin_rev(g, n - 1)
            assert p is not None and r is not None
            key = f"{p},{r}"
            state["dist"][key] = state["dist"].get(key, 0) + 1
            if p == r:
                state["eq_count"] += 1
            else:
                state["gt_count"] += 1
            gap = r - p
            if gap > state["max_gap"]:
                state["max_gap"] = gap
                state["max_gap_edges"] = sorted([list(e) for e in edges_fs])
                state["max_gap_p"] = p
                state["max_gap_r"] = r
            d = depth_edges(edges_fs, n)
            ce = sum(max(0, v - 1) for v in _indeg_list(edges_fs, n))
            residual = r - max(p, chain_r(d))
            if residual > ce:
                state["confluence_bound_violations"].append(
                    {"edges": sorted([list(e) for e in edges_fs]), "p": p, "r": r, "residual": residual, "ce": ce}
                )
            state["kept_processed"] += 1
            processed_this_chunk += 1
        state["raw_processed"] = raw_i

        if time.time() - t0 > budget_sec:
            break

    proc.terminate()
    dt = time.time() - t0
    if not quiet:
        print(
            f"chunk: raw {skip}->{state['raw_processed']} "
            f"(+{state['raw_processed'] - skip} 行, {processed_this_chunk} 件が単一シンク) "
            f"in {dt:.1f}s"
            + (" [完了]" if state["done"] else " [予算切れ、再実行で継続]")
        )
        print(f"累積 kept={state['kept_processed']}, eq={state['eq_count']}, gt={state['gt_count']}")
        print(f"max_gap={state['max_gap']} (p={state['max_gap_p']}, r={state['max_gap_r']})")
        print(f"confluence_bound 違反件数: {len(state['confluence_bound_violations'])}")

    save_checkpoint(n, state)
    return state


def _indeg_list(edges: frozenset[tuple[int, int]], n: int) -> list[int]:
    indeg = [0] * n
    for _i, j in edges:
        indeg[j] += 1
    return indeg


def status(n: int) -> None:
    state = load_checkpoint(n)
    print(
        f"n={n}: raw_processed={state['raw_processed']}, kept={state['kept_processed']}, "
        f"eq={state['eq_count']}, gt={state['gt_count']}, max_gap={state['max_gap']}, "
        f"done={state['done']}"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=8)
    parser.add_argument("--budget", type=float, default=480.0)
    parser.add_argument("--status", action="store_true")
    args = parser.parse_args()
    if args.status:
        status(args.n)
    else:
        run_chunk(args.n, args.budget)
