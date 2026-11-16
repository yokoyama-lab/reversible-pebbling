"""証明の部分主張を機械検査する（P8）。

## 何を確かめるか

P1 の主張は「1 回だけ置かれる頂点は高々 $p$ 個」（$r\\le p$）だった。
これを出す最短の道は次の**部分主張**である。

> **(H) 目標を最後に置く瞬間 $T$ に、1 回組の頂点はすべて載っている。**

(H) が成り立てば、その瞬間のペブル数は高々 $p$ なので $r\\le p$ が**直ちに従う**
（Helly の定理も要らない）。

## なぜ (H) が非自明か（証明の穴を記録しておく）

素朴な議論はこう進む: $v$ が 1 回だけ置かれ $u_v$ で取られたとすると、
$v$ の真の子孫は $u_v$ 以降**凍結**されるはずで、目標も子孫だから
$u_v$ より後に置けない、よって $T\\le u_v$。

**この「凍結」が一般には成り立たない。** $x$ を $v$ の子孫とし、$v$ から $x$ への
道の最後の辺を $y_0\\to x$ とすると、$y_0$ が $u_v$ の時点で既に載っていて
そのまま載り続ける場合、$x$ は $u_v$ 以降も動かせてしまう。

→ **3 行では終わらない。** これは `docs/94_paper_queue.md` P2 の
「初等的な主張は証明の短さが folklore の証拠」という基準に照らすと、
**folklore でない側の証拠**である。

## 検査の対象

1. 族の証書（`data/families/certs/`。台帳の `exhaustive` 行すべて）
2. 小 DAG 全数（$n\\le6$ の非同型 DAG × 全目標 × 全 $p$）

**どちらも「BFS の距離表から復元した正準なスケジュール」1 本についての検査**である。
全ての合法スケジュールについての主張ではない（そこは証明の仕事）。
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import exp01b_engine as fast  # noqa: E402
from exp02_dags import edges_to_dag, enumerate_nonisomorphic  # noqa: E402
from revpebble import Dag, restrict_to_ancestors  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = ROOT / "data" / "families" / "once_at_target.csv"
FIELDS = ["source", "tag", "N", "p", "r", "held_at_T", "ok"]


def check_schedule(seq: list[tuple[str, int]], target: int) -> tuple[int, int, bool]:
    """(1 回組の個数 r, 時刻 T に載っている 1 回組の個数, (H) が成り立つか)。

    $T$ = 目標を**最後に**置いた直後の時刻。
    """
    counts: dict[int, int] = {}
    for kind, v in seq:
        if kind == "put":
            counts[v] = counts.get(v, 0) + 1
    once = {v for v, c in counts.items() if c == 1}
    # 目標の最後の put の位置
    last = max(i for i, (k, v) in enumerate(seq) if k == "put" and v == target)
    state: set[int] = set()
    for i, (kind, v) in enumerate(seq):
        if kind == "put":
            state.add(v)
        else:
            state.discard(v)
        if i == last:
            break
    held = len(once & state)
    return len(once), held, held == len(once)


def rows_families() -> list[dict]:
    import json

    from family_atlas import CERT_DIR, read_rows
    from families import anc, build

    out: list[dict] = []
    for row in read_rows():
        if row["status"] != "exhaustive" or not row["cert"]:
            continue
        params = tuple(int(x) for x in row["params"].split(":"))
        ga, t = anc(build(row["family"], params))
        certs = json.loads((CERT_DIR / row["cert"]).read_text(encoding="utf-8"))
        seq = [(k, v) for k, v in certs[row["p"]]]
        r, held, ok = check_schedule(seq, t)
        out.append({
            "source": "family", "tag": f"{row['family']}({row['params']})",
            "N": row["pebbleable"], "p": row["p"], "r": r,
            "held_at_T": held, "ok": int(ok),
        })
    return out


def rows_small_dags(nmax: int) -> list[dict]:
    out: list[dict] = []
    for n in range(1, nmax + 1):
        for idx, edges in enumerate(enumerate_nonisomorphic(n)):
            g: Dag = edges_to_dag(edges, n, name=f"d{n}_{idx}")
            for target in range(n):
                ga, t = restrict_to_ancestors(g, target)
                N = ga.n - len(ga.free)
                if N == 0:
                    continue
                for p in range(1, N + 2):
                    seq = fast.schedule(ga, t, p)
                    if seq is None:
                        continue
                    r, held, ok = check_schedule(seq, t)
                    out.append({
                        "source": "dag", "tag": f"d{n}_{idx}/t{target}",
                        "N": N, "p": p, "r": r, "held_at_T": held, "ok": int(ok),
                    })
    return out


def cmd_build(nmax: int) -> int:
    rows = rows_families()
    print(f"族の証書: {len(rows)} 行 / 反例 {sum(1 for r in rows if not r['ok'])}", flush=True)
    d = rows_small_dags(nmax)
    print(f"小 DAG   : {len(d)} 行 / 反例 {sum(1 for r in d if not r['ok'])}", flush=True)
    rows.extend(d)
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(rows)
    bad = [r for r in rows if not r["ok"]]
    for b in bad[:5]:
        print(f"  反例 {b['tag']} p={b['p']}: r={b['r']} だが T で載っているのは {b['held_at_T']}")
    print(f"wrote {CSV_PATH}: {len(rows)} 行 / 反例 {len(bad)}")
    return 0


def cmd_verify() -> int:
    if not CSV_PATH.exists():
        print("OK  once_at_target.csv はまだ無い（P8 未実施）")
        return 0
    bad = n = 0
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        for r in csv.DictReader(fh):
            n += 1
            if r["ok"] != "1":
                bad += 1
            if int(r["r"]) > int(r["p"]):
                print(f"NG: {r['tag']} p={r['p']}: r={r['r']} > p（P1 の主張が破れた）")
                return 1
    if bad:
        print(f"NG: (H) の反例が {bad} 件")
        return 1
    print(f"OK  (H)「1 回組は目標の最終配置時に全て載る」に {n} 行で反例なし")
    return 0


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--nmax", type=int, default=6)
    ns = ap.parse_args()
    if ns.build:
        raise SystemExit(cmd_build(ns.nmax))
    if ns.verify:
        raise SystemExit(cmd_verify())
    ap.print_help()
