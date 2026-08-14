"""BFS の届かない $n>20$ で $M^*$ の厳密値を狙う長時間実行（2026-08-10）。

## 位置づけ

`data/cpsat_findings.md` の「**BFS は $n\\le20$ まで出せているので、現時点で CP-SAT の
利得はゼロ**」を崩すのが目的。60 秒制限では 3 ソルバとも `chain(12) e=0` で落ちたが、
**遊休している計算機で時間を掛ければ届く可能性がある**。

- 届けば **BFS が出せない厳密値** = このプロジェクトで初めてソルバが利得を出す
- 届かなければ「$n$ 時間掛けても駄目」という**打ち切り位置の記録**になる。
  どちらでも `data/` に残す価値がある

## 守っていること

- **BFS と重なる域（$n\\le20$）を先に走らせて全点一致を確認**してから、外挿域へ進む。
  一致しなければ定式化の誤りであり、そこで止める（`cpsat_pebble.py` の docstring の方針）
- **`solve_intervals_auto` を使う**（$C$ を増やして収束を見る）。単発の結果を最適値として
  報告してはいけない
- 健全性: $M^*$ は必ず**奇数**（$2A-1$ の形）
- 結果は 1 ケースごとに追記する（途中で殺されても、そこまでが残る）

## 使い方

    .venv/bin/python scripts/frontier_run.py --backend cpsat --out data/frontier_cpsat.jsonl
    .venv/bin/python scripts/frontier_run.py --backend gurobi --out data/frontier_gurobi.jsonl
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

os.environ.setdefault("GRB_LICENSE_FILE", str(Path.home() / ".config/gurobi/gurobi.lic"))

from revpebble import bfs, chain  # noqa: E402
from landauer import landauer_bfs  # noqa: E402


def bfs_value(n: int, p: int, e: int) -> int | None:
    """BFS の厳密値。届かない n では None（例外は握り潰さず None に落とす）。"""
    try:
        return landauer_bfs(chain(n), n, p, e) if e else bfs(chain(n), n, p)[0]
    except (MemoryError, RecursionError):
        return None


def solve(backend: str, n: int, p: int, e: int, seconds: float, workers: int):
    # ブロック標準形（`mip_stage.py`）。interval 版より実測 228〜1580 倍速い
    # （`data/mip_stage_findings.md`）。indicator 制約が 5,748 → 0 になるのが効いている。
    if backend.startswith("stage-"):
        from mip_stage import solve_stage_auto

        return solve_stage_auto(
            chain(n), n, p=p, e=e, max_seconds=seconds, workers=workers,
            backend=backend.split("-", 1)[1],
        )
    if backend == "cpsat":
        from cpsat_interval import solve_intervals_auto

        return solve_intervals_auto(
            chain(n), n, p=p, e=e, max_seconds=seconds, workers=workers
        )
    from mip_interval import solve_intervals_auto as mip_auto  # type: ignore

    return mip_auto(
        chain(n), n, p=p, e=e, max_seconds=seconds, workers=workers, backend=backend
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--backend", required=True,
                    choices=["cpsat", "gurobi", "scip",
                             "stage-gurobi", "stage-scip"])
    ap.add_argument("--out", required=True)
    ap.add_argument("--seconds", type=float, default=3600.0, help="1 ケースの上限秒")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--verify-max", type=int, default=12,
                    help="この n まではBFSと突き合わせる（重なる域）")
    args = ap.parse_args()

    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)

    # 重なる域 → 外挿域。小さい順に進み、2 連続で時間切れなら打ち切る。
    ns = [8, 12, 16, 20, 22, 24, 28, 32, 40]
    consecutive_unknown = 0

    for n in ns:
        p = 1 + (n - 1).bit_length()
        for e in (0, 1):
            t0 = time.time()
            r = solve(args.backend, n, p, e, args.seconds, args.workers)
            dt = time.time() - t0
            ref = bfs_value(n, p, e) if n <= args.verify_max else None

            # **FEASIBLE を厳密値として記録してはいけない**（上界にすぎない）。
            # ここを混ぜると「打ち切り値を結果と読む」型の事故になる。
            #
            # cap_tight は**この分類には使わない**。`solve_intervals_auto` は
            # 「次の C で改善せず、かつその C に余裕がある」ことで収束を判定して
            # best を返すので、**返ってきた記録自身の cap_tight は非収束を意味しない**
            # （最初これを条件に入れて n=8 まで全部弾いた。私の読み違い）。
            # ただし監査のために値は残す。auto が UNKNOWN で早期 return した場合は
            # 収束が確立していないので、そこは status に現れる。
            if r.moves is None:
                kind = "none"
            elif r.status == "OPTIMAL":
                kind = "exact"
            else:
                kind = "upper_bound"    # FEASIBLE 等。上界のみ

            rec = {
                "backend": args.backend, "n": n, "p": p, "e": e,
                "kind": kind,
                "value": r.moves if kind == "exact" else None,
                "upper_bound": r.moves,
                "intervals": r.intervals, "status": r.status,
                # StageResult は cap を持たない（interval 版のみ）。無ければ None。
                "cap": getattr(r, "cap", None),
                "cap_tight": getattr(r, "cap_tight", None),
                "seconds": round(dt, 2), "bfs": ref,
                "verified": ref is not None,
                # 値が出ていないケースは「不一致」ではなく「未判定」。
                # **`OPTIMAL` のときだけ等値を要求する。** `FEASIBLE` の `r.moves` は
                # 暫定解（incumbent）で、真の最適値より**大きい**のが正常。
                # 2026-08-10 に、この区別が無かったため `n=20,e=1` の incumbent 61 を
                # BFS の 57 と等値比較して「定式化の誤り」と誤判定し、19 時間走った
                # ジョブが最後に自死した。
                "agrees": (
                    (r.moves == ref) if (ref is not None and r.moves is not None
                                         and r.status == "OPTIMAL")
                    else None
                ),
                "odd_ok": (r.moves is None or r.moves % 2 == 1),
            }
            with out.open("a") as f:
                f.write(json.dumps(rec) + "\n")
            print(json.dumps(rec, ensure_ascii=False), flush=True)

            # BFS と重なる域で食い違ったら、外挿域の値は信用できない。止める。
            # ただし **`OPTIMAL` と `FEASIBLE` を区別する**:
            #   OPTIMAL  → BFS と等しくなければ定式化の誤り
            #   FEASIBLE → incumbent なので `>= ref` が正常。**`< ref` なら本物の誤り**
            #              （真の最適値より小さい「解」は実行不能解を許している証拠）
            if ref is not None and r.moves is not None:
                if r.status == "OPTIMAL" and r.moves != ref:
                    print(f"!! BFS 不一致 (n={n}, e={e}, OPTIMAL): {r.moves} != {ref}。"
                          "定式化の誤り。", file=sys.stderr, flush=True)
                    return 1
                if r.status != "OPTIMAL" and r.moves < ref:
                    print(f"!! 実行不能解 (n={n}, e={e}, {r.status}): "
                          f"incumbent {r.moves} < 真の最適 {ref}。制約が緩い。",
                          file=sys.stderr, flush=True)
                    return 1
            if r.moves is not None and r.moves % 2 == 0:
                print(f"!! M* が偶数 (n={n}, e={e}): {r.moves}。2A-1 の形に反する。",
                      file=sys.stderr, flush=True)
                return 1

            # 厳密値が出ていなければ未解決として数える（上界だけでは前進ではない）
            consecutive_unknown = 0 if kind == "exact" else consecutive_unknown + 1
        if consecutive_unknown >= 2:
            print(f"# n={n} で e=0,1 とも時間切れ。ここで打ち切る。", flush=True)
            break
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
