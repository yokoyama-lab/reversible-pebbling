"""ステージ定式化の到達範囲探査: 鎖の境界域・木・ピラミッドで各ソルバの限界を測る。

`data/mip_findings.md` の 8 ケースを超えて、
  - 鎖の pmin 境界（n = 2^{p-1}: 16, 32）と近傍（20, 24, 28）
  - pmin + 1 の余裕あり側（16/p6, 24/p7）
  - 完全二分木 h=3,4・ピラミッド h=3,4
を stage-{CP-SAT, Gurobi, SCIP} で解き、BFS 真値（状態数が許す範囲で計算）と
照合する。1 solve あたりの時間上限は --seconds（既定 60）。

K_max の方針: 一律 k_start = 4n（境界鎖では A* が 2n を超えるため。escalation の
INFEASIBLE 証明は下界証明と同等に高くつくので、最初から余裕を取る方が安い）。
OPTIMAL の返り値は K_max の余裕に依存しない（mip_stage docstring の単調性）。

    .venv/bin/python scripts/mip_stage_scale.py [--seconds S] [--solvers a,b] [--cases x,y] [--out CSV]
"""

from __future__ import annotations

import csv
import sys
import time
from math import comb
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import cpsat_stage  # noqa: E402
import mip_stage  # noqa: E402
from landauer import landauer_bfs  # noqa: E402
from revpebble import (  # noqa: E402
    bfs,
    chain,
    complete_binary_tree,
    pyramid,
    restrict_to_ancestors,
)

BFS_STATE_GUARD = 3_000_000


def cases():
    """(名前, dag, target, p, e) の列。"""
    for n, p in ((16, 5), (20, 6), (24, 6), (28, 6), (32, 6), (16, 6), (24, 7)):
        for e in (0, 1):
            yield f"chain({n})p{p}", chain(n), n, p, e
    # p は BFS の pmin で確認済み（cbt(3)=5, cbt(4)=6, pyr(3)=5, pyr(4)=6）
    for h, p in ((3, 5), (4, 6)):
        g = complete_binary_tree(h)
        yield f"cbt({h})p{p}", g, g.n - 1, p, 0
    for h, p in ((3, 5), (4, 6)):
        g = pyramid(h)
        yield f"pyr({h})p{p}", g, g.n - 1, p, 0


def truth(dag, target, p, e) -> int | None | str:
    """BFS 真値。状態数の見積りが上限を超えるときは "-"（未計算）。"""
    rg, rt = restrict_to_ancestors(dag, target)
    n_pebbleable = len(rg.pebbleable())
    est = sum(comb(n_pebbleable, k) for k in range(0, min(p, n_pebbleable) + 1))
    est *= e + 1
    if est > BFS_STATE_GUARD:
        return "-"
    if e == 0:
        return bfs(rg, rt, p)[0]
    return landauer_bfs(rg, rt, p, e)


SOLVERS = {
    "cpsat": lambda g, t, p, e, s, k: cpsat_stage.solve_stage_auto(
        g, t, p, e, max_seconds=s, k_start=k, k_limit=1024
    ),
    "gurobi": lambda g, t, p, e, s, k: mip_stage.solve_stage_auto(
        g, t, p, e, backend="gurobi", max_seconds=s, k_start=k, k_limit=1024
    ),
    "scip": lambda g, t, p, e, s, k: mip_stage.solve_stage_auto(
        g, t, p, e, backend="scip", max_seconds=s, k_start=k, k_limit=1024
    ),
}


def main() -> int:
    seconds = 60.0
    if "--seconds" in sys.argv:
        seconds = float(sys.argv[sys.argv.index("--seconds") + 1])
    solver_names = list(SOLVERS)
    if "--solvers" in sys.argv:
        solver_names = sys.argv[sys.argv.index("--solvers") + 1].split(",")
    only_cases = None
    if "--cases" in sys.argv:
        only_cases = set(sys.argv[sys.argv.index("--cases") + 1].split(","))
    out_path = None
    if "--out" in sys.argv:
        out_path = Path(sys.argv[sys.argv.index("--out") + 1])
        fh = out_path.open("w", newline="")
        writer = csv.writer(fh)
        writer.writerow(
            ["case", "e", "solver", "moves", "A", "status", "k_max",
             "bound", "seconds", "bfs", "agree"]
        )

    print(
        f"{'case':<14} {'e':>2} {'solver':<7} {'moves':>6} {'A':>4} "
        f"{'status':>9} {'K':>5} {'bound':>7} {'秒':>8} {'BFS':>6}  一致"
    )
    bad = 0
    for name, g, tgt, p, e in cases():
        if only_cases is not None and name not in only_cases:
            continue
        b = truth(g, tgt, p, e)
        rg, rt = restrict_to_ancestors(g, tgt)
        k_start = 4 * len(rg.pebbleable())
        for sname in solver_names:
            t0 = time.perf_counter()
            r = SOLVERS[sname](g, tgt, p, e, seconds, k_start)
            dt = time.perf_counter() - t0
            agree = "-"
            if isinstance(b, int) and r.moves is not None:
                agree = "○" if r.moves == b else "×"
                # FEASIBLE の暫定値が真値を上回るのは未証明なだけで誤りではない。
                # 誤値（健全性違反）は OPTIMAL の不一致と、真値未満の暫定値のみ。
                if agree == "×" and (r.status == "OPTIMAL" or r.moves < b):
                    bad += 1
            row = [name, e, sname, r.moves, r.intervals, r.status, r.k_max,
                   r.bound, round(dt, 2), b, agree]
            if out_path:
                writer.writerow(row)
                fh.flush()
            print(
                f"{name:<14} {e:>2} {sname:<7} {str(r.moves):>6} "
                f"{str(r.intervals):>4} {r.status:>9} {r.k_max:>5} "
                f"{'-' if r.bound is None else format(r.bound, '.1f'):>7} "
                f"{dt:>8.2f} {str(b):>6}  {agree}",
                flush=True,
            )
    if out_path:
        fh.close()
        print(f"→ {out_path}")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
