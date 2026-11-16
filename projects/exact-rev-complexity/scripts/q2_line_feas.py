#!/usr/bin/env python3
"""鎖 `n`・ピーク `p`・時間最適 `T=2n-1` の**実行可能性**を CP-SAT で判定する（2026-08-14）。

cadical（CNF）と**独立なエンジン**なので、フロンティアの点を別系統から攻める。
⚠ 打ち切りは結果ではない。`最適/実行可能/実行不能` のみを結果として扱う。
"""
import argparse
import os
import sys
import time

from ortools.sat.python import cp_model

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                   "data", "q2_line_feas.csv")


def feas(n: int, p: int, limit: float, workers: int):
    T = 2 * n - 1
    m = cp_model.CpModel()
    x = [[m.NewBoolVar(f"x{v}_{t}") for t in range(T + 1)] for v in range(n)]
    for v in range(n):
        m.Add(x[v][0] == 0)
        m.Add(x[v][T] == (1 if v == n - 1 else 0))
    for t in range(T):
        for v in range(1, n):
            ch = m.NewBoolVar(f"c{v}_{t}")
            m.Add(x[v][t] != x[v][t + 1]).OnlyEnforceIf(ch)
            m.Add(x[v][t] == x[v][t + 1]).OnlyEnforceIf(ch.Not())
            m.AddImplication(ch, x[v - 1][t])
            m.AddImplication(ch, x[v - 1][t + 1])
    for t in range(T + 1):
        m.Add(sum(x[v][t] for v in range(n)) <= p)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = limit
    s.parameters.num_search_workers = workers
    st = s.Solve(m)
    return {cp_model.OPTIMAL: "実行可能", cp_model.FEASIBLE: "実行可能",
            cp_model.INFEASIBLE: "実行不能"}.get(st, "打ち切り")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("ns", nargs="+", type=int)
    ap.add_argument("--limit", type=float, default=7200.0)
    ap.add_argument("--workers", type=int, default=4)
    a = ap.parse_args()
    if not os.path.exists(OUT):
        with open(OUT, "w") as f:
            f.write("p,n,result,sec\n")
    for n in a.ns:
        t0 = time.time()
        r = feas(n, a.p, a.limit, a.workers)
        with open(OUT, "a") as f:
            f.write(f"{a.p},{n},{r},{time.time() - t0:.0f}\n")
        print(f"p={a.p} n={n}: {r} ({time.time() - t0:.0f}s)", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
