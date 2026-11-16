#!/usr/bin/env python3
"""鎖の p_min を **CP-SAT で直接最小化**する（2026-08-14）。

鎖では深さごとの頂点が 1 つなので「レベル一様」は制約にならない。よって
`q2_level_weighted.solve([1]*n)` は **p_min(line n) そのもの**を厳密に与える。
`p_min(n) = min{p : n ≤ n*(p)}` なので、これは `n*(p)` を求めるのと同じこと。

既知 13 点（n=4..48）で一致を確認済み。**打ち切りは結果ではない**ので、
`最適` でない行は `n*` の確定に使わないこと。
"""
import argparse
import csv
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from q2_level_weighted import solve  # noqa: E402

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                   "data", "q2_line_cpsat.csv")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("ns", nargs="+", type=int)
    ap.add_argument("--limit", type=float, default=3600.0)
    a = ap.parse_args()
    done = set()
    if os.path.exists(OUT):
        with open(OUT) as f:
            done = {int(r["n"]) for r in csv.DictReader(f)}
    else:
        with open(OUT, "w") as f:
            f.write("n,p_min,status,sec\n")
    for n in a.ns:
        if n in done:
            continue
        t0 = time.time()
        v, st = solve([1] * n, a.limit)
        with open(OUT, "a") as f:
            f.write(f"{n},{v},{st},{time.time() - t0:.1f}\n")
        print(f"n={n}: {v} ({st}, {time.time() - t0:.0f}s)", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
