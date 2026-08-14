#!/usr/bin/env python3
"""ピラミッドの最小ピークを「**レベルの鎖の重みつきペブリング**」で近似する（2026-08-14）。

SAT の最適解を見ると、深さ `k` の頂点はおおむね同じ時間帯に居る。そこで
**同じ深さの h-k 個をまとめて 1 つの「重み h-k の超頂点」**とみなし、
深さの鎖 `0 → 1 → ⋯ → D` を時間最適 `T = 2D+1` でペブリングする問題に落とす。

* これは**レベル一様な戦略に限った上界**なので、真の `p_min` 以上になる
* 一致すれば「最適解はレベル一様に取れる」ことの強い証拠
* 一致しなければ、**レベル内で頂点ごとに振る舞いを変えるのが本質的**だとわかる

（`--family line` に相当する重み全 1 の場合が普通の鎖のペブリングになる。）
"""
import argparse
import sys

from ortools.sat.python import cp_model


def solve(weights: list[int], time_limit: float = 300.0):
    """深さの鎖 0→1→…→D、重み weights[k]、T = 2D+1。最小ピークを返す。"""
    D = len(weights) - 1
    T = 2 * D + 1
    m = cp_model.CpModel()
    x = [[m.NewBoolVar(f"x{k}_{t}") for t in range(T + 1)] for k in range(D + 1)]
    for k in range(D + 1):
        m.Add(x[k][0] == 0)
        m.Add(x[k][T] == (1 if k == D else 0))
    for t in range(T):
        for k in range(1, D + 1):
            ch = m.NewBoolVar(f"c{k}_{t}")
            m.Add(x[k][t] != x[k][t + 1]).OnlyEnforceIf(ch)
            m.Add(x[k][t] == x[k][t + 1]).OnlyEnforceIf(ch.Not())
            m.AddImplication(ch, x[k - 1][t])
            m.AddImplication(ch, x[k - 1][t + 1])
    p = m.NewIntVar(1, sum(weights), "p")
    for t in range(T + 1):
        m.Add(sum(weights[k] * x[k][t] for k in range(D + 1)) <= p)
    m.Minimize(p)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = time_limit
    s.parameters.num_search_workers = 8
    st = s.Solve(m)
    if st == cp_model.OPTIMAL:
        return int(s.ObjectiveValue()), "最適"
    if st == cp_model.FEASIBLE:
        return int(s.ObjectiveValue()), f"打ち切り(上界のみ・下界 {int(s.BestObjectiveBound())})"
    return None, "解なし/打ち切り"


MEASURED = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16, 8: 20, 9: 23, 10: 26,
            11: 29, 12: 32, 13: 37, 14: 41, 15: 45, 16: 49, 17: 54}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--hmax", type=int, default=17)
    ap.add_argument("--limit", type=float, default=300.0)
    a = ap.parse_args()
    print(f"  {'h':>3} {'|V|':>5} {'実測p_min':>9} {'レベル一様':>10} {'差':>4} {'状態':>10}")
    for h in range(2, a.hmax + 1):
        w = [h - k for k in range(h)]          # 深さ k の頂点数
        val, st = solve(w, a.limit)
        meas = MEASURED.get(h)
        d = "" if (val is None or meas is None) else f"{val - meas:+d}"
        print(f"  {h:>3} {h * (h + 1) // 2:>5} {str(meas):>9} {str(val):>10} {d:>4} {st:>10}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
