#!/usr/bin/env python3
"""ピラミッドのピーク下界を**拡大性**で強める（2026-08-14）。

`peak_lower_*`（数え上げ）は $h \\le 5$ でしかタイトでなかった。ピラミッドには
**拡大性**がある——層 $k$ の頂点集合 $A$ の親は $N(A) = A \\cup (A+1)$ なので
$|N(A)| \\ge |A| + 1$。これを使うと下界が大きく上がる。

層ごとの個数 $a_k(t) = |S_k(t)|$ と変化数 $c_k(t) = |S_k(t) \\triangle S_k(t+1)|$ だけの
**抽象**に落として整数計画で最小化する。使う事実:

| 事実 | 根拠 |
|---|---|
| 窓 $a_k(t)=0$（$t \\notin [k+1, 2D-k]$） | `time_window_dep`（層1） |
| 両端強制 $a_k = n_k$（$t = k{+}1, k{+}2, 2D{-}k{-}1, 2D{-}k$） | `present_at_dep` / `present_at_end_dep`（層1） |
| sink は $t \\ge D+1$ で常在 | `sink_at_and_stays_dep`（層1） |
| $c_k(t) \\ge \\|a_k(t) - a_k(t{+}1)\\|$ | 対称差の初等的性質 |
| **拡大性** $c_k(t) \\ge 1 \\Rightarrow a_{k-1}(t), a_{k-1}(t{+}1) \\ge c_k(t)+1$ | ピラミッドの親構造（未機械証明） |

**どの制約も合法なペブリングが必ず満たす**ので、この整数計画の最適値は $p_{\\min}$ の下界。

⚠ **打ち切りは下界として使えない**（最適値でなければ下界にならない）。
"""
import argparse
import sys

from ortools.sat.python import cp_model


def bound(h: int, exp_gain: int = 1, limit: float = 300.0):
    D = h - 1
    T = 2 * D + 1
    n = [h - k for k in range(h)]
    m = cp_model.CpModel()
    a = [[m.NewIntVar(0, n[k], f"a{k}_{t}") for t in range(T + 1)] for k in range(D + 1)]
    c = [[m.NewIntVar(0, n[k], f"c{k}_{t}") for t in range(T)] for k in range(D + 1)]
    for k in range(D + 1):
        for t in range(T + 1):
            if k == D:
                m.Add(a[k][t] == (0 if t < D + 1 else 1))
            else:
                if t < k + 1 or t > 2 * D - k:
                    m.Add(a[k][t] == 0)
                if t in (k + 1, k + 2, 2 * D - k - 1, 2 * D - k):
                    m.Add(a[k][t] == n[k])
        for t in range(T):
            m.Add(c[k][t] >= a[k][t] - a[k][t + 1])
            m.Add(c[k][t] >= a[k][t + 1] - a[k][t])
            if k >= 1:
                b = m.NewBoolVar(f"b{k}_{t}")
                m.Add(c[k][t] >= 1).OnlyEnforceIf(b)
                m.Add(c[k][t] == 0).OnlyEnforceIf(b.Not())
                m.Add(a[k - 1][t] >= c[k][t] + exp_gain).OnlyEnforceIf(b)
                m.Add(a[k - 1][t + 1] >= c[k][t] + exp_gain).OnlyEnforceIf(b)
    p = m.NewIntVar(1, sum(n), "p")
    for t in range(T + 1):
        m.Add(sum(a[k][t] for k in range(D + 1)) <= p)
    m.Minimize(p)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = limit
    s.parameters.num_search_workers = 8
    st = s.Solve(m)
    if st == cp_model.OPTIMAL:
        return int(s.ObjectiveValue()), "最適"
    if st == cp_model.FEASIBLE:
        return None, f"打ち切り（下界にならない。既知の下界 {int(s.BestObjectiveBound())}）"
    return None, "実行不能"


MEASURED = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16, 8: 20, 9: 23, 10: 26, 11: 29,
            12: 32, 13: 37, 14: 41, 15: 45, 16: 49, 17: 54, 18: 58}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--hmax", type=int, default=18)
    ap.add_argument("--limit", type=float, default=300.0)
    a = ap.parse_args()
    bad = 0
    print(f"  {'h':>3} {'数え上げ':>8} {'拡大性つき':>10} {'実測':>5} {'比':>6} {'状態':>6}")
    for h in range(2, a.hmax + 1):
        v, st = bound(h, limit=a.limit)
        meas = MEASURED.get(h)
        cnt = 3 if h == 2 else 2 * h
        if v is not None and meas is not None and v > meas:
            bad += 1
            st += " ✖下界が実測を超えた"
        r = f"{v / meas:.2f}" if (v and meas) else "—"
        print(f"  {h:>3} {cnt:>8} {str(v):>10} {str(meas):>5} {r:>6} {st:>6}")
    if bad:
        print(f"\n✖ {bad} 点で下界が実測を超えた。緩和になっていないので使ってはならない。")
        return 1
    print("\n✔ すべての点で下界 ≤ 実測（緩和として健全）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
