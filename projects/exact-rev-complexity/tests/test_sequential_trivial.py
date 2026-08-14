#!/usr/bin/env python3
"""**逐次モデルでは n*(p) = p で自明になる**ことの検査（2026-08-14）。

論拠（紙）: 逐次（1 ステップ 1 トグル）で時間 `T = 2n-1` を達成するとき、
総トグル数は `2n-1` ちょうど。各頂点は最低 1 回置かれ、sink 以外は最低 1 回消えるので
下限も `n + (n-1) = 2n-1`。**等号なので再計算の余地がゼロ**。
すると除去の順は `n-2, n-3, …, 0` に固定され（`v` を消すには `v-1` が要る）、
最初の除去より前に sink の配置が済んでいなければならない（`n-2` が消えたら二度と戻せない）。
よって**全配置が全除去より前**に起き、sink を置いた瞬間に `n` 個すべてが盤上にある。

したがって逐次では `p ≥ n` が必要、すなわち `n*(p) = p`。
**我々の `n*(p) = 7, 11, 17, 25, …` は並列モデルに固有の量である。**

この検査はその主張を SAT で裏づける: 逐次制約を入れると `n > p` はすべて UNSAT になり、
外すと（並列なら）SAT になる点があること。
"""
import sys

from ortools.sat.python import cp_model


def solve(n: int, p: int, sequential: bool, limit: float = 120.0):
    T = 2 * n - 1
    m = cp_model.CpModel()
    x = [[m.NewBoolVar(f"x{v}_{t}") for t in range(T + 1)] for v in range(n)]
    ch = [[m.NewBoolVar(f"c{v}_{t}") for t in range(T)] for v in range(n)]
    for v in range(n):
        m.Add(x[v][0] == 0)
        m.Add(x[v][T] == (1 if v == n - 1 else 0))
    for t in range(T):
        for v in range(n):
            m.Add(x[v][t] != x[v][t + 1]).OnlyEnforceIf(ch[v][t])
            m.Add(x[v][t] == x[v][t + 1]).OnlyEnforceIf(ch[v][t].Not())
            if v >= 1:                                  # 可逆性: 親が前後に要る
                m.AddImplication(ch[v][t], x[v - 1][t])
                m.AddImplication(ch[v][t], x[v - 1][t + 1])
        if sequential:                                  # 1 ステップ 1 トグル
            m.Add(sum(ch[v][t] for v in range(n)) <= 1)
    for t in range(T + 1):
        m.Add(sum(x[v][t] for v in range(n)) <= p)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = limit
    s.parameters.num_search_workers = 8
    st = s.Solve(m)
    return {cp_model.OPTIMAL: "SAT", cp_model.FEASIBLE: "SAT",
            cp_model.INFEASIBLE: "UNSAT"}.get(st, "打ち切り")


# n*(p)（並列・DRAT 証明書つき）。逐次なら n*(p) = p のはず。
NSTAR = {2: 2, 3: 4, 4: 7, 5: 11, 6: 17}


def main() -> int:
    fails = 0
    print(f"{'p':>3} {'n':>4} {'逐次':>6} {'並列':>6}  {'期待':>28}")
    for p, npar in NSTAR.items():
        cases = [(p, "逐次はぎりぎり可"), (p + 1, "逐次は不可・並列は可"), (npar, "並列の上限")]
        for n, why in cases:
            if n > npar:
                continue
            rs = solve(n, p, True)
            rp = solve(n, p, False)
            want_seq = "SAT" if n <= p else "UNSAT"
            ok = (rs == want_seq) and (rp == "SAT")
            if not ok:
                fails += 1
            print(f"{p:>3} {n:>4} {rs:>6} {rp:>6}  {why:>28}  {'' if ok else '✖'}")
    if fails:
        print(f"\n✖ {fails} 件が期待と違う。逐次で自明という主張が誤っている。")
        return 1
    print("\n✔ 逐次では n ≤ p のときだけ可（= n*(p) = p）。並列では n*(p) まで可。")
    print("  → n*(p) が非自明なのは**並列モデルに固有**である。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
