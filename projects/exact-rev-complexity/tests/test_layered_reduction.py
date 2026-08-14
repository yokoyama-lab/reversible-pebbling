#!/usr/bin/env python3
"""還元定理（`full_layered_reduction`）の実測での裏づけ（2026-08-14）。

Lean で証明したこと（`lean/Revgarbage/ParPebbleWindow.lean`）:

> 親が「深さがちょうど 1 小さい頂点**すべて**」である層状 DAG では、**任意の `T` について**
> $p_{\\min}(G, T) = \\min_Q \\max_t |\\{v : \\mathrm{dep}\\,v \\in Q_t\\}|$
> （`Q` は深さの鎖 `0→1→…→D` の長さ `T` の合法なペブリング）。

この検査は、その等式を**独立な 2 つのソルバ**で突き合わせる:

* 左辺 = `cadical` に `|V| × (T+1)` 変数の CNF を解かせた値
* 右辺 = CP-SAT に `(D+1) × (T+1)` 変数の重みつき問題を解かせた値

⚠ **素の CNF を使う**（`--window` は `T = 2D+1` 前提の制約なので、
時間を延ばした点には使ってはならない）。
"""
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import q2_cnf  # noqa: E402
from ortools.sat.python import cp_model  # noqa: E402


def build_layers(ns):
    assert ns[-1] == 1
    idx, par, dep = [], [], []
    for l, n in enumerate(ns):
        cur = []
        for _ in range(n):
            cur.append(len(par))
            par.append(list(idx[l - 1]) if l else [])
            dep.append(l)
        idx.append(cur)
    return par, idx[-1][0], dep


def sat(par, sink, p, T):
    c = q2_cnf.build(par, sink, p, T)          # 素の CNF
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        path = f.name
    c.dump(path)
    try:
        r = subprocess.run(["cadical", path, "-q"], capture_output=True,
                           text=True, timeout=1800)
        out = [ln for ln in r.stdout.splitlines() if ln.startswith("s ")]
        return None if not out else ("SATISFIABLE" in out[0] and "UNSAT" not in out[0])
    finally:
        os.unlink(path)


def chain_weighted(ws, T, limit=180.0):
    D = len(ws) - 1
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
    p = m.NewIntVar(1, sum(ws), "p")
    for t in range(T + 1):
        m.Add(sum(ws[k] * x[k][t] for k in range(D + 1)) <= p)
    m.Minimize(p)
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = limit
    s.parameters.num_search_workers = 4
    st = s.Solve(m)
    return int(s.ObjectiveValue()) if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None


# (層の大きさ, 追加で試す時間のオフセット)
CASES = [
    ([1, 1, 1, 1], [0, 2]),
    ([2, 2, 2, 1], [0, 2, 4]),
    ([3, 3, 3, 1], [0, 2]),
    ([4, 4, 4, 1], [0, 2]),
    ([2, 2, 2, 2, 1], [0, 2, 4]),
    ([3, 3, 3, 3, 1], [0, 2]),
    ([5, 4, 3, 2, 1], [0, 2]),
    ([4, 2, 4, 2, 1], [0, 2]),
    ([1, 4, 1, 4, 1], [0, 2]),
    ([2, 2, 2, 2, 2, 2, 1], [0, 2]),
    ([2] * 11 + [1], [0, 2, 4]),      # 非自明なトレードオフ（T_opt で 11・+2 で 9）
]


def main() -> int:
    fails = 0
    print(f"{'層の大きさ':>26} {'T':>4} {'鎖(CP-SAT)':>11} {'p_min(SAT)':>11} {'判定':>5}")
    for ns, offs in CASES:
        par, sink, dep = build_layers(ns)
        D = len(ns) - 1
        for off in offs:
            T = 2 * D + 1 + off
            u = chain_weighted(ns, T)
            v = None
            if u is not None:
                for p in range(2, u + 1):
                    r = sat(par, sink, p, T)
                    if r is None:
                        break
                    if r:
                        v = p
                        break
            ok = (u is not None and u == v)
            if not ok:
                fails += 1
            print(f"{str(ns):>26} {T:>4} {str(u):>11} {str(v):>11} "
                  f"{'✔' if ok else '✖':>5}")
    if fails:
        print(f"\n✖ {fails} 件が不一致。還元定理と実測が食い違う。"
              f"**まず実測の実装（親の集合が本当に層の全体か）を疑うこと。**")
        return 1
    print(f"\n✔ {sum(len(o) for _, o in CASES)} 点すべてで "
          f"「p_min(G,T) = 深さの鎖の重みつき最適値」")
    return 0


if __name__ == "__main__":
    sys.exit(main())
