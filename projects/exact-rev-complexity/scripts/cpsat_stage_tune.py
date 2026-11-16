"""stage-CP-SAT のフロンティア拡張の試み: chain(24) p=6 e=0（真値 109）。

60 秒既定では FEASIBLE 113 / bound 49 止まり。CP-SAT 側のパラメータと
決定戦略（act を先頭から埋める）で閉じられるかを測る。

    .venv/bin/python scripts/cpsat_stage_tune.py [--seconds S]
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from ortools.sat.python import cp_model  # noqa: E402

from revpebble import chain, restrict_to_ancestors  # noqa: E402


def build(n: int, p: int, k_max: int):
    dag, target = restrict_to_ancestors(chain(n), n)
    verts = list(dag.pebbleable())
    K = k_max
    m = cp_model.CpModel()
    x = {(v, k): m.new_bool_var(f"x{v}_{k}") for v in verts for k in range(K + 1)}
    put = {(v, k): m.new_bool_var(f"p{v}_{k}") for v in verts for k in range(1, K + 1)}
    tk = {(v, k): m.new_bool_var(f"t{v}_{k}") for v in verts for k in range(1, K + 1)}
    act = {k: m.new_bool_var(f"act{k}") for k in range(1, K + 1)}
    for v in verts:
        m.add(x[v, 0] == 0)
        m.add(x[v, K] == (1 if v == target else 0))
        m.add(sum(put[v, k] for k in range(1, K + 1)) >= 1)
    for k in range(1, K + 1):
        m.add(sum(put[v, k] for v in verts) == act[k])
        if k < K:
            m.add_implication(act[k + 1], act[k])
        m.add(sum(x[v, k - 1] for v in verts) + (p - 2) * (1 - act[k]) <= p - 1)
        for v in verts:
            m.add(x[v, k] == x[v, k - 1] + put[v, k] - tk[v, k])
            m.add(put[v, k] + x[v, k - 1] <= 1)
            m.add(tk[v, k] <= x[v, k - 1] + put[v, k])
            m.add_implication(tk[v, k], act[k])
            if k < K:
                m.add(tk[v, k] + put[v, k + 1] <= 1)
            need = [u for u in dag.preds[v] if u not in dag.free]
            for u in need:
                m.add_implication(put[v, k], x[u, k - 1])
                m.add(tk[v, k] <= x[u, k - 1] + put[u, k])
    m.minimize(sum(act[k] for k in range(1, K + 1)))
    return m, x, put, tk, act, verts, K


def run(n: int, p: int, k_max: int, seconds: float, label: str, **kw):
    m, x, put, tk, act, verts, K = build(n, p, k_max)
    if kw.pop("strategy_act", False):
        m.add_decision_strategy(
            [act[k] for k in range(1, K + 1)],
            cp_model.CHOOSE_FIRST,
            cp_model.SELECT_MAX_VALUE,
        )
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = seconds
    solver.parameters.num_workers = kw.pop("workers", 8)
    for key, value in kw.items():
        setattr(solver.parameters, key, value)
    t0 = time.perf_counter()
    st = solver.solve(m)
    dt = time.perf_counter() - t0
    name = solver.status_name(st)
    obj = int(solver.objective_value) if st in (cp_model.OPTIMAL, cp_model.FEASIBLE) else None
    print(
        f"{label:<28} {name:<9} A={obj} bound={solver.best_objective_bound:.0f} {dt:.1f}s",
        flush=True,
    )
    return name, obj


def main() -> None:
    seconds = 60.0
    if "--seconds" in sys.argv:
        seconds = float(sys.argv[sys.argv.index("--seconds") + 1])
    n, p, k = 24, 6, 96
    print(f"chain({n}) p={p} e=0, K={k}, 真値 A*=55 (M=109)")
    for label, kw in (
        ("default", {}),
        ("workers=16", {"workers": 16}),
        ("lin=2", {"linearization_level": 2}),
        ("symmetry=4", {"symmetry_level": 4}),
        ("strategy_act", {"strategy_act": True}),
        ("lin2+workers16", {"linearization_level": 2, "workers": 16}),
    ):
        run(n, p, k, seconds, label, **dict(kw))


if __name__ == "__main__":
    main()
