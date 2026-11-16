"""Gurobi ステージ定式化の診断: LP 緩和の強さとパラメータ感度。

`data/mip_stage_findings.md` の「なぜ境界域で MIP が CP-SAT に劣るか」の
一次データを取る。対象は chain(12) e=0（解ける側）と chain(16) p=5 e=0
（60 秒で解けない側）。

    .venv/bin/python scripts/mip_stage_diag.py [--seconds S]
"""

from __future__ import annotations

import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

os.environ.setdefault(
    "GRB_LICENSE_FILE", str(Path("~/.config/gurobi/gurobi.lic").expanduser())
)

import gurobipy as gp  # noqa: E402

from revpebble import chain, restrict_to_ancestors  # noqa: E402


def build(n: int, p: int, e: int, k_max: int, dominance: bool = True):
    """mip_stage の内部モデルを Gurobi ネイティブに再構築して返す。"""
    dag, target = restrict_to_ancestors(chain(n), n)
    verts = list(dag.pebbleable())
    K = k_max
    m = gp.Model("diag")
    m.Params.OutputFlag = 0
    x = m.addVars(
        [(v, k) for v in verts for k in range(K + 1)], vtype=gp.GRB.BINARY, name="x"
    )
    put = m.addVars(
        [(v, k) for v in verts for k in range(1, K + 1)], vtype=gp.GRB.BINARY, name="p"
    )
    tk = m.addVars(
        [(v, k) for v in verts for k in range(1, K + 1)], vtype=gp.GRB.BINARY, name="t"
    )
    act = m.addVars(range(1, K + 1), vtype=gp.GRB.BINARY, name="a")
    for v in verts:
        m.addConstr(x[v, 0] == 0)
        m.addConstr(x[v, K] == (1 if v == target else 0))
        m.addConstr(gp.quicksum(put[v, k] for k in range(1, K + 1)) >= 1)
    for k in range(1, K + 1):
        m.addConstr(gp.quicksum(put[v, k] for v in verts) == act[k])
        if k < K:
            m.addConstr(act[k + 1] <= act[k])
        m.addConstr(
            gp.quicksum(x[v, k - 1] for v in verts) + (p - 2) * (1 - act[k]) <= p - 1
        )
        for v in verts:
            m.addConstr(x[v, k] == x[v, k - 1] + put[v, k] - tk[v, k])
            m.addConstr(put[v, k] + x[v, k - 1] <= 1)
            m.addConstr(tk[v, k] <= x[v, k - 1] + put[v, k])
            m.addConstr(tk[v, k] <= act[k])
            if dominance and k < K:
                m.addConstr(tk[v, k] + put[v, k + 1] <= 1)
            need = [u for u in dag.preds[v] if u not in dag.free]
            for u in need:
                m.addConstr(put[v, k] <= x[u, k - 1])
            if need and e == 0:
                for u in need:
                    m.addConstr(tk[v, k] <= x[u, k - 1] + put[u, k])
    m.setObjective(gp.quicksum(act[k] for k in range(1, K + 1)), gp.GRB.MINIMIZE)
    return m


def lp_bound(n: int, p: int, e: int, k_max: int) -> float:
    m = build(n, p, e, k_max)
    r = m.relax()
    r.Params.OutputFlag = 0
    r.optimize()
    return r.ObjVal


def run(n: int, p: int, e: int, seconds: float, **params) -> tuple:
    dag, target = restrict_to_ancestors(chain(n), n)
    k_max = 4 * len(dag.pebbleable())
    m = build(n, p, e, k_max, dominance=params.pop("dominance", True))
    m.Params.TimeLimit = seconds
    m.Params.Threads = 8
    for key, value in params.items():
        setattr(m.Params, key, value)
    t0 = time.perf_counter()
    m.optimize()
    dt = time.perf_counter() - t0
    status = {gp.GRB.OPTIMAL: "OPTIMAL", gp.GRB.TIME_LIMIT: "TIME_LIMIT"}.get(
        m.Status, str(m.Status)
    )
    inc = m.ObjVal if m.SolCount else None
    return status, inc, m.ObjBound, round(dt, 2)


def main() -> None:
    seconds = 60.0
    if "--seconds" in sys.argv:
        seconds = float(sys.argv[sys.argv.index("--seconds") + 1])
    for n, p in ((12, 5), (16, 5)):
        k_max = 4 * n
        print(f"== chain({n}) p={p} e=0, K_max={k_max}, 真値 A*: 12→20 / 16→36")
        print(f"LP 緩和(=root前): {lp_bound(n, p, 0, k_max):.2f}")
        for label, params in (
            ("default", {}),
            ("no-dominance", {"dominance": False}),
            ("MIPFocus=3", {"MIPFocus": 3}),
            ("MIPFocus=2", {"MIPFocus": 2}),
            ("Cuts=3", {"Cuts": 3}),
            ("Symmetry=2", {"Symmetry": 2}),
            ("Focus3+Cuts3", {"MIPFocus": 3, "Cuts": 3}),
        ):
            status, inc, bound, dt = run(n, p, 0, seconds, **dict(params))
            print(
                f"{label:<14} status={status:<10} incumbent={inc} "
                f"bound={bound:.1f} {dt}s",
                flush=True,
            )


if __name__ == "__main__":
    main()
