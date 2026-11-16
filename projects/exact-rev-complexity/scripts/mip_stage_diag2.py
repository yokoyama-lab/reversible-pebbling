"""診断第2版: LP 緩和の正しい値・支配カット×K_max の消し込み・鎖専用カット。

第1版（mip_stage_diag.py）の LP=0.00 は gurobipy の遅延 update のバグ
（relax() の前に update() が要る）。ここで修正して取り直す。

鎖専用カット（e=0 のみ・証明つき補題）:
  非 target 頂点 v の put が 1 回なら、その唯一の保持区間 [s,t] の中で
  v+1..n の生涯（put/take 全部）が完結する必要がある（put も可逆 take も
  v のペブルを要求するから）。区間中 v が 1 ペブルを占有するので、
  部分鎖 v+1..n は p-1 個で clean に解けなければならない。すなわち
  n - v ≤ reach(p-1) = 2^{p-2}（reach は既知の定理）。対偶で
      n - v > 2^{p-2}  ⟹  puts(v) ≥ 2。
  これは chain・e=0 でのみ有効（一般 DAG には拡張していない）。

    .venv/bin/python scripts/mip_stage_diag2.py [--seconds S]
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

import cpsat_stage  # noqa: E402
from revpebble import chain, restrict_to_ancestors  # noqa: E402


def build(n: int, p: int, k_max: int, dominance: bool, chain_cuts: bool):
    """e=0 の鎖のステージモデル（mip_stage と同一 + 任意の鎖専用カット）。"""
    dag, target = restrict_to_ancestors(chain(n), n)
    verts = list(dag.pebbleable())
    K = k_max
    m = gp.Model("diag2")
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
        lo = 1
        if chain_cuts and v != target and (len(verts) - v) > 2 ** (p - 2):
            lo = 2
        m.addConstr(gp.quicksum(put[v, k] for k in range(1, K + 1)) >= lo)
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
                m.addConstr(tk[v, k] <= x[u, k - 1] + put[u, k])
    m.setObjective(gp.quicksum(act[k] for k in range(1, K + 1)), gp.GRB.MINIMIZE)
    m.update()
    return m


def main() -> None:
    seconds = 60.0
    if "--seconds" in sys.argv:
        seconds = float(sys.argv[sys.argv.index("--seconds") + 1])

    print("## LP 緩和の正しい値（update 済み relax）")
    for n, p, k in ((12, 5, 24), (12, 5, 48), (16, 5, 64)):
        for cuts in (False, True):
            m = build(n, p, k, dominance=True, chain_cuts=cuts)
            r = m.relax()
            r.Params.OutputFlag = 0
            r.optimize()
            print(
                f"chain({n}) p={p} K={k} chain_cuts={cuts}: LP={r.ObjVal:.2f}",
                flush=True,
            )

    print("## Gurobi: 支配カット × K_max × 鎖カット（e=0）")
    grid = [
        (12, 5, 24, True, False), (12, 5, 24, False, False),
        (12, 5, 48, True, False), (12, 5, 48, False, False),
        (16, 5, 40, True, False), (16, 5, 40, False, False),
        (16, 5, 64, True, False), (16, 5, 64, False, False),
        (16, 5, 40, False, True), (16, 5, 64, False, True),
        (16, 5, 64, True, True),
    ]
    for n, p, k, dom, cuts in grid:
        m = build(n, p, k, dominance=dom, chain_cuts=cuts)
        m.Params.TimeLimit = seconds
        m.Params.Threads = 8
        t0 = time.perf_counter()
        m.optimize()
        dt = time.perf_counter() - t0
        status = {gp.GRB.OPTIMAL: "OPTIMAL", gp.GRB.TIME_LIMIT: "TIME_LIMIT"}.get(
            m.Status, str(m.Status)
        )
        inc = m.ObjVal if m.SolCount else None
        print(
            f"chain({n}) K={k} dom={int(dom)} cuts={int(cuts)}: "
            f"{status} incumbent={inc} bound={m.ObjBound:.1f} {dt:.2f}s",
            flush=True,
        )

    print("## CP-SAT: 支配カットの有無（e=0）")
    for n, p, k in ((12, 5, 24), (16, 5, 64), (20, 6, 80)):
        for dom in (True, False):
            r = cpsat_stage.solve_stage(
                chain(n), n, p, 0, k_max=k, max_seconds=seconds, dominance=dom
            )
            print(
                f"chain({n}) K={k} dom={int(dom)}: {r.status} "
                f"A={r.intervals} bound={r.bound} {r.seconds:.2f}s",
                flush=True,
            )


if __name__ == "__main__":
    main()
