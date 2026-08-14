"""ブロック標準形（put 添字ステージ）定式化の CP-SAT 版。

`scripts/mip_stage.py` と**同一の定式化**を CP-SAT で解く。目的は
「MIP が interval 定式化で負けたのはソルバのせいか定式化のせいか」を
分離すること（`data/mip_findings.md` §5 の未解決問題）。

{interval, stage} × {CP-SAT, Gurobi, SCIP} の 2×3 比較の 1 マスを埋める。
定式化はモジュール mip_stage の docstring を参照（ブロック標準形の補題を含む）。
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from mip_stage import StageResult, _blocks_from_schedule  # noqa: E402
from revpebble import Dag, restrict_to_ancestors  # noqa: E402

try:
    from ortools.sat.python import cp_model
except ImportError as exc:  # pragma: no cover
    raise SystemExit("ortools が必要（.venv を使う。docs/33_install_notes.md）") from exc


def solve_stage(
    dag: Dag,
    target: int,
    p: int,
    e: int = 0,
    *,
    k_max: int,
    max_seconds: float = 60.0,
    workers: int = 8,
    hint: bool = False,
    dominance: bool = True,
    restricted: bool = False,
) -> StageResult:
    """mip_stage.solve_stage と同じモデルを CP-SAT で 1 回解く。"""
    started = time.perf_counter()
    if not restricted:
        dag, target = restrict_to_ancestors(dag, target)
    if target in dag.free:
        return StageResult(0, 0, "OPTIMAL", k_max, 0.0, 0.0)
    if p < 1 or e < 0 or k_max < 1:
        return StageResult(None, None, "INFEASIBLE", k_max, None, 0.0)
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

    irr_terms = []
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
            if dominance and k < K:
                m.add(tk[v, k] + put[v, k + 1] <= 1)
            need = [u for u in dag.preds[v] if u not in dag.free]
            for u in need:
                m.add_implication(put[v, k], x[u, k - 1])
            if need:
                if e == 0:
                    for u in need:
                        m.add(tk[v, k] <= x[u, k - 1] + put[u, k])
                else:
                    iv = m.new_bool_var(f"irr{v}_{k}")
                    m.add_implication(iv, tk[v, k])
                    for u in need:
                        m.add(tk[v, k] - x[u, k - 1] - put[u, k] <= iv)
                    irr_terms.append(iv)
    if irr_terms:
        m.add(sum(irr_terms) <= e)

    m.minimize(sum(act[k] for k in range(1, K + 1)))

    if hint and len(verts) <= 20:
        if e == 0:
            from revpebble import schedule

            moves_hint = schedule(dag, target, p)
        else:
            from landauer import landauer_schedule

            moves_hint = landauer_schedule(dag, target, p, e)
        blocks = _blocks_from_schedule(moves_hint) if moves_hint else None
        if blocks is not None and len(blocks) <= K:
            state: set[int] = set()
            for k, (pv, takes, _erases) in enumerate(blocks, start=1):
                m.add_hint(act[k], 1)
                state.add(pv)
                for v in verts:
                    m.add_hint(put[v, k], int(v == pv))
                    m.add_hint(tk[v, k], int(v in takes))
                state -= set(takes)
                for v in verts:
                    m.add_hint(x[v, k], int(v in state))
            for k in range(len(blocks) + 1, K + 1):
                m.add_hint(act[k], 0)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = max_seconds
    solver.parameters.num_workers = workers
    st = solver.solve(m)
    seconds = time.perf_counter() - started
    if st == cp_model.INFEASIBLE:
        return StageResult(None, None, "INFEASIBLE", K, None, seconds)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return StageResult(None, None, "UNKNOWN", K, None, seconds)
    A = int(solver.objective_value)
    bound = float(solver.best_objective_bound)
    status = "OPTIMAL" if st == cp_model.OPTIMAL else "FEASIBLE"
    return StageResult(2 * A - 1, A, status, K, bound, seconds)


def solve_stage_auto(
    dag: Dag,
    target: int,
    p: int,
    e: int = 0,
    *,
    k_start: int | None = None,
    k_limit: int = 512,
    max_seconds: float = 60.0,
    workers: int = 8,
    hint: bool = False,
    dominance: bool = True,
) -> StageResult:
    """K_max を INFEASIBLE のたびに倍にして解く（mip_stage 版と同じ規約）。"""
    dag, target = restrict_to_ancestors(dag, target)
    if target in dag.free:
        return StageResult(0, 0, "OPTIMAL", 0, 0.0, 0.0)
    n = len(dag.pebbleable())
    K = k_start if k_start is not None else max(2, 2 * n)
    total = 0.0
    while True:
        r = solve_stage(
            dag, target, p, e, k_max=K, max_seconds=max_seconds,
            workers=workers, hint=hint, dominance=dominance, restricted=True,
        )
        total += r.seconds
        if r.status != "INFEASIBLE":
            return StageResult(r.moves, r.intervals, r.status, K, r.bound, total)
        if K >= k_limit:
            return StageResult(None, None, f"INFEASIBLE(K<={K})", K, r.bound, total)
        K = min(2 * K, k_limit)


if __name__ == "__main__":
    from landauer import landauer_bfs
    from revpebble import bfs, chain

    expected = {
        (4, 0): 9, (4, 1): 7, (6, 0): 15, (6, 1): 11,
        (8, 0): 25, (8, 1): 17, (12, 0): 39, (12, 1): 29,
    }
    failures = []
    print(
        f"{'case':<16} {'CP':>5} {'BFS':>5} {'A':>4} {'K':>4} "
        f"{'status':>9} {'秒':>8}  一致"
    )
    for n, p in ((4, 3), (6, 4), (8, 4), (12, 5)):
        for e in (0, 1):
            r = solve_stage_auto(chain(n), n, p=p, e=e, max_seconds=60.0)
            b = landauer_bfs(chain(n), n, p, e) if e else bfs(chain(n), n, p)[0]
            ok = r.moves == b == expected[n, e]
            if not ok:
                failures.append((n, e, r.moves, b))
            print(
                f"chain({n}) e={e:<5} {str(r.moves):>5} {str(b):>5} "
                f"{str(r.intervals):>4} {r.k_max:>4} {r.status:>9} "
                f"{r.seconds:>8.2f}  {'○' if ok else '**×**'}"
            )
    if failures:
        raise SystemExit(f"BFS 不一致: {failures}")
