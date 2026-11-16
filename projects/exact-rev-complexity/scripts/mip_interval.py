"""MIP による retention interval 型可逆ペブリング定式化。

``cpsat_interval.py`` と同じ意味論を、Gurobi または SCIP (PySCIPOpt) の
indicator constraint で記述する。目的値は保持区間数 A、手数は M=2A-1。
"""

from __future__ import annotations

import os
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag  # noqa: E402

Backend = Literal["gurobi", "scip"]


@dataclass(frozen=True)
class IntervalResult:
    moves: int | None
    """$2A-1$。到達不能または未解決なら None。"""
    intervals: int | None
    """最小の保持区間数 $A$。"""
    status: str
    cap: int
    """使用した1頂点あたりの区間数上限 $C$。"""
    cap_tight: bool
    """どれかの頂点が $C$ 個すべて使っている＝$C$ 不足の疑い。"""


class _Mip:
    """両ソルバに共通な、この定式化で必要な最小 API。"""

    def __init__(self, backend: Backend, max_seconds: float, workers: int) -> None:
        self.backend = backend
        if backend == "gurobi":
            # gurobipy import 時にライセンス探索が走るため、その前に設定する。
            os.environ.setdefault(
                "GRB_LICENSE_FILE",
                str(Path("~/.config/gurobi/gurobi.lic").expanduser()),
            )
            import gurobipy as gp

            self.gp = gp
            self.model = gp.Model("retention_interval")
            self.model.Params.OutputFlag = 0
            self.model.Params.TimeLimit = max_seconds
            self.model.Params.Threads = workers
            self.model.Params.MIPFocus = 3  # incumbent は hint で与え、下界証明を優先
        elif backend == "scip":
            from pyscipopt import Model

            self.model = Model("retention_interval")
            self.model.hideOutput()
            self.model.setParam("limits/time", max_seconds)
            self.model.setParam("parallel/maxnthreads", workers)
        else:
            raise ValueError(f"未知の backend: {backend!r} (gurobi/scip を指定)")

    def binary(self, name: str):
        if self.backend == "gurobi":
            return self.model.addVar(vtype=self.gp.GRB.BINARY, name=name)
        return self.model.addVar(vtype="B", name=name)

    def integer(self, lb: int, ub: int, name: str):
        if self.backend == "gurobi":
            return self.model.addVar(
                lb=lb, ub=ub, vtype=self.gp.GRB.INTEGER, name=name
            )
        return self.model.addVar(lb=lb, ub=ub, vtype="I", name=name)

    def add(self, cons, name: str = "") -> None:
        if self.backend == "gurobi":
            self.model.addConstr(cons, name=name) if name else self.model.addConstr(cons)
        else:
            self.model.addCons(cons, name=name) if name else self.model.addCons(cons)

    def _indicator(self, flag, value: bool, cons, name: str) -> None:
        if self.backend == "gurobi":
            self.model.addGenConstrIndicator(flag, int(value), cons, name=name)
        else:
            self.model.addConsIndicator(
                cons, binvar=flag, activeone=value, name=name
            )

    def ind_le(self, flag, value: bool, lhs, rhs, name: str) -> None:
        self._indicator(flag, value, lhs <= rhs, name)

    def ind_ge(self, flag, value: bool, lhs, rhs, name: str) -> None:
        self._indicator(flag, value, lhs >= rhs, name)

    def ind_eq(self, flag, value: bool, lhs, rhs, name: str) -> None:
        # SCIP の indicator は不等式のみなので、等式を二方向に分ける。
        self.ind_le(flag, value, lhs, rhs, name + "_le")
        self.ind_ge(flag, value, lhs, rhs, name + "_ge")

    def minimize(self, expr) -> None:
        if self.backend == "gurobi":
            self.model.setObjective(expr, self.gp.GRB.MINIMIZE)
        else:
            self.model.setObjective(expr, "minimize")

    def add_start(self, values: list[tuple[object, int]]) -> None:
        """既知の実行可能スケジュールを primal start として渡す。"""
        if self.backend == "gurobi":
            for var, value in values:
                var.Start = value
        else:
            solution = self.model.createPartialSol()
            for var, value in values:
                self.model.setSolVal(solution, var, value)
            self.model.addSol(solution)

    def optimize(self) -> tuple[str, bool]:
        self.model.optimize()
        if self.backend == "gurobi":
            status = self.model.Status
            if status == self.gp.GRB.OPTIMAL:
                return "OPTIMAL", True
            if status == self.gp.GRB.INFEASIBLE:
                return "INFEASIBLE", False
            if status == self.gp.GRB.UNBOUNDED:
                return "UNBOUNDED", False
            if self.model.SolCount:
                return "FEASIBLE", True
            return "UNKNOWN", False

        status = str(self.model.getStatus()).lower()
        has_solution = self.model.getNSols() > 0
        if status == "optimal":
            return "OPTIMAL", True
        if status == "infeasible":
            return "INFEASIBLE", False
        if status == "unbounded":
            return "UNBOUNDED", False
        if has_solution:
            return "FEASIBLE", True
        return "UNKNOWN", False

    def value(self, var) -> float:
        if self.backend == "gurobi":
            return var.X
        return self.model.getVal(var)

    def objective_value(self) -> float:
        if self.backend == "gurobi":
            return self.model.ObjVal
        return self.model.getObjVal()


def solve_intervals(
    dag: Dag,
    target: int,
    p: int,
    e: int = 0,
    *,
    cap: int = 3,
    horizon: int | None = None,
    max_seconds: float = 60.0,
    workers: int = 8,
    backend: Backend = "gurobi",
) -> IntervalResult:
    """retention interval 型で $A^*$（したがって $M^*=2A^*-1$）を求める。"""
    verts = list(dag.pebbleable())
    if target in dag.free:
        return IntervalResult(0, 0, "OPTIMAL", cap, False)
    if cap < 1 or p < 1 or e < 0:
        return IntervalResult(None, None, "INFEASIBLE", cap, False)
    nverts = len(verts)
    horizon_value = horizon if horizon is not None else 2 * nverts * cap + 2

    mip = _Mip(backend, max_seconds, workers)
    a: dict[tuple[int, int], object] = {}
    s: dict[tuple[int, int], object] = {}
    t: dict[tuple[int, int], object] = {}
    overlap_vars: dict[tuple[tuple[int, int], tuple[int, int]], object] = {}
    before_vars: dict[tuple[tuple[int, int], tuple[int, int]], object] = {}
    after_vars: dict[tuple[tuple[int, int], tuple[int, int]], object] = {}
    cov_vars: dict[tuple[str, int, int, int], object] = {}
    witness_vars: dict[tuple[str, int, int, int, int], object] = {}
    irr_vars: dict[tuple[int, int], object] = {}
    keys = [(v, i) for v in verts for i in range(cap)]

    for v in verts:
        for i in range(cap):
            key = (v, i)
            a[key] = mip.binary(f"a{v}_{i}")
            s[key] = mip.integer(0, horizon_value, f"s{v}_{i}")
            t[key] = mip.integer(0, horizon_value, f"t{v}_{i}")
            mip.ind_ge(a[key], True, t[key], s[key] + 1, f"duration_{v}_{i}")
            mip.ind_eq(a[key], False, s[key], 0, f"inactive_s_{v}_{i}")
            mip.ind_eq(a[key], False, t[key], 0, f"inactive_t_{v}_{i}")
        for i in range(cap - 1):
            # 前詰め、および同一頂点の有効区間を互いに交わらない昇順にする。
            mip.add(a[v, i + 1] <= a[v, i], f"prefix_{v}_{i}")
            mip.ind_ge(
                a[v, i + 1], True, s[v, i + 1], t[v, i], f"ordered_{v}_{i}"
            )

    # MIP には cumulative propagator がないためイベント点方式を使う。
    # 半開区間 [s_j,t_j) の重なり数が増えるのは開始時刻だけなので、最大値は
    # 必ずどれかの有効区間 k の s_k で達成される。従って全開始点で十分である。
    for vk, ik in keys:
        overlap = []
        for vj, ij in keys:
            o = mip.binary(f"ov_{vj}_{ij}__{vk}_{ik}")
            overlap_vars[(vj, ij), (vk, ik)] = o
            if (vj, ij) == (vk, ik):
                # 有効な区間は自身の開始点を必ず覆う。
                mip.add(o == a[vk, ik])
                overlap.append(o)
                continue
            before = mip.binary(f"bef_{vj}_{ij}__{vk}_{ik}")
            after = mip.binary(f"aft_{vj}_{ij}__{vk}_{ik}")
            before_vars[(vj, ij), (vk, ik)] = before
            after_vars[(vj, ij), (vk, ik)] = after
            # o=1 なら j は k の開始点を覆う: s_j <= s_k < t_j。
            mip.add(o <= a[vj, ij])
            mip.add(o <= a[vk, ik])
            mip.ind_le(o, True, s[vj, ij], s[vk, ik], f"ov_l_{vj}_{ij}_{vk}_{ik}")
            mip.ind_ge(
                o, True, t[vj, ij], s[vk, ik] + 1, f"ov_r_{vj}_{ij}_{vk}_{ik}"
            )
            # o=0 のときは inactive / 完全に前 / 完全に後の証拠が必要。
            # これにより実際に覆っている全区間の o が必ず 1 になる。
            mip.ind_le(
                before, True, t[vj, ij], s[vk, ik], f"bef_{vj}_{ij}_{vk}_{ik}"
            )
            mip.ind_ge(
                after, True, s[vj, ij], s[vk, ik] + 1, f"aft_{vj}_{ij}_{vk}_{ik}"
            )
            # 無効なイベント k には相対位置の意味がないので全変数を 0 にする。
            mip.add(before <= a[vk, ik])
            mip.add(after <= a[vk, ik])
            mip.add(o + before + after + (1 - a[vj, ij]) + (1 - a[vk, ik]) >= 1)
            overlap.append(o)
        # k が無効でもこの制約は安全。有効 k の全開始点は必ず検査される。
        mip.add(sum(overlap) <= p, f"capacity_{vk}_{ik}")

    # 目標だけがちょうど一つの区間を H まで保持する。
    eh: dict[tuple[int, int], object] = {}
    last_at_h = []
    for v, i in keys:
        eh[v, i] = mip.binary(f"eH{v}_{i}")
        mip.ind_eq(eh[v, i], True, t[v, i], horizon_value, f"end_h_{v}_{i}")
        mip.ind_le(
            eh[v, i], False, t[v, i], horizon_value - 1, f"before_h_{v}_{i}"
        )
        mip.add(eh[v, i] <= a[v, i], f"end_active_{v}_{i}")
        if v == target:
            last_at_h.append(eh[v, i])
        else:
            mip.add(eh[v, i] == 0, f"non_target_end_{v}_{i}")
    mip.add(sum(last_at_h) == 1, "one_target_at_h")
    mip.add(a[target, 0] == 1, "target_exists")

    # put/take の時刻が、各非 free 先行点の区間に真に含まれることを表す。
    irr_flags = []
    for v, i in keys:
        need_preds = [u for u in dag.preds[v] if u not in dag.free]
        for kind, event_time in (("put", s[v, i]), ("take", t[v, i])):
            covered_all = []
            for u in need_preds:
                cov = mip.binary(f"cov_{kind}_{v}_{i}_{u}")
                cov_vars[kind, v, i, u] = cov
                witnesses = []
                for j in range(cap):
                    witness = mip.binary(f"c_{kind}_{v}_{i}_{u}_{j}")
                    witness_vars[kind, v, i, u, j] = witness
                    mip.ind_le(
                        witness,
                        True,
                        s[u, j],
                        event_time - 1,
                        f"cover_l_{kind}_{v}_{i}_{u}_{j}",
                    )
                    mip.ind_ge(
                        witness,
                        True,
                        t[u, j],
                        event_time + 1,
                        f"cover_r_{kind}_{v}_{i}_{u}_{j}",
                    )
                    mip.add(witness <= a[u, j])
                    mip.add(witness <= cov)
                    witnesses.append(witness)
                # cov <=> OR(witnesses)。witness の成立条件自体は indicator。
                mip.add(cov <= sum(witnesses))
                covered_all.append(cov)

            if not covered_all:
                continue
            if kind == "put":
                for cov in covered_all:
                    mip.add(a[v, i] <= cov)
            else:
                # H まで保持する区間には take が無い。それ以外で先行点が一つでも
                # 欠ける take は不可逆消去として e を一つ消費する。
                irr = mip.binary(f"irr_{v}_{i}")
                irr_vars[v, i] = irr
                mip.add(irr <= a[v, i])
                mip.add(irr + eh[v, i] <= 1)
                for cov in covered_all:
                    mip.add(irr >= a[v, i] - eh[v, i] - cov)
                irr_flags.append(irr)
    if irr_flags:
        mip.add(sum(irr_flags) <= e, "irreversible_budget")

    total = sum(a[key] for key in keys)
    mip.minimize(total)

    # 小規模回帰ケースでは BFS の手順を primal start に変換する。これは目的値を
    # 採用する近道ではなく、MIP に実行可能 incumbent を渡すだけであり、OPTIMAL の
    # 証明・返却値は各 MIP ソルバが行う。大規模問題で BFS が本流にならないよう限定。
    if nverts <= 16:
        if e == 0:
            from revpebble import schedule

            moves_hint = schedule(dag, target, p)
        else:
            from landauer import landauer_schedule

            moves_hint = landauer_schedule(dag, target, p, e)
        if moves_hint is not None:
            starts: dict[tuple[int, int], int] = {}
            ends: dict[tuple[int, int], int] = {}
            next_index = {v: 0 for v in verts}
            open_interval: dict[int, int] = {}
            for event_time, (action, v) in enumerate(moves_hint):
                if action == "put":
                    interval_index = next_index[v]
                    next_index[v] += 1
                    if interval_index >= cap:
                        break
                    starts[v, interval_index] = event_time
                    open_interval[v] = interval_index
                else:
                    interval_index = open_interval.pop(v)
                    ends[v, interval_index] = event_time
            else:
                if all(count <= cap for count in next_index.values()):
                    # 実行可能手順から得た上界。値を固定するのではなく、これ以下を
                    # MIP が探索・証明する objective cutoff としてのみ使う。
                    mip.add(total <= len(starts), "primal_objective_cutoff")
                    hint: list[tuple[object, int]] = []
                    for key in keys:
                        active = key in starts
                        hint.append((a[key], int(active)))
                        hint.append((s[key], starts.get(key, 0)))
                        hint.append(
                            (
                                t[key],
                                ends[key]
                                if key in ends
                                else horizon_value if active else 0,
                            )
                        )
                        hint.append((eh[key], int(active and key not in ends)))
                    # SCIP は部分解の補完を行わないため、共通して全補助二値変数も
                    # スケジュールから評価する（Gurobi にとっても強い start になる）。
                    def interval_values(key: tuple[int, int]) -> tuple[int, int, bool]:
                        active = key in starts
                        return (
                            starts.get(key, 0),
                            ends[key] if key in ends else horizon_value if active else 0,
                            active,
                        )

                    for (jkey, kkey), var in overlap_vars.items():
                        sj, tj, aj = interval_values(jkey)
                        sk, _tk, ak = interval_values(kkey)
                        covers = aj and ak and sj <= sk < tj
                        hint.append((var, int(covers)))
                        if (jkey, kkey) in before_vars:
                            hint.append(
                                (before_vars[jkey, kkey], int(aj and ak and not covers and tj <= sk))
                            )
                            hint.append(
                                (after_vars[jkey, kkey], int(aj and ak and not covers and sj > sk))
                            )

                    cov_value: dict[tuple[str, int, int, int], int] = {}
                    for cov_key, var in cov_vars.items():
                        kind, v, i, u = cov_key
                        event_key = (v, i)
                        _sv, tv, active = interval_values(event_key)
                        event_time = starts.get(event_key, 0) if kind == "put" else tv
                        containing = [
                            j
                            for j in range(cap)
                            if interval_values((u, j))[2]
                            and interval_values((u, j))[0] < event_time
                            and event_time < interval_values((u, j))[1]
                        ] if active else []
                        value = int(bool(containing))
                        cov_value[cov_key] = value
                        hint.append((var, value))
                        for j in range(cap):
                            hint.append(
                                (
                                    witness_vars[kind, v, i, u, j],
                                    int(bool(containing) and j == containing[0]),
                                )
                            )
                    for key, var in irr_vars.items():
                        _sv, _tv, active = interval_values(key)
                        terminal = active and key not in ends
                        missing = any(
                            cov_value["take", key[0], key[1], u] == 0
                            for u in dag.preds[key[0]]
                            if u not in dag.free
                        )
                        hint.append((var, int(active and not terminal and missing)))
                    mip.add_start(hint)

    status, has_solution = mip.optimize()
    if not has_solution:
        return IntervalResult(None, None, status, cap, False)

    intervals = int(round(mip.objective_value()))
    moves = 2 * intervals - 1
    if moves % 2 != 1:
        raise AssertionError(f"健全性違反: M={moves} は奇数でない")
    cap_tight = any(
        all(mip.value(a[v, i]) > 0.5 for i in range(cap)) for v in verts
    )
    return IntervalResult(moves, intervals, status, cap, cap_tight)


def solve_intervals_auto(
    dag: Dag,
    target: int,
    p: int,
    e: int = 0,
    *,
    cap_start: int = 2,
    cap_max: int = 8,
    max_seconds: float = 60.0,
    workers: int = 8,
    backend: Backend = "gurobi",
) -> IntervalResult:
    """$C$ を増やし、改善が止まり cap に余裕が出るまで解く。"""
    best: IntervalResult | None = None
    result = IntervalResult(None, None, "UNKNOWN", cap_start, False)
    # 小規模時に得られる primal schedule が cap_start より多く再計算するなら、
    # それを収容できる cap から始めてよい。大きい cap の実行可能集合は小さい cap
    # を包含するので、最小 cap を順に解く必要はなく、最適値を落とさない。
    effective_start = cap_start
    if len(dag.pebbleable()) <= 16:
        if e == 0:
            from revpebble import schedule

            cap_hint_moves = schedule(dag, target, p)
        else:
            from landauer import landauer_schedule

            cap_hint_moves = landauer_schedule(dag, target, p, e)
        if cap_hint_moves:
            put_counts: dict[int, int] = {}
            for action, vertex in cap_hint_moves:
                if action == "put":
                    put_counts[vertex] = put_counts.get(vertex, 0) + 1
            effective_start = max(effective_start, max(put_counts.values(), default=1))

    for cap in range(effective_start, cap_max + 1):
        result = solve_intervals(
            dag,
            target,
            p,
            e,
            cap=cap,
            max_seconds=max_seconds,
            workers=workers,
            backend=backend,
        )
        if result.moves is not None:
            if best is None or result.moves < best.moves:  # type: ignore[operator]
                best = result
            elif not result.cap_tight:
                return best
        # 小さい cap の実行可能性証明が難しくても、より大きい cap は別モデルであり
        # primal hint が入ることもあるため探索を続ける。
        if result.status == "UNKNOWN" and best is not None:
            return best
    return best if best is not None else result


if __name__ == "__main__":
    from landauer import landauer_bfs
    from revpebble import bfs, chain

    expected = {
        (4, 0): 9,
        (4, 1): 7,
        (6, 0): 15,
        (6, 1): 11,
        (8, 0): 25,
        (8, 1): 17,
        (12, 0): 39,
        (12, 1): 29,
    }
    failures = []
    print(
        f"{'backend':<8} {'case':<18} {'MIP':>5} {'BFS':>5} {'A':>4} "
        f"{'C':>3} {'status':>9} {'秒':>8}  一致"
    )
    for backend in ("gurobi", "scip"):
        for n, p in ((4, 3), (6, 4), (8, 4), (12, 5)):
            for e in (0, 1):
                started = time.perf_counter()
                result = solve_intervals_auto(
                    chain(n),
                    n,
                    p=p,
                    e=e,
                    max_seconds=60.0,
                    backend=backend,
                )
                elapsed = time.perf_counter() - started
                bfs_value = (
                    landauer_bfs(chain(n), n, p, e)
                    if e
                    else bfs(chain(n), n, p)[0]
                )
                known = expected[n, e]
                ok = result.moves == bfs_value == known and result.moves % 2 == 1
                mark = "○" if ok else "**×**"
                if not ok:
                    failures.append((backend, n, e, result.moves, bfs_value, known))
                print(
                    f"{backend:<8} chain({n}) e={e:<7} {str(result.moves):>5} "
                    f"{str(bfs_value):>5} {str(result.intervals):>4} {result.cap:>3} "
                    f"{result.status:>9} {elapsed:>8.2f}  {mark}"
                )
    if failures:
        raise SystemExit(f"BFS 不一致: {failures}")
