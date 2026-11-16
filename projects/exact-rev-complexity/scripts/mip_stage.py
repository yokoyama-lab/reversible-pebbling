"""ブロック標準形（put 添字ステージ）による可逆ペブリングの MIP 定式化。

`data/mip_findings.md` の結論（retention interval 定式化は CP-SAT に有利で、
MIP はイベント点方式 + indicator に展開するしかなく負けた）を受けて、
**MIP の LP 緩和が効く形に問題を書き直した**もの。

## ブロック標準形（この定式化を支える正規化補題）

clean 可逆ペブリングの任意のスケジュールは、初期状態が空である以上 put で
始まるので、**「put 1 回 + その後の take 集合」のブロック列**に一意に分割できる。
さらにブロック内の take は**トポロジカル降順**に並べ替えてよい:

- ブロック内では put 直後が状態の極大点で、以後は縮むだけ。降順に取れば、
  take される頂点より先に取り除かれるのは番号が大きい頂点だけなので、
  先行点（番号が小さい）は put 直後に揃っていれば take 時にも揃っている。
- したがって take の可逆/不可逆の判定は「put 直後の状態に先行点が揃うか」で
  閉じ、ブロック内の順序変数は不要。並べ替えで不可逆消去の回数は増えない。

ステージ数 = put 総数 A。保存則から take 総数 = A - 1 なので M = 2A - 1
（`cpsat_interval_findings.md` §1 の恒等式と同じ）。素朴な時間展開
（横幅 2A-1）に対しホライズンが半分になり、idle の対称性が消え、
**1 頂点あたりの区間数上限 C も不要**になる（完全性は K_max だけで決まる）。

## interval 版 MIP との違い（なぜ MIP で速くなると期待するか）

- indicator 制約ゼロ。全制約が {0,±1, p-2} 係数の純 0/1 線形 → LP 緩和が空でない。
- イベント点の O((nC)^2) 個の重なり二値が消え、ピークは各ステージの
  Σ_v x_{v,k} ≤ p-1 という単純なナップサック行になる。
- 「各祖先は少なくとも 1 回 put される」（e に依らず有効）を足すと LP 下界が
  即座に A ≥ n になる。

## 完全性（K_max の扱い）

feasibility は K について単調（トポロジカル最小の非 free 頂点の put-take 対を
先頭に足せば A → A+1）。したがって **K_max ≥ A* なら最適値はちょうど A* で、
K_max の余裕は答えに影響しない**。INFEASIBLE が証明されたら K_max を倍にして
再試行する（`solve_stage_auto`）。interval 版の cap 自動昇格と違い、
「cap_tight なら疑う」の類のヒューリスティックは要らない。
"""

from __future__ import annotations

import os
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag, restrict_to_ancestors  # noqa: E402

Backend = Literal["gurobi", "scip"]


@dataclass(frozen=True)
class StageResult:
    moves: int | None
    """$2A-1$。到達不能または未解決なら None。"""
    intervals: int | None
    """最小の put 回数 $A$（= 保持区間数）。"""
    status: str
    """OPTIMAL / FEASIBLE / INFEASIBLE / UNKNOWN。"""
    k_max: int
    """最後に使ったステージ数上限。"""
    bound: float | None
    """終了時点の $A$ の下界（OPTIMAL なら A に一致）。"""
    seconds: float
    """escalation を含む合計時間。"""


def _blocks_from_schedule(
    moves: list[tuple[str, int]],
) -> list[tuple[int, list[int], set[int]]] | None:
    """(put 頂点, take リスト, 不可逆 take 集合) のブロック列に分解する。

    不可逆かどうかは呼び出し側で put 直後の状態と突き合わせて判定し直すので、
    ここでは "erase" の印をそのまま保持するだけ。
    """
    blocks: list[tuple[int, list[int], set[int]]] = []
    for op, v in moves:
        if op == "put":
            blocks.append((v, [], set()))
        else:
            if not blocks:
                return None  # put より前の take は存在しないはず
            blocks[-1][1].append(v)
            if op == "erase":
                blocks[-1][2].add(v)
    return blocks


class _Mip:
    """Gurobi / SCIP 共通の最小 API（indicator は使わないので薄い）。"""

    def __init__(self, backend: Backend, max_seconds: float, workers: int) -> None:
        self.backend = backend
        if backend == "gurobi":
            os.environ.setdefault(
                "GRB_LICENSE_FILE",
                str(Path("~/.config/gurobi/gurobi.lic").expanduser()),
            )
            import gurobipy as gp

            self.gp = gp
            self.model = gp.Model("stage")
            self.model.Params.OutputFlag = 0
            self.model.Params.TimeLimit = max_seconds
            self.model.Params.Threads = workers
        elif backend == "scip":
            from pyscipopt import Model

            self.model = Model("stage")
            self.model.hideOutput()
            self.model.setParam("limits/time", max_seconds)
            self.model.setParam("parallel/maxnthreads", workers)
        else:
            raise ValueError(f"未知の backend: {backend!r} (gurobi/scip)")

    def binary(self, name: str):
        if self.backend == "gurobi":
            return self.model.addVar(vtype=self.gp.GRB.BINARY, name=name)
        return self.model.addVar(vtype="B", name=name)

    def add(self, cons, name: str = "") -> None:
        if self.backend == "gurobi":
            self.model.addConstr(cons, name=name)
        else:
            self.model.addCons(cons, name=name)

    def minimize(self, expr) -> None:
        if self.backend == "gurobi":
            self.model.setObjective(expr, self.gp.GRB.MINIMIZE)
        else:
            self.model.setObjective(expr, "minimize")

    def add_start(self, values: list[tuple[object, int]]) -> None:
        if self.backend == "gurobi":
            for var, value in values:
                var.Start = value
        else:
            sol = self.model.createSol()
            for var, value in values:
                self.model.setSolVal(sol, var, value)
            # 検証に失敗した hint は黙って捨てられる（値の固定ではない）
            self.model.addSol(sol)

    def optimize(self) -> tuple[str, bool]:
        self.model.optimize()
        if self.backend == "gurobi":
            g = self.gp.GRB
            status = self.model.Status
            if status == g.OPTIMAL:
                return "OPTIMAL", True
            if status == g.INFEASIBLE:
                return "INFEASIBLE", False
            if status == g.INF_OR_UNBD:
                # 目的は 0 で下に有界なので UNBOUNDED はあり得ない
                return "INFEASIBLE", False
            if self.model.SolCount:
                return "FEASIBLE", True
            return "UNKNOWN", False
        status = str(self.model.getStatus()).lower()
        if status == "optimal":
            return "OPTIMAL", True
        if status == "infeasible":
            return "INFEASIBLE", False
        if self.model.getNSols() > 0:
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

    def dual_bound(self) -> float | None:
        try:
            if self.backend == "gurobi":
                return float(self.model.ObjBound)
            return float(self.model.getDualbound())
        except Exception:
            return None


def solve_stage(
    dag: Dag,
    target: int,
    p: int,
    e: int = 0,
    *,
    k_max: int,
    max_seconds: float = 60.0,
    workers: int = 8,
    backend: Backend = "gurobi",
    hint: bool = False,
    dominance: bool = True,
    restricted: bool = False,
) -> StageResult:
    """ステージ数上限 k_max のブロック標準形モデルを 1 回解く。

    OPTIMAL の返り値は k_max ≥ A* である限り真の最適値
    （モジュール docstring の単調性）。INFEASIBLE は「put 回数 ≤ k_max の
    スケジュールが存在しない」ことの証明。
    """
    started = time.perf_counter()
    if not restricted:
        dag, target = restrict_to_ancestors(dag, target)
    if target in dag.free:
        return StageResult(0, 0, "OPTIMAL", k_max, 0.0, 0.0)
    if p < 1 or e < 0 or k_max < 1:
        return StageResult(None, None, "INFEASIBLE", k_max, None, 0.0)
    verts = list(dag.pebbleable())
    K = k_max

    mip = _Mip(backend, max_seconds, workers)
    x = {(v, k): mip.binary(f"x{v}_{k}") for v in verts for k in range(K + 1)}
    put = {(v, k): mip.binary(f"p{v}_{k}") for v in verts for k in range(1, K + 1)}
    tk = {(v, k): mip.binary(f"t{v}_{k}") for v in verts for k in range(1, K + 1)}
    act = {k: mip.binary(f"act{k}") for k in range(1, K + 1)}

    for v in verts:
        # 初期状態は空、終端状態は target のみ
        mip.add(x[v, 0] == 0)
        mip.add(x[v, K] == (1 if v == target else 0))
        # 各祖先は少なくとも 1 回 put される（e に依らず有効。LP 下界 ≥ n）
        mip.add(sum(put[v, k] for k in range(1, K + 1)) >= 1, f"anc_{v}")

    irr_terms = []
    for k in range(1, K + 1):
        # 各アクティブステージにちょうど 1 個の put
        mip.add(sum(put[v, k] for v in verts) == act[k], f"one_put_{k}")
        if k < K:
            mip.add(act[k + 1] <= act[k], f"mono_{k}")
        # ピーク: put 直後に |x_{k-1}| + 1 ≤ p。非アクティブ側は |x| = 1
        mip.add(
            sum(x[v, k - 1] for v in verts) + (p - 2) * (1 - act[k]) <= p - 1,
            f"peak_{k}",
        )
        for v in verts:
            # 遷移（流量保存）と put/take の意味論
            mip.add(x[v, k] == x[v, k - 1] + put[v, k] - tk[v, k], f"tr_{v}_{k}")
            mip.add(put[v, k] + x[v, k - 1] <= 1, f"putfree_{v}_{k}")
            mip.add(tk[v, k] <= x[v, k - 1] + put[v, k], f"tkpres_{v}_{k}")
            mip.add(tk[v, k] <= act[k], f"tkact_{v}_{k}")
            if dominance and k < K:
                # ブロック k で take した頂点をブロック k+1 の put にしない
                # （両者を消してブロックを併合すれば 2 手縮む: 支配される）
                mip.add(tk[v, k] + put[v, k + 1] <= 1, f"dom_{v}_{k}")
            # put の可用性は無条件、take は可逆でなければ e を消費
            need = [u for u in dag.preds[v] if u not in dag.free]
            for u in need:
                mip.add(put[v, k] <= x[u, k - 1], f"avail_{v}_{k}_{u}")
            if need:
                if e == 0:
                    for u in need:
                        mip.add(tk[v, k] <= x[u, k - 1] + put[u, k], f"rev_{v}_{k}_{u}")
                else:
                    iv = mip.binary(f"irr{v}_{k}")
                    mip.add(iv <= tk[v, k])
                    for u in need:
                        mip.add(
                            tk[v, k] - x[u, k - 1] - put[u, k] <= iv, f"rev_{v}_{k}_{u}"
                        )
                    irr_terms.append(iv)
    if irr_terms:
        mip.add(sum(irr_terms) <= e, "erasure_budget")

    mip.minimize(sum(act[k] for k in range(1, K + 1)))

    if hint:
        _add_hint(mip, dag, target, p, e, verts, K, x, put, tk, act)

    status, has_solution = mip.optimize()
    seconds = time.perf_counter() - started
    bound = mip.dual_bound()
    if not has_solution:
        return StageResult(None, None, status, K, bound, seconds)
    A = int(round(mip.objective_value()))
    moves = 2 * A - 1
    if moves % 2 != 1:  # pragma: no cover
        raise AssertionError(f"健全性違反: M={moves} が奇数でない")
    return StageResult(moves, A, status, K, bound, seconds)


def _add_hint(mip, dag, target, p, e, verts, K, x, put, tk, act) -> None:
    """BFS の最適スケジュールをブロック列に直して primal start として渡す。

    値の固定ではない（Gurobi は Start、SCIP は検証つき addSol、いずれも
    上界の種にすぎず、最適性の証明はソルバが行う）。状態数が大きく BFS が
    無理な規模では黙って何もしない。
    """
    if len(verts) > 20:
        return
    if e == 0:
        from revpebble import schedule

        moves_hint = schedule(dag, target, p)
    else:
        from landauer import landauer_schedule

        moves_hint = landauer_schedule(dag, target, p, e)
    if not moves_hint:
        return
    blocks = _blocks_from_schedule(moves_hint)
    if blocks is None or len(blocks) > K:
        return
    values: list[tuple[object, int]] = []
    state: set[int] = set()
    xs: dict[tuple[int, int], int] = {}
    for k, (pv, takes, _erases) in enumerate(blocks, start=1):
        values.append((act[k], 1))
        state.add(pv)
        for v in verts:
            values.append((put[v, k], int(v == pv)))
            values.append((tk[v, k], int(v in takes)))
        state -= set(takes)
        for v in verts:
            xs[v, k] = int(v in state)
    for k in range(len(blocks) + 1, K + 1):
        values.append((act[k], 0))
        for v in verts:
            values.append((put[v, k], 0))
            values.append((tk[v, k], 0))
            xs[v, k] = xs[v, len(blocks)]
    for v in verts:
        values.append((x[v, 0], 0))
        for k in range(1, K + 1):
            values.append((x[v, k], xs[v, k]))
    mip.add_start(values)


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
    backend: Backend = "gurobi",
    hint: bool = False,
    dominance: bool = True,
) -> StageResult:
    """K_max を INFEASIBLE のたびに倍にして解く（**通常はこちらを使う**）。

    max_seconds は 1 回の solve あたりの上限。返り値の seconds は合計。
    """
    dag, target = restrict_to_ancestors(dag, target)
    if target in dag.free:
        return StageResult(0, 0, "OPTIMAL", 0, 0.0, 0.0)
    n = len(dag.pebbleable())
    K = k_start if k_start is not None else max(2, 2 * n)
    total = 0.0
    while True:
        r = solve_stage(
            dag,
            target,
            p,
            e,
            k_max=K,
            max_seconds=max_seconds,
            workers=workers,
            backend=backend,
            hint=hint,
            dominance=dominance,
            restricted=True,
        )
        total += r.seconds
        if r.status != "INFEASIBLE":
            return StageResult(
                r.moves, r.intervals, r.status, K, r.bound, total
            )
        if K >= k_limit:
            return StageResult(
                None, None, f"INFEASIBLE(K<={K})", K, r.bound, total
            )
        K = min(2 * K, k_limit)


if __name__ == "__main__":
    from landauer import landauer_bfs
    from revpebble import bfs, chain

    hint = "--hint" in sys.argv
    backends = [b for b in ("gurobi", "scip") if f"--only-{b}" in sys.argv] or [
        "gurobi",
        "scip",
    ]
    expected = {
        (4, 0): 9, (4, 1): 7, (6, 0): 15, (6, 1): 11,
        (8, 0): 25, (8, 1): 17, (12, 0): 39, (12, 1): 29,
    }
    failures = []
    print(
        f"{'backend':<8} {'case':<16} {'MIP':>5} {'BFS':>5} {'A':>4} "
        f"{'K':>4} {'bound':>6} {'status':>9} {'秒':>8}  一致"
    )
    for backend in backends:
        for n, p in ((4, 3), (6, 4), (8, 4), (12, 5)):
            for e in (0, 1):
                r = solve_stage_auto(
                    chain(n), n, p=p, e=e, max_seconds=60.0,
                    backend=backend, hint=hint,
                )
                b = landauer_bfs(chain(n), n, p, e) if e else bfs(chain(n), n, p)[0]
                ok = r.moves == b == expected[n, e]
                if not ok:
                    failures.append((backend, n, e, r.moves, b))
                print(
                    f"{backend:<8} chain({n}) e={e:<5} {str(r.moves):>5} {str(b):>5} "
                    f"{str(r.intervals):>4} {r.k_max:>4} "
                    f"{'-' if r.bound is None else f'{r.bound:.1f}':>6} "
                    f"{r.status:>9} {r.seconds:>8.2f}  {'○' if ok else '**×**'}"
                )
    if failures:
        raise SystemExit(f"BFS 不一致: {failures}")
