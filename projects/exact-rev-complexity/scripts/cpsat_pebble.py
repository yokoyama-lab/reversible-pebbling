"""CP-SAT による $M^*(G,p,e)$ の計算（BFS が届かない大きな DAG 用）。

## 位置づけ

`docs/30_cross_field.md` §1.5 の方針「ML 側の MILP/CP 技術を我々が輸入する」の実装。

- BFS（`revpebble.bfs` / `landauer.landauer_bfs`）は**全スケジュールにわたる真の最適**を
  出すが、状態数が $\\sum_{k\\le p}\\binom{n}{k}$ で、頂点数に対して指数的。
- CP-SAT は**時間展開**した有限モデル上で最適解を探し、**最適性を証明して停止**する
  （`status == OPTIMAL`）。頂点数が数十でも動く可能性がある。

**重要**: CP-SAT の答えが正しいのは「定式化が真の最適解を落としていない」場合に限る。
したがって **BFS が届く範囲で全点一致を確認してから**、外挿範囲を信用する
（`tests/test_cpsat_pebble.py`）。一致しなければ定式化の誤りであり、
その発見自体が意味を持つ（`docs/30_cross_field.md` §1.6）。

## 定式化

時刻 $t=0..T$、各非源点 $v$ に対しブール変数 $x_{t,v}$（時刻 $t$ に $v$ がペブル済み）。

- 初期: 全て 0。終端: 目標のみ 1。
- 各ステップで**高々1個**の $x$ が変化する（0 変化 = idle）。手数 = idle でないステップ数。
- `put`$(v)$ は時刻 $t$ で $v$ の全先行点がペブル済み（または free）であることを要求。
- `take`$(v)$ は同条件を満たせば無償。満たさないなら**不可逆消去**として予算 $e$ を 1 消費。
- 各時刻の同時ペブル数 $\\le p$。

$T$（地平線）は上界を与える必要がある。既定は `2*(頂点数)+p+2*e+4`（十分に緩い）か、
呼び出し側から `horizon` で渡す。**$T$ が小さすぎると「実行不可能」を最適値と誤認する**ので、
`solve` は `horizon_tight` を返し、最適値が $T$ に張り付いていないかを呼び出し側で検査できる。
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag  # noqa: E402

try:
    from ortools.sat.python import cp_model
except ImportError as exc:  # pragma: no cover
    raise SystemExit(
        "ortools が必要です。リポジトリの .venv を使ってください:\n"
        "  .venv/bin/python scripts/cpsat_pebble.py\n"
        "（導入手順は docs/33_install_notes.md）"
    ) from exc


@dataclass(frozen=True)
class CpsatResult:
    """CP-SAT の結果。`moves` は最適手数（到達不能なら None）。"""

    moves: int | None
    status: str
    horizon: int
    horizon_tight: bool
    """最適値が地平線に張り付いている＝地平線不足の疑いがあるか。"""
    schedule: list[tuple[str, int]] | None = None


def default_horizon(dag: Dag, p: int, e: int) -> int:
    """最初に試す地平線。**上界の保証は無い**（`solve_auto` が倍々に伸ばす）。

    $e=0$ の可逆ペブリングでは $M^*$ が超線形になりうる（鎖 $n=16$ で 71 手）ので、
    $2n$ 程度では足りない。実測: `chain(8)`（$p=4$, $e=0$, $M^*=25$）は
    $T=24$ で **INFEASIBLE** になった。**地平線不足は誤った最適値ではなく
    実行不可能として現れる**（安全側）が、放置すると「到達不能」と誤読するので
    必ず `solve_auto` を使うこと。
    """
    n = len(dag.pebbleable())
    return 2 * n + p + 2 * e + 4


def solve(
    dag: Dag,
    target: int,
    p: int,
    e: int = 0,
    *,
    horizon: int | None = None,
    max_seconds: float = 60.0,
    workers: int = 8,
    want_schedule: bool = True,
) -> CpsatResult:
    """$M^*(G, p, e)$ を CP-SAT で解く。"""
    verts = list(dag.pebbleable())
    if target in dag.free:
        return CpsatResult(0, "OPTIMAL", 0, False, [])
    T = horizon if horizon is not None else default_horizon(dag, p, e)

    m = cp_model.CpModel()
    # x[t][v]
    x = {(t, v): m.new_bool_var(f"x_{t}_{v}") for t in range(T + 1) for v in verts}
    # move[t] : ステップ t→t+1 が実手か
    move = [m.new_bool_var(f"mv_{t}") for t in range(T)]
    # put[t][v] / take[t][v]
    put = {(t, v): m.new_bool_var(f"p_{t}_{v}") for t in range(T) for v in verts}
    take = {(t, v): m.new_bool_var(f"k_{t}_{v}") for t in range(T) for v in verts}
    # irr[t][v] : この take が不可逆消去か
    irr = {(t, v): m.new_bool_var(f"i_{t}_{v}") for t in range(T) for v in verts}

    # 初期状態: 空
    for v in verts:
        m.add(x[0, v] == 0)
    # 終端状態: 目標のみ
    for v in verts:
        m.add(x[T, v] == (1 if v == target else 0))

    for t in range(T):
        # 高々1個が変化。move[t] はその有無
        m.add(sum(put[t, v] + take[t, v] for v in verts) == move[t])
        # idle なら状態不変、実手ならその1個だけ変化
        for v in verts:
            # x[t+1,v] = x[t,v] + put - take
            m.add(x[t + 1, v] == x[t, v] + put[t, v] - take[t, v])
            # put は 0→1、take は 1→0
            m.add_implication(put[t, v], x[t, v].Not())
            m.add_implication(take[t, v], x[t, v])

        # 手が起きたら以降も止まらない（idle は末尾に固める）= 対称性除去
        if t + 1 < T:
            m.add_implication(move[t].Not(), move[t + 1].Not())

        # 可用性: preds が全てペブル済み（free は常に可用）
        for v in verts:
            need = [x[t, u] for u in dag.preds[v] if u not in dag.free]
            if need:
                avail = m.new_bool_var(f"a_{t}_{v}")
                # avail <=> AND(need)
                m.add_bool_and(need).only_enforce_if(avail)
                m.add_bool_or([nv.Not() for nv in need]).only_enforce_if(avail.Not())
                # put は avail を要求
                m.add_implication(put[t, v], avail)
                # take: avail なら可逆、さもなくば irr（take ⇒ irr ∨ avail）
                m.add_bool_or([irr[t, v], avail]).only_enforce_if(take[t, v])
                m.add_implication(irr[t, v], take[t, v])
                m.add_implication(irr[t, v], avail.Not())
            else:
                # preds が空 or 全て free → 常に可用。irr は起きない
                m.add(irr[t, v] == 0)

        # ピーク制約
        m.add(sum(x[t, v] for v in verts) <= p)
    m.add(sum(x[T, v] for v in verts) <= p)

    # 消去予算
    m.add(sum(irr[t, v] for t in range(T) for v in verts) <= e)

    m.minimize(sum(move))

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = max_seconds
    solver.parameters.num_workers = workers
    st = solver.solve(m)
    name = solver.status_name(st)

    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return CpsatResult(None, name, T, False, None)

    moves = int(solver.objective_value)
    sched: list[tuple[str, int]] | None = None
    if want_schedule:
        sched = []
        for t in range(T):
            for v in verts:
                if solver.value(put[t, v]):
                    sched.append(("put", v))
                elif solver.value(take[t, v]):
                    sched.append(("take", v))
    return CpsatResult(moves, name, T, moves >= T, sched)


def solve_auto(
    dag: Dag,
    target: int,
    p: int,
    e: int = 0,
    *,
    max_seconds: float = 60.0,
    workers: int = 8,
    max_doublings: int = 5,
    want_schedule: bool = False,
) -> CpsatResult:
    """地平線を自動で伸ばして解く（**通常はこちらを使う**）。

    INFEASIBLE の間は地平線を倍にして再試行する。真に到達不能な場合と
    地平線不足を区別できるのが利点（`max_doublings` 回伸ばしても INFEASIBLE なら
    到達不能と判断する）。UNKNOWN（時間切れ）はそのまま返す。
    """
    T = default_horizon(dag, p, e)
    last = None
    for _ in range(max_doublings + 1):
        r = solve(
            dag,
            target,
            p,
            e,
            horizon=T,
            max_seconds=max_seconds,
            workers=workers,
            want_schedule=want_schedule,
        )
        last = r
        if r.status == "INFEASIBLE":
            T *= 2
            continue
        if r.moves is not None and r.horizon_tight:
            # 最適値が地平線に張り付いた: 伸ばして再確認する
            T *= 2
            continue
        return r
    return last  # type: ignore[return-value]


def feasible_in(
    dag: Dag,
    target: int,
    p: int,
    e: int,
    moves: int,
    *,
    max_seconds: float = 60.0,
    workers: int = 8,
) -> str:
    """「ピーク $p$・消去 $\\le e$ で **ちょうど `moves` 手** で clean 到達できるか」の決定問題。

    最適化（`solve_auto`）より格段に軽い。idle ステップを持たないので変数が減り、
    目的関数が無いので探索が単純になる。
    **定理の検証（この手数で可能か／不可能か）にはこちらを使う。**

    戻り値: "FEASIBLE"（可能）/ "INFEASIBLE"（不可能＝証明された）/ "UNKNOWN"（時間切れ）。
    """
    verts = list(dag.pebbleable())
    T = moves
    m = cp_model.CpModel()
    x = {(t, v): m.new_bool_var(f"x{t}_{v}") for t in range(T + 1) for v in verts}
    put = {(t, v): m.new_bool_var(f"p{t}_{v}") for t in range(T) for v in verts}
    take = {(t, v): m.new_bool_var(f"k{t}_{v}") for t in range(T) for v in verts}
    irr = {(t, v): m.new_bool_var(f"i{t}_{v}") for t in range(T) for v in verts}

    for v in verts:
        m.add(x[0, v] == 0)
        m.add(x[T, v] == (1 if v == target else 0))

    for t in range(T):
        # 毎ステップちょうど1手（idle なし）
        m.add(sum(put[t, v] + take[t, v] for v in verts) == 1)
        for v in verts:
            m.add(x[t + 1, v] == x[t, v] + put[t, v] - take[t, v])
            m.add_implication(put[t, v], x[t, v].Not())
            m.add_implication(take[t, v], x[t, v])
            need = [x[t, u] for u in dag.preds[v] if u not in dag.free]
            if need:
                avail = m.new_bool_var(f"a{t}_{v}")
                m.add_bool_and(need).only_enforce_if(avail)
                m.add_bool_or([nv.Not() for nv in need]).only_enforce_if(avail.Not())
                m.add_implication(put[t, v], avail)
                m.add_bool_or([irr[t, v], avail]).only_enforce_if(take[t, v])
                m.add_implication(irr[t, v], take[t, v])
                m.add_implication(irr[t, v], avail.Not())
            else:
                m.add(irr[t, v] == 0)
        m.add(sum(x[t, v] for v in verts) <= p)
    m.add(sum(x[T, v] for v in verts) <= p)
    m.add(sum(irr[t, v] for t in range(T) for v in verts) <= e)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = max_seconds
    solver.parameters.num_workers = workers
    st = solver.solve(m)
    return {cp_model.OPTIMAL: "FEASIBLE", cp_model.FEASIBLE: "FEASIBLE"}.get(
        st, solver.status_name(st)
    )


if __name__ == "__main__":  # 手動確認（BFS との突き合わせ）
    from landauer import landauer_bfs
    from revpebble import chain

    print(f"{'case':<16} {'CP-SAT':>8} {'BFS':>8} {'status':>10} {'T':>5}  一致")
    for n in (4, 6, 8, 12):
        p = 1 + (n - 1).bit_length()
        for e in (0, 1, 2):
            r = solve_auto(chain(n), n, p=p, e=e, max_seconds=60)
            b = landauer_bfs(chain(n), n, p, e)
            ok = "○" if r.moves == b else "**×**"
            print(
                f"chain({n}) e={e:<5} {str(r.moves):>8} {str(b):>8} "
                f"{r.status:>10} {r.horizon:>5}  {ok}"
            )
