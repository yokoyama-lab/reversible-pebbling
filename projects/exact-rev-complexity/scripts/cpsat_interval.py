"""CP-SAT の **retention interval** 型定式化（MOCCASIN 型）。

`data/cpsat_findings.md` の結論に従い、時間展開（$O(n\\cdot T)$ 変数）を捨てて
**各頂点の「保持区間」を整数変数で持つ** $O(n)$ 変数の定式化にする。

## 定式化の核となる観察

clean 可逆ペブリングでは、**各保持区間はちょうど 1 回の `put` で始まり 1 回の `take` で終わる。**
例外は目標頂点の最後の区間だけ（終端で載っているので `take` されない）。したがって

$$\\boxed{\\;M^*(G,p,e) \\;=\\; 2A^* - 1\\;}$$

ここで $A^*$ = **最小の保持区間数**（= ペブルを置く回数の総和）。
**手数の最小化は「再計算回数の最小化」と同一問題**である。

これは既存の全ての厳密値が**奇数**であることと整合する
（$1,3,5,9,11,\\dots,71$ / $155$ / $429$ / $99$ / $2n-1$）。**実装の健全性チェックに使える。**

## モデル

各頂点 $v$ に高々 $C$ 個の区間 $i$: 有効フラグ $a_{v,i}$、開始 $s_{v,i}$、終了 $t_{v,i}$
（整数、$0\\le s < t \\le H$）。

- **ピーク**: 全区間を「需要 1・容量 $p$」の累積資源に載せる → `add_cumulative`。
  スケジューリング専用の伝播器が効くので、素朴な各時刻の総和より格段に強い。
- **可用性**: `put`（時刻 $s_{v,i}$）は各先行点 $u$ について
  「ある区間 $j$ が $s_{u,j} < s_{v,i} < t_{u,j}$」を要求。
- **`take`**（時刻 $t_{v,i}$）は同条件を満たせば可逆、さもなくば不可逆消去として $e$ を消費。
- **目標**: ちょうど 1 個の区間が $t = H$ で終わる。他の全区間は $t < H$。
- **順序の正規化**: $a_{v,i} \\ge a_{v,i+1}$ かつ $t_{v,i} \\le s_{v,i+1}$（同一頂点の区間は交わらない）。

## 完全性の注意（**重要**）

$C$（1 頂点あたりの区間数の上限）が小さすぎると**最適解を落とす**。
`solve_intervals_auto` は $C$ を増やして値が改善しなくなるまで繰り返す。
**単発の `solve_intervals` の結果を最適値として報告してはいけない。**
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
    raise SystemExit("ortools が必要（.venv を使う。docs/33_install_notes.md）") from exc


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
) -> IntervalResult:
    """retention interval 型で $A^*$（したがって $M^*=2A^*-1$）を求める。"""
    verts = list(dag.pebbleable())
    if target in dag.free:
        return IntervalResult(0, 0, "OPTIMAL", cap, False)
    N = len(verts)
    H = horizon if horizon is not None else 2 * N * cap + 2

    m = cp_model.CpModel()
    a: dict[tuple[int, int], object] = {}
    s: dict[tuple[int, int], object] = {}
    t: dict[tuple[int, int], object] = {}
    iv = []  # cumulative 用の optional interval
    for v in verts:
        for i in range(cap):
            a[v, i] = m.new_bool_var(f"a{v}_{i}")
            s[v, i] = m.new_int_var(0, H, f"s{v}_{i}")
            t[v, i] = m.new_int_var(0, H, f"t{v}_{i}")
            # 有効なら長さ >= 1、無効なら s=t=0 に固定（対称性除去）
            m.add(t[v, i] >= s[v, i] + 1).only_enforce_if(a[v, i])
            m.add(s[v, i] == 0).only_enforce_if(a[v, i].Not())
            m.add(t[v, i] == 0).only_enforce_if(a[v, i].Not())
            dur = m.new_int_var(0, H, f"d{v}_{i}")
            m.add(dur == t[v, i] - s[v, i])
            iv.append(
                m.new_optional_interval_var(
                    s[v, i], dur, t[v, i], a[v, i], f"iv{v}_{i}"
                )
            )
        for i in range(cap - 1):
            # 正規化: 有効フラグは前詰め、区間は交わらず昇順
            m.add_implication(a[v, i].Not(), a[v, i + 1].Not())
            m.add(s[v, i + 1] >= t[v, i]).only_enforce_if(a[v, i + 1])

    # ピーク制約: 需要 1・容量 p の累積資源
    m.add_cumulative(iv, [1] * len(iv), p)

    # 目標: 最後の区間が H で終わる。他は H より前に終わる
    # eh[v,i] が真の区間は「終端まで載っている」ので **take されない**
    eh: dict[tuple[int, int], object] = {}
    last_at_H = []
    for v in verts:
        for i in range(cap):
            ends_at_H = m.new_bool_var(f"eH{v}_{i}")
            eh[v, i] = ends_at_H
            m.add(t[v, i] == H).only_enforce_if(ends_at_H)
            m.add(t[v, i] <= H - 1).only_enforce_if(ends_at_H.Not())
            m.add_implication(ends_at_H, a[v, i])
            if v != target:
                m.add(ends_at_H == 0)
            else:
                last_at_H.append(ends_at_H)
    m.add(sum(last_at_H) == 1)
    # 目標は少なくとも 1 区間
    m.add(a[target, 0] == 1)

    # 可用性: put/take の時刻が先行点の区間に真に含まれるか
    irr_flags = []
    for v in verts:
        need_preds = [u for u in dag.preds[v] if u not in dag.free]
        for i in range(cap):
            for kind, time_var in (("put", s[v, i]), ("take", t[v, i])):
                covered_all = []
                for u in need_preds:
                    cov = m.new_bool_var(f"cov_{kind}_{v}_{i}_{u}")
                    lits = []
                    for j in range(cap):
                        c = m.new_bool_var(f"c_{kind}_{v}_{i}_{u}_{j}")
                        m.add(s[u, j] <= time_var - 1).only_enforce_if(c)
                        m.add(t[u, j] >= time_var + 1).only_enforce_if(c)
                        m.add_implication(c, a[u, j])
                        lits.append(c)
                    # cov <=> どれかの区間が覆う
                    m.add_bool_or(lits).only_enforce_if(cov)
                    for lit in lits:
                        m.add_implication(lit, cov)
                    covered_all.append(cov)
                if not covered_all:
                    continue
                if kind == "put":
                    # put は必ず可用（無条件で要求）
                    for cov in covered_all:
                        m.add_implication(a[v, i], cov)
                else:
                    # take: 可用でなければ不可逆消去。
                    # **eh（終端まで載っている区間）は take されないので対象外**
                    # ← これを外していたため e=0 が INFEASIBLE になっていた（2026-07-27 修正）
                    irr = m.new_bool_var(f"irr_{v}_{i}")
                    m.add_implication(irr, a[v, i])
                    m.add_implication(irr, eh[v, i].Not())
                    for cov in covered_all:
                        # a ∧ ¬eh ∧ ¬cov → irr
                        m.add_bool_or([a[v, i].Not(), eh[v, i], cov, irr])
                    irr_flags.append(irr)
    if irr_flags:
        m.add(sum(irr_flags) <= e)

    total = sum(a[v, i] for v in verts for i in range(cap))
    m.minimize(total)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = max_seconds
    solver.parameters.num_workers = workers
    st = solver.solve(m)
    name = solver.status_name(st)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return IntervalResult(None, None, name, cap, False)
    A = int(solver.objective_value)
    tight = any(
        all(solver.value(a[v, i]) for i in range(cap)) for v in verts
    )
    return IntervalResult(2 * A - 1, A, name, cap, tight)


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
) -> IntervalResult:
    """$C$ を増やして値が改善しなくなるまで解く（**通常はこちらを使う**）。"""
    best: IntervalResult | None = None
    cap = cap_start
    while cap <= cap_max:
        r = solve_intervals(
            dag, target, p, e, cap=cap, max_seconds=max_seconds, workers=workers
        )
        if r.moves is not None:
            if best is None or r.moves < best.moves:  # type: ignore[operator]
                best = r
            elif not r.cap_tight:
                return best  # 改善せず、かつ C に余裕がある → 収束
        if r.status == "UNKNOWN":
            return best if best is not None else r
        cap += 1
    return best if best is not None else r


if __name__ == "__main__":
    from landauer import landauer_bfs
    from revpebble import bfs, chain

    print(f"{'case':<18} {'interval':>9} {'BFS':>6} {'A':>4} {'C':>3} {'status':>9}  一致")
    for n in (4, 6, 8, 12):
        p = 1 + (n - 1).bit_length()
        for e in (0, 1):
            r = solve_intervals_auto(chain(n), n, p=p, e=e, max_seconds=60)
            b = landauer_bfs(chain(n), n, p, e) if e else bfs(chain(n), n, p)[0]
            ok = "○" if r.moves == b else "**×**"
            print(
                f"chain({n}) e={e:<7} {str(r.moves):>9} {str(b):>6} "
                f"{str(r.intervals):>4} {r.cap:>3} {r.status:>9}  {ok}"
            )
