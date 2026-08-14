#!/usr/bin/env python3
"""ピラミッドのピーク下界を**凍結された親**で強める（2026-08-15）。

`q2_pyr_lower.py`（拡大性つき）は $h \\le 12$ ではタイトだが、$h \\ge 13$ で
実測から離れる（$h=13$ で 35 対 37、$h=18$ で 50 対 58）。原因は抽象が
各層の**個数しか持たない**こと。ここでは変化数を **add / rem に分ける**ことで
1 つ制約を足す。

## 足した事実（新規・この抽象の要）

並列可逆ペブリングの規則
$v \\in P_i \\triangle P_{i+1} \\Rightarrow \\mathrm{parents}(v) \\subseteq P_i \\cap P_{i+1}$
より、層 $k$ の**変化した頂点の親は $t$ と $t+1$ の両方に居る**——つまり
**凍結されている**。よってその親たちは、同じ時刻に層 $k-1$ で
消える頂点（`rem`）とも現れる頂点（`add`）とも**互いに素**:

$$A_k = S_k(t) \\triangle S_k(t+1),\\quad N(A_k) \\subseteq S_{k-1}(t) \\cap S_{k-1}(t+1)$$

$\\mathrm{rem}_{k-1}(t) = S_{k-1}(t) \\setminus S_{k-1}(t+1)$ は
$S_{k-1}(t) \\cap S_{k-1}(t+1)$ と交わらないので、どちらも $S_{k-1}(t)$ に含まれることから

$$a_{k-1}(t) \\ge |N(A_k)| + \\mathrm{rem}_{k-1}(t) \\ge c_k(t) + 1 + \\mathrm{rem}_{k-1}(t)$$

同様に $a_{k-1}(t+1) \\ge c_k(t) + 1 + \\mathrm{add}_{k-1}(t)$。
**`q2_pyr_lower.py` の制約はこの右辺から `rem`/`add` を落としたもの**なので、
これは真に強い（等号は層 $k-1$ が同時刻に何も変えないとき）。

add/rem に分けたことで、個数の関係も不等式から**等式**になる:
$a_k(t{+}1) = a_k(t) + \\mathrm{add}_k(t) - \\mathrm{rem}_k(t)$。

## 健全性

どの制約も**合法なペブリングが必ず満たす**ので、この整数計画の最適値は
$p_{\\min}$ の下界。⚠ **打ち切りは下界にならない**（最適値でなければ意味がない）。
"""
from __future__ import annotations

import argparse
import sys

from ortools.sat.python import cp_model

# `q2_pyr_lower.py` と同一の実測値（回帰の突き合わせ用）
MEASURED = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16, 8: 20, 9: 23, 10: 26, 11: 29,
            12: 32, 13: 37, 14: 41, 15: 45, 16: 49, 17: 54, 18: 58}


def _add_interval(m, a, chg, n, D, T) -> None:
    """区間版の制約 — **位置を持たずに run の効果を部分的に取り込む**。

    層 $k$ の頂点 $j$ の親は層 $k-1$ の**隣接ペア** $\\{j, j{+}1\\}$ である。
    よって層 $k-1$ が集合 $S$ で**固定されている間**に触れる層 $k$ の頂点は、
    $S$ 内の隣接ペアの個数 $= |S| - \\mathrm{runs}(S) \\le |S| - 1$ 個以下。

    区間 $[t_1,t_2]$ で層 $k-1$ が不変なら、その間に変化しうる層 $k$ の頂点は
    高々 $a_{k-1}-1$ 個なので、

    $$|a_k(t_2) - a_k(t_1)| \\le \\max(0,\\ a_{k-1}(t_1) - 1)$$

    **全ての対 $(t_1,t_2)$ に端点だけ課せば十分**である: 最大と最小を与える
    時刻 $t_a, t_b$ が区間内にあるなら、部分区間 $[t_a,t_b]$ も不変なので
    そちらの端点制約が効くため。$O(T^2)$ 本で済む。

    ⚠ 健全性: どの合法なペブリングもこれを満たす（親が居なければ動かせない）。
    """
    # z[k][t] = 「層 k が t → t+1 で変化する」
    z = [[m.NewBoolVar(f"z{k}_{t}") for t in range(T)] for k in range(D + 1)]
    for k in range(D + 1):
        for t in range(T):
            m.Add(chg[k][t] >= 1).OnlyEnforceIf(z[k][t])
            m.Add(chg[k][t] == 0).OnlyEnforceIf(z[k][t].Not())

    for k in range(1, D + 1):
        # 触れる子の個数の上限 max(0, a_{k-1}(t) - 1)
        tch = []
        for t in range(T + 1):
            v = m.NewIntVar(0, n[k - 1], f"tch{k}_{t}")
            m.AddMaxEquality(v, [a[k - 1][t] - 1, 0])
            tch.append(v)
        for t1 in range(T):
            for t2 in range(t1 + 1, T + 1):
                # u = 「層 k-1 が [t1,t2] で不変」
                u = m.NewBoolVar(f"u{k}_{t1}_{t2}")
                zs = [z[k - 1][t] for t in range(t1, t2)]
                m.AddBoolAnd([x.Not() for x in zs]).OnlyEnforceIf(u)
                m.AddBoolOr([u] + zs)          # 実際に不変なら u を真に強制する
                m.Add(a[k][t2] - a[k][t1] <= tch[t1]).OnlyEnforceIf(u)
                m.Add(a[k][t1] - a[k][t2] <= tch[t1]).OnlyEnforceIf(u)


def bound(h: int, limit: float = 300.0, frozen: bool = True, workers: int = 8,
          interval: bool = False):
    """ピラミッド $P_h$ のピーク下界。

    `frozen=False` で旧抽象に戻す（比較用）。`interval=True` で区間版の制約を足す
    （下の `_add_interval` を参照）。
    """
    D = h - 1
    T = 2 * D + 1
    n = [h - k for k in range(h)]
    m = cp_model.CpModel()

    a = [[m.NewIntVar(0, n[k], f"a{k}_{t}") for t in range(T + 1)] for k in range(D + 1)]
    add = [[m.NewIntVar(0, n[k], f"p{k}_{t}") for t in range(T)] for k in range(D + 1)]
    rem = [[m.NewIntVar(0, n[k], f"m{k}_{t}") for t in range(T)] for k in range(D + 1)]
    chg = [[m.NewIntVar(0, n[k], f"c{k}_{t}") for t in range(T)] for k in range(D + 1)]

    for k in range(D + 1):
        for t in range(T + 1):
            if k == D:                                   # sink
                m.Add(a[k][t] == (0 if t < D + 1 else 1))
            else:
                if t < k + 1 or t > 2 * D - k:           # 時間窓（層1: time_window_dep）
                    m.Add(a[k][t] == 0)
                if t in (k + 1, k + 2, 2 * D - k - 1, 2 * D - k):
                    m.Add(a[k][t] == n[k])               # 両端強制（層1: present_at_dep 他）

        for t in range(T):
            # 変化を add / rem に分ける。個数の関係が等式になる（旧抽象は不等式）
            m.Add(a[k][t + 1] == a[k][t] + add[k][t] - rem[k][t])
            m.Add(chg[k][t] == add[k][t] + rem[k][t])
            # add ⊆ 補集合(S(t))、rem ⊆ S(t) なので上限が付く
            m.Add(add[k][t] <= n[k] - a[k][t])
            m.Add(rem[k][t] <= a[k][t])

    for k in range(1, D + 1):
        for t in range(T):
            act = m.NewBoolVar(f"act{k}_{t}")
            m.Add(chg[k][t] >= 1).OnlyEnforceIf(act)
            m.Add(chg[k][t] == 0).OnlyEnforceIf(act.Not())
            # 拡大性: |N(A)| >= |A| + 1（旧抽象と同じ）
            #   ＋ 凍結された親は層 k-1 の rem/add と互いに素（ここが新しい）
            extra_t = rem[k - 1][t] if frozen else 0
            extra_t1 = add[k - 1][t] if frozen else 0
            m.Add(a[k - 1][t] >= chg[k][t] + 1 + extra_t).OnlyEnforceIf(act)
            m.Add(a[k - 1][t + 1] >= chg[k][t] + 1 + extra_t1).OnlyEnforceIf(act)

    if interval:
        _add_interval(m, a, chg, n, D, T)

    p = m.NewIntVar(1, sum(n), "p")
    for t in range(T + 1):
        m.Add(sum(a[k][t] for k in range(D + 1)) <= p)
    m.Minimize(p)

    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = limit
    s.parameters.num_search_workers = workers
    st = s.Solve(m)
    if st == cp_model.OPTIMAL:
        return int(s.ObjectiveValue()), "最適"
    if st == cp_model.FEASIBLE:
        return None, f"打ち切り（下界にならない。到達した下界 {int(s.BestObjectiveBound())}）"
    return None, "実行不能"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--hmin", type=int, default=2)
    ap.add_argument("--hmax", type=int, default=18)
    ap.add_argument("--limit", type=float, default=300.0)
    ap.add_argument("--compare", action="store_true", help="旧抽象（凍結なし）も出す")
    ap.add_argument("--interval", action="store_true", help="区間版の制約を足す")
    ap.add_argument("--workers", type=int, default=8)
    args = ap.parse_args()

    print(f"  {'h':>3} {'旧(拡大性)':>10} {'新':>9} {'実測':>5} {'隙間':>5}  状態")
    unsound = 0
    improved = 0
    for h in range(args.hmin, args.hmax + 1):
        new, st = bound(h, args.limit, frozen=True, workers=args.workers,
                        interval=args.interval)
        old, _ = (bound(h, args.limit, frozen=False, workers=args.workers)
                  if args.compare else (None, ""))
        meas = MEASURED.get(h)
        gap = "" if (new is None or meas is None) else str(meas - new)
        # 健全性: 下界が実測を超えたら抽象が間違っている。
        # **実行不能も不健全**（合法なペブリングが存在するのに解が無い＝制約が強すぎる）。
        # 沈黙や「実行不能」を成功と読まないこと。
        if new is not None and meas is not None and new > meas:
            st += "  ⛔ 実測を超えた＝不健全"
            unsound += 1
        elif st == "実行不能":
            st += "  ⛔ 合法なペブリングが在るのに解が無い＝制約が強すぎる"
            unsound += 1
        if new is not None and old is not None and new > old:
            improved += 1
        print(f"  {h:>3} {str(old) if old is not None else '—':>10} "
              f"{str(new) if new is not None else '—':>9} {str(meas) if meas else '—':>5} "
              f"{gap:>5}  {st}")

    print()
    if unsound:
        print(f"  ⛔ 不健全な点が {unsound} 件。抽象が誤っている。")
        return 1
    print("  ✔ すべての点で下界 ≤ 実測（緩和として健全）")
    if args.compare:
        print(f"  ✔ 旧抽象より強くなった点: {improved} 件")
    return 0


if __name__ == "__main__":
    sys.exit(main())
