#!/usr/bin/env python3
"""放棄ペブリング（abandonment pebbling）の厳密最小コスト。

問い: 可逆計算で「放棄された計算」の情報を **保存（場所を占める）／逆走（手数を払う）／
再計算（後で手数を払う）** の間でどう配分できるか。

模型（`README.md` §1 が正本）:
  - DAG 上の可逆ペブルゲーム（置く・外すのどちらも親が全部ペブル済みであることを要求）
  - **消去**（erase）: 親を要求せずにペブルを外す。回数の上限 e、または 1 回 c_erase の値段
  - **要求**: 指定した「訪問必須」頂点それぞれを、いつかペブルすること（同時でなくてよい）
  - **終了**: 盤が空（clean）
  - 目的関数 = c_move·(手数) + c_erase·(消去回数) + c_hold·(空間×時間の積分)

三つの選択肢はこの目的関数の中で初めて比べられる:
  保存 = c_hold を払う／逆走 = c_move を払う／再計算 = 後で c_move を払う／
  消去 = c_erase を払う（＝物理的にはエントロピーを外に捨てる）。

層3（実測）。定理は主張しない。閉形式の予想は README の予想表に事前登録する。
"""

from __future__ import annotations

import argparse
import heapq
import sys
from dataclasses import dataclass


# --------------------------------------------------------------------------
# グラフの族
# --------------------------------------------------------------------------
@dataclass(frozen=True)
class Dag:
    """頂点 0..n-1、preds[v] は v の親（先に置かれていなければならない頂点）。"""

    name: str
    preds: tuple[tuple[int, ...], ...]
    required: tuple[int, ...]  # 訪問必須（いつかペブルすること）

    @property
    def n(self) -> int:
        return len(self.preds)


def chain(n: int) -> Dag:
    """鎖 0 -> 1 -> ... -> n-1。必須は末端のみ（＝通常の可逆ペブリング）。"""
    preds = tuple(() if v == 0 else (v - 1,) for v in range(n))
    return Dag(f"chain{n}", preds, (n - 1,))


def chain_visit_all(n: int) -> Dag:
    """鎖だが全頂点を訪問必須にする（自明: 前向きに一度ずつ通れば済む）。"""
    preds = tuple(() if v == 0 else (v - 1,) for v in range(n))
    return Dag(f"chainall{n}", preds, tuple(range(n)))


def tree(d: int) -> Dag:
    """深さ d の完全二分木。根 0 が source、葉が sink。**葉すべてが訪問必須**。

    「探索木を全部当たる」= 放棄が本質的に起きる最小の族。各葉を試したあと、
    その葉（と使い終わった枝）の情報は放棄される。
    """
    n = 2 ** (d + 1) - 1
    preds: list[tuple[int, ...]] = []
    for v in range(n):
        preds.append(() if v == 0 else ((v - 1) // 2,))
    leaves = tuple(range(2**d - 1, n))
    return Dag(f"tree{d}", tuple(preds), leaves)


def tree_root(d: int) -> Dag:
    """深さ d の完全二分木を **葉から根へ**（通常の可逆ペブリング）。校正用。"""
    n = 2 ** (d + 1) - 1
    preds: list[tuple[int, ...]] = []
    for v in range(n):
        kids = [2 * v + 1, 2 * v + 2]
        preds.append(tuple(k for k in kids if k < n))
    return Dag(f"treeroot{d}", tuple(preds), (0,))


def broom(spine: int, probe: int) -> Dag:
    """背骨 spine 本、各背骨頂点から長さ probe の枝（探査）が生える。

    枝の先端が「試して捨てる」計算。枝は互いに接頭辞を共有しないので、
    保存が得になる余地が無い（＝木との対比のための対照群）。
    """
    preds: list[tuple[int, ...]] = []
    spine_id = []
    for i in range(spine):
        spine_id.append(len(preds))
        preds.append(() if i == 0 else (spine_id[i - 1],))
    required = [spine_id[-1]]
    for i in range(spine):
        prev = spine_id[i]
        for _ in range(probe):
            preds.append((prev,))
            prev = len(preds) - 1
        required.append(prev)
    return Dag(f"broom{spine}x{probe}", tuple(preds), tuple(required))


FAMILIES = {
    "chain": lambda a: chain(a),
    "chainall": lambda a: chain_visit_all(a),
    "tree": lambda a: tree(a),
    "treeroot": lambda a: tree_root(a),
}


# --------------------------------------------------------------------------
# 厳密解（Dijkstra）
# --------------------------------------------------------------------------
@dataclass(frozen=True)
class Prices:
    move: int = 1
    erase: int | None = None  # None = 手数と同じ値段。0 = 無料（＝古典模型）
    hold: int = 0

    @property
    def erase_cost(self) -> int:
        return self.move if self.erase is None else self.erase

    def __str__(self) -> str:
        return f"move={self.move},erase={self.erase_cost},hold={self.hold}"


@dataclass
class Result:
    cost: int | None
    moves: int | None
    erases: int | None
    peak: int | None
    integral: int | None
    states: int
    path: list[str] | None = None


def solve(
    g: Dag,
    p: int | None,
    e: int | None,
    prices: Prices,
    *,
    want_path: bool = False,
    order_lr: bool = False,
    final: str = "clean",
) -> Result:
    """最小コストを厳密に求める。

    p: ペブル数上限（None で無制限）。e: 消去回数の上限（0 なら消去禁止、None で無制限）。
    order_lr: 必須頂点を required の順番でしか訪問できないと制限する（WLOG の検定用）。
    """
    req_index = {v: i for i, v in enumerate(g.required)}
    full = (1 << len(g.required)) - 1
    preds = g.preds

    # 状態 = (ペブル集合のビット, 訪問済みビット, 使った消去回数)
    start = (0, 0, 0)
    dist: dict[tuple[int, int, int], int] = {start: 0}
    prev: dict[tuple[int, int, int], tuple[tuple[int, int, int], str] | None] = {start: None}
    # (手数, 消去回数, ペブルの最大値, 空間×時間の積分)
    stat: dict[tuple[int, int, int], tuple[int, int, int, int]] = {start: (0, 0, 0, 0)}
    pq: list[tuple[int, tuple[int, int, int]]] = [(0, start)]
    seen = 0

    def popcount(x: int) -> int:
        return bin(x).count("1")

    while pq:
        cost, st = heapq.heappop(pq)
        if cost > dist.get(st, 1 << 60):
            continue
        seen += 1
        P, vis, used = st
        goal_P = 0 if final == "clean" else sum(1 << v for v in g.required)
        if P == goal_P and vis == full:
            mv, er, pk, ig = stat[st]
            path = None
            if want_path:
                path = []
                cur: tuple[int, int, int] | None = st
                while cur is not None and prev[cur] is not None:
                    par, lab = prev[cur]  # type: ignore[misc]
                    path.append(lab)
                    cur = par
                path.reverse()
            return Result(cost, mv, er, pk, ig, seen, path)

        live = popcount(P)
        hold = prices.hold * live
        for v in range(g.n):
            bit = 1 << v
            ready = all(P & (1 << u) for u in preds[v])
            cands: list[tuple[int, int, int, int, int, str]] = []
            # (新P, 消去増, コスト, 手数増, 消去回数増, ラベル)
            if not (P & bit):
                if ready and (p is None or popcount(P) + 1 <= p):
                    cands.append((P | bit, 0, prices.move, 1, 0, f"+{v}"))
            else:
                if ready:
                    cands.append((P & ~bit, 0, prices.move, 1, 0, f"-{v}"))
                if e is None or used < e:
                    cands.append((P & ~bit, 1, prices.erase_cost, 1, 1, f"!{v}"))
            for newP, dused, c, dmv, der, lab in cands:
                nvis = vis
                if v in req_index and not (P & bit):  # 置いた瞬間に訪問と数える
                    i = req_index[v]
                    if order_lr and vis != (1 << i) - 1:
                        pass  # 左から順にしか訪問できない制限
                    else:
                        nvis = vis | (1 << i)
                nst = (newP, nvis, used + dused)
                ncost = cost + c + hold
                if ncost < dist.get(nst, 1 << 60):
                    dist[nst] = ncost
                    mv, er, pk, ig = stat[st]
                    stat[nst] = (mv + dmv, er + der,
                                 max(pk, popcount(newP)), ig + live)
                    prev[nst] = (st, lab)
                    heapq.heappush(pq, (ncost, nst))
    return Result(None, None, None, None, None, seen)


# --------------------------------------------------------------------------
# 独立な上界（オイラー巡回）— 最適値との突き合わせ用の第2実装
# --------------------------------------------------------------------------
def euler_tour_cost(d: int, prices: Prices) -> int:
    """深さ d の完全二分木を DFS で辿り、各頂点を 1 回置いて 1 回外す戦略のコスト。

    p = d+1 で成立する。空間×時間の積分も同時に数える。**Dijkstra とは独立に数える。**
    """
    n = 2 ** (d + 1) - 1
    seq: list[tuple[str, int]] = []

    def walk(v: int) -> None:
        seq.append(("+", v))
        for k in (2 * v + 1, 2 * v + 2):
            if k < n:
                walk(k)
        seq.append(("-", v))

    walk(0)
    cost = 0
    live = 0
    for op, _v in seq:
        cost += prices.move + prices.hold * live
        live += 1 if op == "+" else -1
    assert live == 0
    return cost


# --------------------------------------------------------------------------
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("family", choices=sorted(FAMILIES))
    ap.add_argument("arg", type=int, help="tree なら深さ、chain なら長さ")
    ap.add_argument("--p", type=int, default=None, help="ペブル上限")
    ap.add_argument("--pmax", type=int, default=None, help="p を 2..pmax で掃く")
    ap.add_argument("--e", type=int, default=0, help="消去回数の上限（-1 で無制限）")
    ap.add_argument("--emax", type=int, default=None, help="e を 0..emax で掃く")
    ap.add_argument("--hold", type=int, default=0)
    ap.add_argument("--erase-price", default="move",
                    help="消去 1 回の値段。'move'（既定）か整数。0 = 無料＝古典模型")
    ap.add_argument("--final", choices=("clean", "keep"), default="clean",
                    help="clean=盤を空にする / keep=必須頂点だけ残す（reach と同じ約束）")
    ap.add_argument("--order-lr", action="store_true")
    ap.add_argument("--path", action="store_true")
    args = ap.parse_args()

    g = FAMILIES[args.family](args.arg)
    ep = None if args.erase_price == "move" else int(args.erase_price)
    prices = Prices(move=1, erase=ep, hold=args.hold)
    ps = range(2, args.pmax + 1) if args.pmax else [args.p]
    es = range(0, args.emax + 1) if args.emax is not None else [None if args.e < 0 else args.e]

    print(f"# {g.name}: n={g.n} 必須={len(g.required)} 個, 値段 {prices}")
    print(f"# {'p':>3} {'e':>4} {'cost':>7} {'moves':>7} {'erases':>7}"
          f" {'peak':>5} {'S*T':>6} {'states':>9}")
    for p in ps:
        for e in es:
            r = solve(g, p, e, prices, want_path=args.path,
                      order_lr=args.order_lr, final=args.final)
            es_lbl = "inf" if e is None else str(e)
            if r.cost is None:
                print(f"  {p!s:>3} {es_lbl:>4} {'-':>7} {'-':>7} {'-':>7}"
                      f" {'-':>5} {'-':>6} {r.states:>9}")
            else:
                print(
                    f"  {p!s:>3} {es_lbl:>4} {r.cost:>7} {r.moves:>7} {r.erases:>7}"
                    f" {r.peak:>5} {r.integral:>6} {r.states:>9}"
                )
                if r.path:
                    print("    " + " ".join(r.path))
    return 0


if __name__ == "__main__":
    sys.exit(main())
