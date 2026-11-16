#!/usr/bin/env python3
"""定理 1（§9）を、完全二分木以外の out-tree で検定する。

定理 1: out-tree の全葉訪問（空盤→空盤、e=0）は $\\ge 2n$ 手で、
**$2n$ ちょうどが達成できるのは $p\\ge d+1$ のときに限る**（$d+1$ = 根から葉への最大頂点数）。

紙の証明が正しくても、**模型の実装が定理の言う模型とずれていたら意味が無い**ので、
無作為な out-tree で両方向を機械的に確かめる（陽性と陰性を対で見る）。

    python3 test_theorem1.py
"""

from __future__ import annotations

import random
import sys

from abandon import Dag, solve, Prices


def random_out_tree(n: int, rng: random.Random) -> Dag:
    """頂点 0 を根とする無作為な out-tree。葉すべてを訪問要求にする。"""
    preds: list[tuple[int, ...]] = [()]
    for v in range(1, n):
        preds.append((rng.randrange(v),))
    children: dict[int, int] = {}
    for v in range(1, n):
        children[preds[v][0]] = children.get(preds[v][0], 0) + 1
    leaves = tuple(v for v in range(n) if v not in children)
    return Dag(f"rand{n}", tuple(preds), leaves)


def depth_plus_one(g: Dag) -> int:
    """根から葉への最大頂点数。"""
    best = 1
    for v in range(g.n):
        d, u = 1, v
        while g.preds[u]:
            u = g.preds[u][0]
            d += 1
        best = max(best, d)
    return best


def main() -> int:
    rng = random.Random(20260825)
    prices = Prices(move=1, erase=None, hold=0)
    ok = bad = 0
    print("#  n  d+1   p=d+1 の最小手数 (2n)   p=d の最小手数   判定")
    for trial in range(12):
        n = rng.randint(4, 9)
        g = random_out_tree(n, rng)
        dp1 = depth_plus_one(g)
        at = solve(g, dp1, 0, prices)
        below = solve(g, dp1 - 1, 0, prices) if dp1 >= 2 else None

        # (1) p = d+1 では ちょうど 2n
        cond1 = at.cost == 2 * n
        # (2) p = d では 2n より真に大きい（実行不能も「2n では達成できない」に含む）
        cond2 = True if below is None else (below.cost is None or below.cost > 2 * n)
        verdict = "OK" if (cond1 and cond2) else "❌ 反例"
        if cond1 and cond2:
            ok += 1
        else:
            bad += 1
        b = "不可能" if (below is None or below.cost is None) else str(below.cost)
        print(f"  {n}  {dp1}      {at.cost} ({2 * n})            {b}          {verdict}")
        if verdict != "OK":
            print(f"    preds={g.preds} required={g.required}")

    # 陰性対照: 「$2n$ 未満が出る」ことは絶対に無いはず（定理 1a）
    control = 0
    for trial in range(12):
        n = rng.randint(4, 9)
        g = random_out_tree(n, rng)
        for p in range(2, n + 1):
            r = solve(g, p, 0, prices)
            if r.cost is not None and r.cost < 2 * n:
                control += 1
    print(f"\n定理 1a（>= 2n）に対する反例: {control} 件（0 でなければ模型か証明が誤り）")
    print(f"定理 1c の検定: OK {ok} / 反例 {bad}")
    return 0 if (bad == 0 and control == 0) else 1


if __name__ == "__main__":
    sys.exit(main())
