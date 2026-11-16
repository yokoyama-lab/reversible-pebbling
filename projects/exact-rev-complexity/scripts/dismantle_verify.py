"""`data/conj_g_proof_attempt.md`（Opus5-medium）の敵対的検証（Fable5-max 側）。

**あちらのスクリプトは読まず**、本文 §2.3（解体形式）・§4（A♮）・§6（B♮ の
据え替えレシピ）の記述だけから独立に再実装し、突き合わせる。狙う穴:

1. あちらの全数検査は $p\\le5$（位置 ≤13/16）まで。**$k=p$ の端（$m_k=1/2$）を
   $p=6$（位置 ≤13 全数）と $p=7$・$k=7$（位置 ≤11 全数）で踏む**。
   ここは倍化恒等式 $W(2S;p{+}1)=W(S;p)$ が $|S|=p$ で破れる場所＝端の場合分けが
   効く唯一の場所（conj_u_status.md §3.1／あちらの §11.5）。
2. B♮ (III) の**据え替えレシピそのもの**を本文どおりに実装し、cost(D'') ≤ cost(D)+1 を
   レシピ単位で確認（結論だけでなく構成の検査）。
3. 解体形式 ≡ commit DP（umin_dp）の同値を独立実装で再確認。

    python3 scripts/dismantle_verify.py --equiv     # 同値の確認
    python3 scripts/dismantle_verify.py --p6        # p=6 全数（k=6 含む）
    python3 scripts/dismantle_verify.py --p7edge    # p=7, k=7 の端 全数
"""

from __future__ import annotations

import argparse
import sys
from itertools import combinations, permutations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

INF = float("inf")


def psi(g: int, m) -> float:
    """ψ(g,m) = max(0, ⌈g/m⌉-2)（m≥1）、m=1/2 は g=1 なら 0 それ以外 ∞。"""
    if m == 0.5:
        return 0 if g == 1 else INF
    return max(0, -(-g // m) - 2)


def m_of(p: int, j: int):
    """サイズ j で取り除く段の階 m_j = 2^{p-j-1}（j=p は 1/2）。"""
    if j == p:
        return 0.5
    return 1 << (p - j - 1)


def dismantle_cost(D: tuple[int, ...], p: int) -> float:
    """D = (y_k, …, y_1)。y_j は残り j 個のとき除去。T_j = {y_1..y_j}。"""
    k = len(D)
    remaining = set(D)
    total = 0.0
    for idx, y in enumerate(D):
        j = k - idx  # いま残っている個数
        pred = max([w for w in remaining if w < y], default=0)
        c = psi(y - pred, m_of(p, j))
        if c is INF or c == INF:
            return INF
        total += c
        remaining.discard(y)
    return total


def w_dismantle(T: tuple[int, ...], p: int) -> float:
    return min(dismantle_cost(D, p) for D in permutations(T)) if T else 0.0


def drop_stage(D: tuple[int, ...], x: int) -> tuple[int, ...]:
    """A♮ の操作 D∖x: x の段を落とす（前の要素はサイズ-1、後は不変）。"""
    return tuple(y for y in D if y != x)


def reseat(D: tuple[int, ...], x: int) -> tuple[int, ...]:
    """B♮ の D'': 本文 §6 の据え替え。

    y = min{w ∈ S : w > x}。(I) y なし／(II) y が x より後に除去 → D∖x。
    (III) y が x より先に除去 → x と y の段を除き、x の居た段に y を据える。
    D は除去順（先頭が最初に除去）なので「先に除去」= D 内で x より前。
    """
    S = set(D)
    above = [w for w in S if w > x]
    if not above:
        return drop_stage(D, x)
    y = min(above)
    pos_x = D.index(x)
    pos_y = D.index(y)
    if pos_y > pos_x:  # y は x より後に除去される (II)
        return drop_stage(D, x)
    # (III): y を x の段（位置）へ
    out = [w for w in D if w not in (x, y)]
    # x の位置は除去列で pos_x。y と x を抜いた列に、y を「x が居た段」へ挿入。
    # x より前に除去される要素のうち y 以外は段が 1 下がる（列位置そのまま）。
    insert_at = pos_x - 1  # y (pos_y < pos_x) を抜いたぶん 1 つ手前
    out.insert(insert_at, y)
    return tuple(out)


def check_range(p: int, maxpos: int, kmin: int, kmax: int, *, tag: str) -> int:
    import umin_dp as ud

    badA = badB = badE = 0
    ptsA = ptsB = ptsE = 0
    for k in range(kmin, kmax + 1):
        for T in combinations(range(1, maxpos + 1), k):
            wd = w_dismantle(T, p)
            wc = ud.umin_dp(T, p)
            ptsE += 1
            if (wd == INF) != (wc == INF) or (wd != INF and wd != wc):
                badE += 1
                if badE <= 5:
                    print(f"  ★同値破れ {tag}: T={set(T)} 解体={wd} DP={wc}")
            for D in permutations(T):
                cD = dismantle_cost(D, p)
                for x in T:
                    predx = max([w for w in T if w < x], default=0)
                    corr = psi(x - predx, m_of(p, k))
                    # A♮: 右辺が有限なら cost(D∖x) ≤ cost(D)+ψ(δ,m_k)
                    ptsA += 1
                    cDx = dismantle_cost(drop_stage(D, x), p)
                    if cD != INF and corr != INF and not (cDx <= cD + corr):
                        badA += 1
                        if badA <= 5:
                            print(f"  ★A♮破れ {tag}: T={set(T)} D={D} x={x}: "
                                  f"{cDx} > {cD}+{corr}")
                    # B♮（据え替えレシピ）: 右辺が有限なら cost(D'') ≤ cost(D)+1
                    ptsB += 1
                    cDD = dismantle_cost(reseat(D, x), p)
                    if cD != INF and not (cDD <= cD + 1):
                        badB += 1
                        if badB <= 5:
                            print(f"  ★B♮破れ {tag}: T={set(T)} D={D} x={x}: "
                                  f"{cDD} > {cD}+1  D''={reseat(D, x)}")
    print(f"  {tag}: 同値 {ptsE:,d} 点(破れ{badE})  A♮ {ptsA:,d} 点(破れ{badA})  "
          f"B♮レシピ {ptsB:,d} 点(破れ{badB})", flush=True)
    return badA + badB + badE


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--equiv", action="store_true")
    ap.add_argument("--p6", action="store_true")
    ap.add_argument("--p7edge", action="store_true")
    args = ap.parse_args()
    rc = 0
    if args.equiv:
        print("== 同値（解体形式 == commit DP）＋ A♮/B♮ の小さい全数 ==")
        rc |= check_range(3, 12, 1, 3, tag="p=3 位置≤12")
        rc |= check_range(4, 12, 1, 4, tag="p=4 位置≤12")
        rc |= check_range(5, 11, 1, 5, tag="p=5 位置≤11")
    if args.p6:
        print("== p=6 全数（k=p=6 の端 m=1/2 を含む）位置 ≤13 ==")
        rc |= check_range(6, 13, 1, 6, tag="p=6 位置≤13")
    if args.p7edge:
        print("== p=7 の端 k=7 全数 位置 ≤11 ==")
        rc |= check_range(7, 11, 7, 7, tag="p=7 k=7 位置≤11")
    if rc == 0:
        print("=> 反例なし（検証した範囲で証明の主張どおり）")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
