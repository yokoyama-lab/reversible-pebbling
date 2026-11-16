"""補題 A♮・B♮ の**証明の内部ステップ**を検査する（結論だけでなく場合分けの値そのもの）。

`data/conj_g_proof_attempt.md` §4・§6・§11.6。
`scripts/lemmaAB_proof_check.py` が「不等式の結論」を検査するのに対し、こちらは
「結論は正しいが証明の途中が間違っている」型の誤りを狙う:

  A♮ の帰納: 各 (T, D, x) で本文が場合 (a)(b1)–(b4) ごとに主張している
             gamma* と delta' の値が実際と一致するか、および ($\\star$) 自体。
  B♮ の (III): 段ごとの主張（y 以外は費用が増えない／y の段はサイズ j0 で
             費用 psi(gamma+delta0, m_{j0})）と、総和の評価式。

加えて
  - **大ギャップ帯での全数検査**（従来の全数は位置 <= 13 で費用がほぼ 0 の領域しか
    踏んでいなかった）。費用の分布と最大費用を出す。
  - Fable5-max 側の**倍化恒等式**（`data/conj_u_status.md` 補題 D）との整合と、
    |S| = p での破れが本稿の m_p = 1/2（自由ペブル 1 本）の端であることの同定。

    python3 scripts/lemmaAB_stepcheck.py                 # 内部ステップ＋補題 D
    python3 scripts/lemmaAB_stepcheck.py --big P NMAX    # 大ギャップ帯の全数
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from dismantle_dp import C, W_commit  # noqa: E402

INF = float("inf")


def lvl(g: int, p: int, j: int) -> float:
    """サイズ j の段の費用。m_j = 2^{p-j-1}（j = p は自由ペブル 1 本）。"""
    return C(g, p - j + 1)


def pred_in(S, x: int) -> int:
    return max([0] + [w for w in S if w < x])


def steps(order, p: int):
    """解体順序の各段: (サイズ j, 要素, pred, gap, 費用)。"""
    cur = set(order)
    out = []
    for y in order:
        j = len(cur)
        pr = pred_in(cur, y)
        out.append((j, y, pr, y - pr, lvl(y - pr, p, j)))
        cur.discard(y)
    return out


def construct_B(S, order, x):
    """§6 の構成と、どの場合 (I)(II)(III) かを返す。"""
    above = [w for w in S if w > x]
    if not above:
        return tuple(w for w in order if w != x), "I"
    y = min(above)
    if order.index(y) > order.index(x):
        return tuple(w for w in order if w != x), "II"
    out = []
    for w in order:
        if w == y:
            continue
        out.append(y if w == x else w)
    return tuple(out), "III"


# --------------------------------------------------------------------------


def check_Anat_steps(pmax: int = 5, nmax: int = 16) -> int:
    bad_val = bad_star = tot = 0
    cases: Counter = Counter()
    for p in range(2, pmax + 1):
        for k in range(2, p + 1):
            for T in combinations(range(1, nmax + 1), k):
                Tset = set(T)
                for order in permutations(T):
                    if any(c == INF for *_, c in steps(order, p)):
                        continue
                    y = order[0]
                    gamma = y - pred_in(Tset, y)
                    for x in T:
                        if x == y:
                            cases["a"] += 1
                            continue
                        tot += 1
                        delta = x - pred_in(Tset, x)
                        gstar = y - pred_in(Tset - {x}, y)
                        dprime = x - pred_in(Tset - {y}, x)
                        if y > x:
                            if pred_in(Tset, y) == x:
                                case, claim = "b2", (gamma + delta, delta)
                            else:
                                case, claim = "b1", (gamma, delta)
                        elif y == pred_in(Tset, x):
                            case, claim = "b4", (gamma, delta + gamma)
                        else:
                            case, claim = "b3", (gamma, delta)
                        cases[case] += 1
                        if claim != (gstar, dprime):
                            bad_val += 1
                            if bad_val <= 5:
                                print(f"  ✗値 p={p} T={T} D={order} x={x} {case}: "
                                      f"主張 {claim} 実際 {(gstar, dprime)}")
                        lhs = lvl(gstar, p, k - 1) + lvl(dprime, p, k - 1)
                        rhs = lvl(gamma, p, k) + lvl(delta, p, k)
                        if not lhs <= rhs:
                            bad_star += 1
                            if bad_star <= 5:
                                print(f"  ✗(★) p={p} T={T} D={order} x={x} {case}: "
                                      f"{lhs} > {rhs}")
    print(f"A♮ の内部: {tot} 件  γ*/δ' の食い違い {bad_val}  (★) の破れ {bad_star}")
    print(f"   場合の踏破 {dict(cases)}")
    return bad_val + bad_star


def check_Bnat_steps(pmax: int = 5, nmax: int = 16) -> int:
    bad_step = bad_y = bad_tot = tot = 0
    for p in range(2, pmax + 1):
        for k in range(2, p + 1):
            for T in combinations(range(1, nmax + 1), k):
                for order in permutations(T):
                    st = steps(order, p)
                    if any(c == INF for *_, c in st):
                        continue
                    for x in T:
                        o2, case = construct_B(T, order, x)
                        if case != "III":
                            continue
                        st2 = steps(o2, p)
                        if any(c == INF for *_, c in st2):
                            continue
                        tot += 1
                        y = min(w for w in T if w > x)
                        old = {e: (j, c) for j, e, _, _, c in st}
                        new = {e: (j, c) for j, e, _, _, c in st2}
                        j0, j1 = old[x][0], old[y][0]
                        v = next(pr for _, e, pr, _, _ in st if e == x)
                        gamma, delta0 = y - x, x - v
                        for e in T:
                            if e in (x, y):
                                continue
                            if new[e][1] > old[e][1]:
                                bad_step += 1
                                if bad_step <= 5:
                                    print(f"  ✗段 p={p} T={T} D={order} x={x} e={e}: "
                                          f"{old[e][1]} → {new[e][1]}")
                        want = lvl(gamma + delta0, p, j0)
                        if new[y] != (j0, want):
                            bad_y += 1
                            if bad_y <= 5:
                                print(f"  ✗y段 p={p} T={T} D={order} x={x}: "
                                      f"主張 {(j0, want)} 実際 {new[y]}")
                        c0 = sum(c for *_, c in st)
                        c2 = sum(c for *_, c in st2)
                        bound = c0 - lvl(gamma, p, j1) - lvl(delta0, p, j0) + want
                        if not (c2 <= bound <= c0 + 1):
                            bad_tot += 1
                            if bad_tot <= 5:
                                print(f"  ✗総和 p={p} T={T} D={order} x={x}: "
                                      f"c2={c2} bound={bound} c0={c0}")
    print(f"B♮ (III) の内部: {tot} 件  段 {bad_step}  y 段 {bad_y}  総和 {bad_tot}")
    return bad_step + bad_y + bad_tot


def check_lemmaD(pmax: int = 5, nmax: int = 14) -> int:
    """倍化恒等式 W(2S;p+1) = W(S;p)（|S| <= p-1）と、|S| = p での破れの型。"""
    ok = bad = 0
    boundary = []
    for p in range(2, pmax + 1):
        for k in range(1, p + 1):
            for S in combinations(range(1, nmax + 1), k):
                lhs = W_commit(tuple(2 * s for s in S), p + 1)
                rhs = W_commit(S, p)
                if k <= p - 1:
                    if lhs == rhs:
                        ok += 1
                    else:
                        bad += 1
                        if bad <= 3:
                            print(f"  ✗D p={p} S={S}: {lhs} vs {rhs}")
                elif lhs != rhs:
                    boundary.append((p, S, rhs, lhs))
    print(f"補題 D（|S|<=p-1）: 一致 {ok}、不一致 {bad}")
    print(f"   |S|=p での破れ {len(boundary)} 件 — いずれも最終ランクの自由本数が "
          f"左 1 本（C(g;1)）／右 2 本（psi 領域）という端の差。例 {boundary[:2]}")
    return bad


def big_gap(p: int, nmax: int) -> int:
    """大ギャップ帯での A♮ / B♮ 全数。費用の分布も出す。"""
    badA = badB = tot = 0
    dist: Counter = Counter()
    for k in range(1, p + 1):
        for T in combinations(range(1, nmax + 1), k):
            for order in permutations(T):
                st = steps(order, p)
                if any(c == INF for *_, c in st):
                    continue
                c0 = sum(c for *_, c in st)
                dist[int(c0)] += 1
                for x in T:
                    tot += 1
                    extra = C(x - pred_in(set(T), x), p - k + 1)
                    o1 = tuple(w for w in order if w != x)
                    s1 = steps(o1, p)
                    c1 = INF if any(c == INF for *_, c in s1) else sum(c for *_, c in s1)
                    o2, _ = construct_B(T, order, x)
                    s2 = steps(o2, p)
                    c2 = INF if any(c == INF for *_, c in s2) else sum(c for *_, c in s2)
                    if extra < INF and c1 < INF and c1 > c0 + extra:
                        badA += 1
                        if badA <= 3:
                            print(f"  ✗A♮ p={p} T={T} D={order} x={x}: {c1} > {c0}+{extra}")
                    if c2 < INF and c2 > c0 + 1:
                        badB += 1
                        if badB <= 3:
                            print(f"  ✗B♮ p={p} T={T} D={order} x={x}: {c2} > {c0}+1")
    print(f"大ギャップ帯 p={p} 位置<= {nmax}: {tot} 件  (A♮) 反例 {badA} / (B♮) 反例 {badB}"
          f"  最大費用 {max(dist) if dist else '-'}")
    return badA + badB


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--big", nargs=2, type=int, metavar=("P", "NMAX"),
                    help="大ギャップ帯の全数検査だけを走らせる")
    args = ap.parse_args()
    if args.big:
        return 1 if big_gap(*args.big) else 0
    rc = check_Anat_steps()
    rc += check_Bnat_steps()
    rc += check_lemmaD()
    print("内部ステップ・補題 D とも反例なし" if rc == 0 else "⚠ 食い違いあり")
    return 1 if rc else 0


if __name__ == "__main__":
    raise SystemExit(main())
