"""補題 A・B の証明（`data/conj_g_proof_attempt.md`）の各ステップを機械検査する。

検査するのは**証明に現れる主張そのもの**であって、予想 U の数値照合ではない
（そちらは `scripts/umin_dp.py` と `scripts/dismantle_dp.py`）。

  (S)   psi(a+b, 2m) + psi(b, 2m) <= psi(a, m) + psi(b, m)         … 補題 A の実体
  (S2)  psi(a+b, 2m)              <= psi(a, 2m) + psi(b, m) + 1     … 補題 B の実体
  (A♮)  任意の解体順序 D と x について
          cost(D∖x) <= cost(D) + C(x - pred_T(x); p-|T|+1)
  (B♮)  §6 の構成 D'' について cost(D'') <= cost(D) + 1

さらに **変異注入**で検出力を測る（主張を弱める／強めると反例が出ること）と、
証明の場合分け（A♮ の (a)(b1)-(b4)、B♮ の (I)(II)(III)）を実データで踏破したかを数える。

    python3 scripts/lemmaAB_proof_check.py             # 全数（数秒）＋無作為
    python3 scripts/lemmaAB_proof_check.py --quick     # 全数のみ
"""

from __future__ import annotations

import argparse
import random
import sys
from itertools import combinations, permutations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from dismantle_dp import C, dismantle_cost  # noqa: E402

INF = float("inf")


def psi(g: int, m: int) -> int:
    """m >= 1 の整数（2 冪）に対する psi。m=1/2 の端は C(g;1) 側で扱う。"""
    return max(0, -(-g // m) - 2)


# --------------------------------------------------------------------------
# 算術


def check_arith(gmax: int = 260, tmax: int = 6) -> int:
    bad = {"S": 0, "S2": 0}
    mut = {"S:弱": 0, "S:強": 0, "S2:弱": 0}
    n = 0
    for t in range(tmax):
        m = 1 << t
        for a in range(1, gmax):
            for b in range(1, gmax):
                n += 1
                if psi(a + b, 2 * m) + psi(b, 2 * m) > psi(a, m) + psi(b, m):
                    bad["S"] += 1
                if psi(a + b, 2 * m) > psi(a, 2 * m) + psi(b, m) + 1:
                    bad["S2"] += 1
                # 変異: 右辺を弱める / 左辺を強める → 反例が出るはず
                if psi(a + b, 2 * m) + psi(b, 2 * m) > psi(a, m) + psi(b, 2 * m):
                    mut["S:弱"] += 1
                if psi(a + b, m) + psi(b, 2 * m) > psi(a, m) + psi(b, m):
                    mut["S:強"] += 1
                if psi(a + b, 2 * m) > psi(a, 2 * m) + psi(b, 2 * m) + 1:
                    mut["S2:弱"] += 1
    print(f"(S) {n} 点 反例 {bad['S']} / (S2) {n} 点 反例 {bad['S2']}")
    print(f"   変異注入（反例が出れば検出力あり）: {mut}")
    ok = bad["S"] == 0 and bad["S2"] == 0 and all(v > 0 for v in mut.values())
    return 0 if ok else 1


# --------------------------------------------------------------------------
# A♮ と B♮


def pred_of(S, x) -> int:
    return max([0] + [w for w in S if w < x])


def construct_B(S: tuple[int, ...], order: tuple[int, ...], x: int) -> tuple[int, ...]:
    """§6 の構成。y = x の直上。y が x より先に消されるなら x の段へ y を据える。"""
    above = [w for w in S if w > x]
    if not above:
        return tuple(w for w in order if w != x)          # 場合 (I)
    y = min(above)
    if order.index(y) > order.index(x):
        return tuple(w for w in order if w != x)          # 場合 (II)
    out = []                                              # 場合 (III)
    for w in order:
        if w == y:
            continue
        out.append(y if w == x else w)
    return tuple(out)


def case_A(T, order, x) -> str:
    y = order[0]
    if y == x:
        return "a"
    py = pred_of(T, y)
    if y > x:
        return "b2" if py == x else "b1"
    return "b4" if y == pred_of(T, x) else "b3"


def case_B(S, order, x) -> str:
    above = [w for w in S if w > x]
    if not above:
        return "I"
    return "II" if order.index(min(above)) > order.index(x) else "III"


def check_schedules(pmax: int = 5, nmax: int = 13) -> int:
    badA = badB = badII = 0
    tot = 0
    ca = {"a": 0, "b1": 0, "b2": 0, "b3": 0, "b4": 0}
    cb = {"I": 0, "II": 0, "III": 0}
    for p in range(2, pmax + 1):
        for k in range(1, p + 1):
            for T in combinations(range(1, nmax + 1), k):
                for order in permutations(T):
                    c0 = dismantle_cost(order, p)
                    if c0 == INF:
                        continue
                    for x in T:
                        tot += 1
                        ca[case_A(T, order, x)] += 1
                        cb[case_B(T, order, x)] += 1
                        # (A♮)
                        extra = C(x - pred_of(T, x), p - k + 1)
                        c1 = dismantle_cost(tuple(w for w in order if w != x), p)
                        if not (c1 <= c0 + extra):
                            badA += 1
                        # (B♮)
                        c2 = dismantle_cost(construct_B(T, order, x), p)
                        if not (c2 <= c0 + 1):
                            badB += 1
                        # (I)(II) では増分 0 のはず
                        if case_B(T, order, x) in ("I", "II") and c1 > c0:
                            badII += 1
    print(f"(A♮) 全数 {tot} 件 反例 {badA}   場合の踏破 {ca}")
    print(f"(B♮) 全数 {tot} 件 反例 {badB}   場合の踏破 {cb}"
          f"（(I)(II) の増分 0 違反 {badII}）")
    return 1 if (badA or badB or badII) else 0


def check_random(n: int = 200000, pmax: int = 9, posmax: int = 800,
                 seed: int = 20260810) -> int:
    rng = random.Random(seed)
    badA = badB = 0
    done = 0
    worstB = -99.0
    for _ in range(n):
        p = rng.randint(2, pmax)
        k = rng.randint(1, p)
        T = tuple(sorted(rng.sample(range(1, posmax + 1), k)))
        order = list(T)
        rng.shuffle(order)
        order = tuple(order)
        c0 = dismantle_cost(order, p)
        if c0 == INF:
            continue
        x = rng.choice(T)
        extra = C(x - pred_of(T, x), p - k + 1)
        c1 = dismantle_cost(tuple(w for w in order if w != x), p)
        c2 = dismantle_cost(construct_B(T, order, x), p)
        if c1 == INF or c2 == INF:
            continue
        done += 1
        if extra < INF and c1 > c0 + extra:
            badA += 1
        if c2 > c0 + 1:
            badB += 1
        worstB = max(worstB, c2 - c0)
    print(f"無作為 {done} 件（p<= {pmax}, 位置 <= {posmax}）: "
          f"(A♮) 反例 {badA} / (B♮) 反例 {badB}、B の増分の最大 {worstB}")
    return 1 if (badA or badB) else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()
    rc = check_arith()
    rc |= check_schedules()
    if not args.quick:
        rc |= check_random()
    print("すべて反例 0" if rc == 0 else "⚠ 反例あり")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
