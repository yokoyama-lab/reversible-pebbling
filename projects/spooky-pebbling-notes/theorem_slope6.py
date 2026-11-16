#!/usr/bin/env python3
"""【定理】$T_{UG}(n,s) \\ge 6n - s(s+3)$、および上包絡全体の下界。

    python3 theorem_slope6.py

## 定理D（傾き 6 の下界・無条件）

$s\\ge2$ とすべての $n$ で $T_{UG}(n,s) \\ge 6n - s(s+3)$。

**証明**（$s$ の帰納法）。まず**任意の $k$ で $T_{UP}(k,s)\\ge 4k-2s-1$**（定理A の
$T_{UG}\\ge4k-2s$ と KSS Lemma 4.10 の $T_{UP}\\ge T_{UG}-1$）。Cor 4.12 の各項に
これと帰納法の仮定 $T_{UG}(\\mu,s{-}1)\\ge 6\\mu-(s{-}1)(s{+}2)$ を入れると:
$$(2k-1) + (4k-2s-1) + \\bigl(6(n-k)-(s-1)(s+2)\\bigr) = 6n - s^2-3s = 6n-s(s+3)$$
**ここでも $k$ が消える**（$2k+4k-6k=0$）。$k=n$ の項も $T_{UG}(0,\\cdot)=0 \\ge
-(s-1)(s+2)$ なので同じ評価でよい。基底 $s=2$: $T_{UG}(n,2)=n^2+n-4\\ (n\\ge3)$ が
$6n-10$ 以上 $\\iff (n-2)(n-3)\\ge0$ で成立、$n=1,2$ も直接確認。∎

## 定理E（上包絡全体の下界）

同じ望遠鏡が任意の傾きで回る。$T_{UG}(n,s) \\ge 2mn - c_m(s)$ where
$$c_1 = 0,\\qquad c_m(s) = c_{m-1}(s) + c_m(s-1) + 2 .$$
（傾き $2m$ を出すには $T_{UP}$ の傾き $2(m-1)$ の下界が要り、それは 1 段下の
$T_{UG}$ の下界と Lemma 4.10 から来る。）

$m\\le3$ では $c_2(s)=2s$・$c_3(s)=s(s+3)$ と**厳密に一致**するが、
**$m\\ge4$ では緩む**（$c_4(4)$ は漸化式が 64、実測の折れ目からは 62）。
傾き 8 以降を厳密にするには別の材料が要る。

## θ のギャップには効かない（記録）

$n=\\theta(s)$ では $6n-s(s+3) = 4n-2s = 2s^2$ で**2 本の線が一致する**ので、定理D は
その点で新しい情報を与えない。定理D を Cor 4.12 の「各項 $\\ge$ 左辺」に入れ直すと
$T_{UP}(\\theta,s) \\ge 2n-1$（$n\\le2\\theta-s$ が制約）で、最良でも $4\\theta-2s-1$ 止まり。
**排除したいのがちょうどその値なので、1 だけ足りない。**
"""
from __future__ import annotations

from functools import lru_cache

import closed2

INF = float("inf")


def theta(s: int) -> int:
    return s * (s + 1) // 2


@lru_cache(maxsize=None)
def c(m: int, s: int) -> int:
    """定理E の係数。c_1=0、c_m(s)=c_{m-1}(s)+c_m(s-1)+2。"""
    if m <= 1:
        return 0
    if s <= 1:
        # s=1 では T_UG が有限なのは n=1 の 2 だけ。2m*1 - c <= 2 から
        # 最良（最小）の基底は c_m(1) = 2m-2。ここを緩めると全体が 2 ずつずれる。
        return 2 * (m - 1)
    return c(m - 1, s) + c(m, s - 1) + 2


def main() -> int:
    fails: list[str] = []
    cD = cE = 0

    print("定理D: T_UG(n,s) >= 6n - s(s+3)")
    for s in range(2, 11):
        for n in range(1, min(200, 4 * s * s) + 1):
            v = closed2.T_UG(n, s)
            if v == INF:
                continue
            cD += 1
            if v < 6 * n - s * (s + 3):
                fails.append(f"定理D 破れ: T_UG({n},{s})={v} < {6 * n - s * (s + 3)}")
    print(f"  {cD} 点")

    print("定理D の緊密性: theta(s) <= n <= B(4,s)-1 で等号（＝傾き6の直線に乗る）")
    tight = 0
    for s in range(3, 9):
        n = theta(s)
        while closed2.T_UG(n, s) == 6 * n - s * (s + 3):
            tight += 1
            n += 1
        if n <= theta(s):
            fails.append(f"s={s}: theta({s}) で等号にならない")
    print(f"  {tight} 点で等号")

    print("定理E: T_UG(n,s) >= 2mn - c_m(s)（c_1=0, c_m(s)=c_{m-1}(s)+c_m(s-1)+2）")
    for s in range(2, 9):
        for m in range(1, 6):
            for n in range(1, min(200, 4 * s * s) + 1):
                v = closed2.T_UG(n, s)
                if v == INF:
                    continue
                cE += 1
                if v < 2 * m * n - c(m, s):
                    fails.append(f"定理E 破れ: m={m} T_UG({n},{s})={v} < {2 * m * n - c(m, s)}")
    print(f"  {cE} 点")

    print("\nc_m(s) と実測の係数の比較（小さいほど強い下界）:")
    print(f"{'s':>2} {'c_2 (=2s)':>12} {'c_3 (=s(s+3))':>16} {'c_4 漸化式':>12} {'c_4 実測':>10}")
    for s in range(3, 8):
        # 実測の c_4: 傾き 8 の直線の切片
        n0 = None
        prev = None
        for n in range(2, 8 * s * s):
            d = int(closed2.T_UG(n, s) - closed2.T_UG(n - 1, s))
            if d == 8 and prev != 8:
                n0 = n
                break
            prev = d
        c4_meas = int(8 * n0 - closed2.T_UG(n0, s)) if n0 else None
        print(f"{s:>2} {c(2, s):>12} {c(3, s):>16} {c(4, s):>12} {str(c4_meas):>10}")
        if c(2, s) != 2 * s:
            fails.append(f"c_2({s})={c(2, s)} != 2s")
        if c(3, s) != s * (s + 3):
            fails.append(f"c_3({s})={c(3, s)} != s(s+3)")

    print("\n定理F（傾き6の領域の厳密値）: theta(s) <= n <= B(4,s)-1 で T_UG = 6n-s(s+3)")
    print("  上界も同じ望遠鏡: k in [s, theta(s)-1] を選び n-k を s-1 の傾き6領域に落とす。")
    print("  可能な n の上限は (B(4,s-1)-1) + (theta(s)-1) なので B(4,s) = B(4,s-1)+theta(s)-1。")
    cF = 0
    b4 = {}
    for s in range(3, 9):
        prev = None
        for n in range(2, 8 * s * s):
            d = int(closed2.T_UG(n, s) - closed2.T_UG(n - 1, s))
            if d == 8 and prev != 8:
                b4[s] = n
                break
            prev = d
    for s in range(4, 9):
        want = b4[s - 1] + theta(s) - 1
        cF += 1
        if b4[s] != want:
            fails.append(f"定理F の B(4,{s})={b4[s]} != B(4,{s - 1})+theta({s})-1={want}")
    for s in range(3, 9):
        for n in range(theta(s), b4[s]):
            cF += 1
            if closed2.T_UG(n, s) != 6 * n - s * (s + 3):
                fails.append(f"定理F 破れ: T_UG({n},{s}) != {6 * n - s * (s + 3)}")
    print(f"  {cF} 点（B(4,s) の漸化 5 点を含む）。B(4,s) 実測: "
          + ", ".join(f"s={s}:{b4[s]}" for s in sorted(b4)))

    if fails:
        print(f"\nNG {len(fails)} 件（先頭 10）:")
        for f in fails[:10]:
            print("  -", f)
        return 1
    print("\nすべて成立。c_2・c_3 は厳密、c_4 以降は漸化式のほうが緩い（表の右2列）。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
