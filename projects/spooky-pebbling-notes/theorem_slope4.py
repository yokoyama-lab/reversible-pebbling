#!/usr/bin/env python3
"""【定理】$T_{UG}(n,s) = 4n-2s$ と $T_{UP}(n,s) = 4n-2s-1$（傾き 4 の領域）。

    python3 theorem_slope4.py

**$T_{UP}$ の分解の $\\ge$ 方向を使わずに**、次まで証明できる。
この経路だけでは各 $s$ につき **$n=\\theta(s)$ の 1 点**が残る。
その 1 点は `exchange.py`（$T_{UP}$ 分解の $\\ge$ 方向）で 2026-08-13 に閉じた。
本ファイルは「分解に依存しない独立経路」としての価値があるので残してある。

---

## 定理A（下界・無条件）: $T_{UG}(n,s) \\ge 4n-2s$（$s\\ge2$、すべての $n$）

$s$ についての帰納法。$s=2$ は `theorem_p3.py` の段4 で示した閉形式から:
$T_{UG}(1,2)=2\\ge0$、$T_{UG}(2,2)=4\\ge4$、$m\\ge3$ で $m^2+m-4\\ge 4m-4 \\iff m\\ge3$。

$s\\ge3$: KSS Cor 4.12 の各項に、既証明の $T_{UP}(k,s)\\ge 2k-1$ と帰納法の仮定
$T_{UG}(m,s-1)\\ge 4m-2(s-1)$ を入れると、**$k$ が消える**:
$$2k-1 + T_{UP}(k,s) + T_{UG}(n-k,s-1) \\ \\ge\\ (2k-1)+(2k-1)+4(n-k)-2(s-1) = 4n-2s .$$
最小も $4n-2s$ 以上。∎

## 定理B: $s \\le n \\le \\theta(s)$ で $T_{UG}(n,s) = 4n-2s$

上界は `upper_bound.py` の定理（Cor 4.12 の構成側）、下界は定理A。∎

## 定理C: $s \\le n \\le \\theta(s)-1$ で $T_{UP}(n,s) = 4n-2s-1$、ゆえに $T_{UG}-T_{UP}=+1$

**上界**（$s$ の帰納法。$T_{UP}$ 分解の $\\le$ 方向＝構成のみ使う）:
基底 $n=s$ は補題4 の $T_{UP}(s,s)=2s-1=4s-2s-1$。
- $s\\le n\\le\\theta(s{-}1)$ では $k=1$: $1 + T_{UP}(n{-}1,s{-}1) + 1 \\le 2+(4(n{-}1)-2(s{-}1)-1) = 4n-2s-1$
- $\\theta(s{-}1)<n\\le\\theta(s)-1$ では $k=n-\\theta(s{-}1)+1 \\in[2,s]$:
  $n-k=\\theta(s{-}1)-1$ に固定され、$k\\le s$ だから補題4 で $T_{UP}(k,s)=2k-1$。
  $(2k-1)+(4(\\theta(s{-}1)-1)-2(s{-}1)-1)+(2k-1) = 4n-2s-1$

**下界**: KSS Lemma 4.10 の $T_{UG}\\le T_{UP}+1$ と定理B から
$T_{UP}\\ge T_{UG}-1 = 4n-2s-1$。∎

## 残るギャップ（各 $s$ につき 1 点）

$n=\\theta(s)$ で $T_{UP} = 4n-2s+1$（$=T_{UG}+1$）であること。パリティと KSS の $\\pm1$ から
$T_{UP}\\in\\{4n-2s-1,\\ 4n-2s+1\\}$ までは確定しているので、**$4n-2s-1$ ではないこと**を
言えばよい。これが言えれば $\\theta(s)=s(s+1)/2$ が定理になる。

### 現行の道具では届かない（試して分かったことの記録）

Cor 4.12 は「最小＝左辺」なので**各項が左辺以上**、すなわち任意の $n>k$ で
$$T_{UP}(k,s) \\ \\ge\\ T_{UG}(n,s) - (2k-1) - T_{UG}(n-k,s-1)$$
という $T_{UP}$ の下界が得られる。$k=\\theta(s)$ を入れ、定理A の下界
$T_{UG}(n,s)\\ge4n-2s$ と定理B の上界 $T_{UG}(m,s-1)=4m-2(s-1)$ を使うと
$$\\ge (4n-2s) - (2\\theta-1) - \\bigl(4(n-\\theta)-2(s-1)\\bigr) = 2\\theta-1$$
となり、**$n$ が消えて自明な下界しか出ない**。定理A の下界がちょうど傾き 4 の直線
なので、望遠鏡のように打ち消し合ってしまう。Cor 4.7 経由（Thm 4.11 で $T_P$ に
移す）も同様に $T_{UP}(n,s)\\ge 2n-2s+1$ という自明な下界に落ちる。

**したがって、この 1 点を閉じるには新しい材料が要る**。候補は 2 つ:
(i) $T_{UP}$ の分解の $\\ge$ 方向（sweep-first の unpebbling 版）、
(ii) 傾き 6 の領域での $T_{UG}$ の下界（$T_{UG}\\ge 6n-s(s+3)$）を直接示すこと。
**同じ道（定理A の下界を Cor 4.12 に入れ直す）を再試行しないこと。**
"""
from __future__ import annotations

import closed2

INF = float("inf")


def theta(s: int) -> int:
    return s * (s + 1) // 2


def main() -> int:
    fails: list[str] = []
    cA = cB = cC = cD = 0

    for s in range(2, 11):
        nmax = min(200, 4 * s * s)
        for n in range(1, nmax + 1):
            v = closed2.T_UG(n, s)
            if v == INF:
                continue
            cA += 1
            if v < 4 * n - 2 * s:
                fails.append(f"定理A 破れ: T_UG({n},{s})={v} < {4 * n - 2 * s}")

        for n in range(s, theta(s) + 1):
            cB += 1
            if closed2.T_UG(n, s) != 4 * n - 2 * s:
                fails.append(f"定理B 破れ: T_UG({n},{s})={closed2.T_UG(n, s)} != {4 * n - 2 * s}")

        for n in range(s, theta(s)):
            cC += 1
            got = closed2.T_UP(n, s)
            if got != 4 * n - 2 * s - 1:
                fails.append(f"定理C 破れ: T_UP({n},{s})={got} != {4 * n - 2 * s - 1}")
            if closed2.T_UG(n, s) - got != 1:
                fails.append(f"定理C の系 破れ: n={n} s={s} で delta={closed2.T_UG(n, s) - got}")

        # 残るギャップ: n = theta(s) の 1 点
        n = theta(s)
        cD += 1
        got = closed2.T_UP(n, s)
        if got != 4 * n - 2 * s + 1:
            fails.append(f"ギャップ点 破れ: T_UP({n},{s})={got} != {4 * n - 2 * s + 1}")

    print(f"定理A（下界 T_UG>=4n-2s）: {cA} 点")
    print(f"定理B（T_UG=4n-2s on [s,theta]）: {cB} 点")
    print(f"定理C（T_UP=4n-2s-1 on [s,theta-1] と delta=+1）: {cC} 点")
    print(f"この経路だけで残る 1 点（n=theta(s) で T_UP=4n-2s+1）: {cD} 点（s=2..10）")
    if fails:
        print(f"\nNG {len(fails)} 件（先頭 10）:")
        for f in fails[:10]:
            print("  -", f)
        return 1
    print("\nすべて成立。この経路（分解に依存しない）で証明済みなのは A・B・C。")
    print("各 s につき n=theta(s) の 1 点だけはこの経路では出ないが、")
    print("T_UP 分解の >= 方向（exchange.py、2026-08-13）で閉じている。未証明は無い。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
