#!/usr/bin/env python3
"""**定理**: 鎖の最小量子空間 $p=3$ での厳密最短時間は $T(n,3) = n^2-n-3\\ (n\\ge4)$。

    python3 theorem_p3.py       # 証明の各段を全数探索で検定

これまで層3（予想）だったものが、KSS の 2 本の厳密漸化式（Cor 4.7・Cor 4.12）を
認めれば**定理になる**。以下、証明を段に分け、各段を全数探索で確かめる。

---

## 段1（縮退）: $T_P(m,2) = \\infty\\ (m\\ge3)$、$T_{UG}(m,1) = \\infty\\ (m\\ge2)$

KSS Cor 4.7 / 4.12 の $\\infty$ 条項そのもの。$s<3$ のペブルでは鎖の先端に到達できない。

## 段2（$k$ の強制）: $T_{UG}(n,2) = 2n-1 + T_{UP}(n-1,2)$

Cor 4.12 は $T_{UG}(n,2) = \\min_k[\\,2k-1 + T_{UP}(k,2) + T_{UG}(n-k,1)\\,]$。
段1 より $T_{UG}(n-k,1)$ が有限なのは $n-k\\le1$ のときだけで、$k=n$ は自己参照
（そして最小にならない）ので **$k=n-1$ が強制される**。$T_{UG}(1,1)=2$ を代入して段2。

## 段3（ghost の強制）: $T_{UP}(n,2) = 1 + T_{UG}(n,2)\\ (n\\ge3)$

$v_n$ がペブルを持つ間、部分鎖 $v_1..v_{n-1}$ に使える枠は **1 個だけ**。1 枠では
$v_2$ を置けない（$v_1$ を置いたままでないと $v_2$ の前提が満たせず、枠が足りない）。
よって $v_{n-1}$（$n-1\\ge2$）をペブルにできず、**`unpebble(v_n)` も `unghost(v_n)` も
永久に打てない**。$v_n$ を空にするには少なくとも 1 回 `ghost(v_n)` が要る。
`ghost` は前提を持たないので**最初に打ってよい**（それ以前に打てる手は $v_1$ 上の
ものだけで、ghost の後に回しても妥当性は変わらない）。ghost 直後の状態は
$T_{UG}(n,2)$ の始状態そのもの。ゆえに段3。

## 段4（閉形式）: $T_{UG}(n,2)=n^2+n-4$、$T_{UP}(n,2)=n^2+n-3\\ (n\\ge3)$

段2 と段3 から $n\\ge4$ で $T_{UG}(n,2) = 2n-1 + T_{UG}(n-1,2) + 1 = 2n + T_{UG}(n-1,2)$。
基底 $T_{UG}(3,2)=8$ から
$$T_{UG}(n,2) = 8 + \\sum_{j=4}^{n} 2j = 8 + n(n+1) - 12 = n^2+n-4 .$$

## 段5（主定理）: $T_P(n,3) = n^2-n-3\\ (n\\ge4)$

Cor 4.7 は $T_P(n,3)=\\min_k[\\,2k-1 + T_{UP}(k,2) + T_P(n-k,2)\\,]$。段1 より
$T_P(n-k,2)$ が有限なのは $n-k\\le2$、すなわち $k\\in\\{n-1,n-2\\}$ のみ。
$T_P(1,2)=1$, $T_P(2,2)=3$ を入れると**どちらも $2n-2+T_{UP}(\\cdot,2)$ の形**になり、
$T_{UP}$ は $n$ について単調増加だから $k=n-2$ が最小。段4 を代入して
$$T_P(n,3) = 2n-2 + \\bigl((n-2)^2+(n-2)-3\\bigr) = n^2-n-3 . \\qquad\\blacksquare$$

---

**依存**: KSS Cor 4.7 と Cor 4.12 が厳密であること（KSS の定理。`test_kss.py` が
$n\\le9,s\\le4$ で全数検証済み）。段3 の交換論法と有限の基底はここで機械検定する。
"""
from __future__ import annotations

import sys

import kss

INF = float("inf")


def V(f, n: int, s: int) -> float:
    if n <= 0:
        return 0 if n == 0 else INF
    x = f(n, s)
    return INF if x is None else x


def main(nmax: int = 12) -> int:
    fails: list[str] = []
    P = lambda n, s: V(kss.T_P, n, s)      # noqa: E731
    UP = lambda n, s: V(kss.T_UP, n, s)    # noqa: E731
    UG = lambda n, s: V(kss.T_UG, n, s)    # noqa: E731

    print("段1（縮退）")
    for m in range(3, nmax + 1):
        if P(m, 2) != INF:
            fails.append(f"段1: T_P({m},2)={P(m, 2)}（∞ のはず）")
    for m in range(2, nmax + 1):
        if UG(m, 1) != INF:
            fails.append(f"段1: T_UG({m},1)={UG(m, 1)}（∞ のはず）")
    if UG(1, 1) != 2:
        fails.append(f"段1: T_UG(1,1)={UG(1, 1)}（2 のはず）")
    print(f"  T_P(m,2)=∞ (m>=3) と T_UG(m,1)=∞ (m>=2)、T_UG(1,1)=2 … "
          f"{'成立' if not fails else 'NG'}")

    print("段2（k の強制）: T_UG(n,2) = 2n-1 + T_UP(n-1,2)")
    n2 = 0
    for n in range(2, nmax + 1):
        n2 += 1
        if UG(n, 2) != 2 * n - 1 + UP(n - 1, 2):
            fails.append(f"段2: n={n} で {UG(n, 2)} != {2 * n - 1 + UP(n - 1, 2)}")
    print(f"  {n2} 点")

    print("段3（ghost の強制）: T_UP(n,2) = 1 + T_UG(n,2) (n>=3)")
    n3 = 0
    for n in range(3, nmax + 1):
        n3 += 1
        if UP(n, 2) != 1 + UG(n, 2):
            fails.append(f"段3: n={n} で {UP(n, 2)} != {1 + UG(n, 2)}")
    print(f"  {n3} 点（n=1,2 は例外: T_UP(1,2)=1, T_UP(2,2)=3）")

    print("段4（閉形式）: T_UG(n,2)=n^2+n-4, T_UP(n,2)=n^2+n-3 (n>=3)")
    n4 = 0
    if UG(3, 2) != 8:
        fails.append(f"段4 の基底: T_UG(3,2)={UG(3, 2)}（8 のはず）")
    for n in range(3, nmax + 1):
        n4 += 2
        if UG(n, 2) != n * n + n - 4:
            fails.append(f"段4: T_UG({n},2)={UG(n, 2)} != {n * n + n - 4}")
        if UP(n, 2) != n * n + n - 3:
            fails.append(f"段4: T_UP({n},2)={UP(n, 2)} != {n * n + n - 3}")
    print(f"  {n4} 点（基底 T_UG(3,2)=8 を含む）")

    print("段5（主定理）: T_P(n,3) = 2n-2 + T_UP(n-2,2) = n^2-n-3 (n>=4)")
    n5 = 0
    for n in range(4, nmax + 1):
        n5 += 2
        if P(n, 3) != 2 * n - 2 + UP(n - 2, 2):
            fails.append(f"段5 の分解: T_P({n},3)={P(n, 3)} != {2 * n - 2 + UP(n - 2, 2)}")
        if P(n, 3) != n * n - n - 3:
            fails.append(f"段5: T_P({n},3)={P(n, 3)} != {n * n - n - 3}")
    # k=n-1 より k=n-2 が良い（T_UP の単調性）
    for n in range(4, nmax + 1):
        if not UP(n - 2, 2) <= UP(n - 1, 2):
            fails.append(f"段5 の単調性: T_UP({n - 2},2) > T_UP({n - 1},2)")
    print(f"  {n5} 点（k=n-2 が最小であることも確認）")

    if fails:
        print(f"\nNG {len(fails)} 件（先頭 10）:")
        for f in fails[:10]:
            print("  -", f)
        return 1
    print(f"\n証明の全段が全数探索と一致（n<={nmax}）。")
    print("T(n,3) = n^2-n-3 は KSS Cor 4.7/4.12 を認めれば定理（層2）。")
    return 0


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[1:]]
    raise SystemExit(main(*a) if a else main())
