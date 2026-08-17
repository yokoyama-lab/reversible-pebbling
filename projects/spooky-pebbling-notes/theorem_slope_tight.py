#!/usr/bin/env python3
"""【定理E'】任意の傾き $2m$ の**緊密な**下界 $T_{UP}(n,s)\\ge 2mn-\\beta_m(s)$。

    python3 theorem_slope_tight.py            # 全数照合
    python3 theorem_slope_tight.py 8 7        # m<=8, s<=7 まで

## なぜ定理E は緩んだのか（2026-08-18 に判明）

定理E（`theorem_slope6.py`）の係数 $c_m$ は $m\\ge4$ で緩む（$c_4(3)=38$、実測 34）。
原因は望遠鏡の**頭の項**にある。定理E は Cor 4.12 に

$$T_{UP}(k,s)\\ \\ge\\ T_{UG}(k,s)-1 \\qquad(\\text{KSS Lemma 4.10})$$

を入れるが、**最大点は $\\delta=-1$ の領域にあり、そこでは $T_{UP}=T_{UG}+1$**。
つまり 1 段ごとに **2 だけ損**をしている（下の `δ の向き` の表がその証拠）。

## 直し方: $T_{UP}$ 自身の分解で回す

$T_{UG}$ ではなく $T_{UP}$ の分解（`exchange.py` / `Decomp.lean`）で望遠鏡を回すと
$T_{UG}\\to T_{UP}$ の変換が要らないので損が出ない:

$$(2k-1) + \\bigl(2(m{-}1)k-\\beta_{m-1}(s)\\bigr) + \\bigl(2m(n{-}k)-\\beta_m(s{-}1)\\bigr)
  = 2mn - \\bigl(\\beta_{m-1}(s)+\\beta_m(s-1)+1\\bigr)$$

で **$k$ が消える**。係数は

$$\\beta_1(s)=1,\\qquad \\beta_m(2)=m^2-m+3,\\qquad
  \\beta_m(s)=\\beta_{m-1}(s)+\\beta_m(s-1)+1\\ (s\\ge3).$$

底の $s=2$ は閉形式 $T_{UP}(n,2)=n^2+n-3$（`Cap2.lean`、層1）から出る。要るのは
$2mn\\le n^2+n+m^2-m$ で、これは $(n-m)(n-m+1)\\ge0$ そのもの。

## 実測との一致（このファイルが検定する）

* $\\beta_m(s) = \\max_n(2mn-T_{UP}(n,s))$ が **$m\\le8$, $s\\le7$ で完全一致**
* $m\\ge3$ で $\\max_n(2mn-T_{UG}(n,s)) = \\beta_m(s)+1$ — **下界は緊密**
* $\\beta_2(s)=2s+1$（定理A の $T_{UP}$ 版）、$\\beta_3(s)=s(s+3)-1$（`Sign.lean`）と一致
* $m\\ge4$ では定理E より真に強い（$m=6,s=5$ で 434 対 502）

**層1（Lean 機械証明）**: `spooky-pebbling-lean/SpookyPebbling/SlopeTight.lean` の
`TUP_ge_slope_tight` / `TUG_ge_slope_tight`。緊密性（構成側）は未証明で層2 のまま。
"""
from __future__ import annotations

import sys
from functools import lru_cache

import closed2

INF = float("inf")


@lru_cache(maxsize=None)
def beta(m: int, s: int) -> int:
    """定理E' の係数 β_m(s)。"""
    if m <= 1:
        return 1
    if s <= 2:
        return m * m - m + 3
    return beta(m - 1, s) + beta(m, s - 1) + 1


@lru_cache(maxsize=None)
def c(m: int, s: int) -> int:
    """定理E の係数（比較用）。"""
    if m <= 1:
        return 0
    if s <= 1:
        return 2 * (m - 1)
    return c(m - 1, s) + c(m, s - 1) + 2


def measured(fn, m: int, s: int, nmax: int):
    best = None
    for n in range(1, nmax + 1):
        v = fn(n, s)
        if v == INF:
            continue
        g = 2 * m * n - int(v)
        if best is None or g > best:
            best = g
    return best


def main() -> int:
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    smax = int(sys.argv[2]) if len(sys.argv) > 2 else 7
    sys.setrecursionlimit(200000)
    fails: list[str] = []
    cnt = 0

    print(f"定理E' の検定（m<={mmax}, s<={smax}）")
    for s in range(2, smax + 1):
        nmax = min(4000, 60 * s * s)
        for m in range(1, mmax + 1):
            b = measured(closed2.T_UP, m, s, nmax)
            g = measured(closed2.T_UG, m, s, nmax)
            cnt += 2
            if b != beta(m, s):
                fails.append(f"β({m},{s}): 実測 {b} != 漸化式 {beta(m, s)}")
            if m >= 3 and g != b + 1:
                fails.append(f"γ({m},{s})={g} != β+1={b + 1}（緊密性）")
    print(f"  {cnt} 点")

    print("\n既知の閉形式との一致:")
    for s in range(2, smax + 1):
        if beta(2, s) != 2 * s + 1:
            fails.append(f"β_2({s})={beta(2, s)} != 2s+1")
        if beta(3, s) != s * (s + 3) - 1:
            fails.append(f"β_3({s})={beta(3, s)} != s(s+3)-1")
    print(f"  β_2(s)=2s+1・β_3(s)=s(s+3)-1 を s=2..{smax} で確認")

    print("\n定理E' と定理E の比較（小さいほど強い）:")
    print(f"{'m':>2} {'s':>2} {'E′: β+1':>10} {'E: c':>8} {'改善':>6}")
    for m in range(2, min(mmax, 6) + 1):
        for s in range(3, min(smax, 5) + 1):
            print(f"{m:>2} {s:>2} {beta(m, s) + 1:>10} {c(m, s):>8} {c(m, s) - beta(m, s) - 1:>6}")

    print("\nδ の向き（β_m(s) - γ_m(s)）: +1 なら最大点で T_UP=T_UG-1、-1 なら T_UP=T_UG+1")
    print(f"{'s':>2} | " + " ".join(f"{m:>4}" for m in range(1, min(mmax, 6) + 1)))
    for s in range(2, min(smax, 6) + 1):
        nmax = min(4000, 60 * s * s)
        row = []
        for m in range(1, min(mmax, 6) + 1):
            b = measured(closed2.T_UP, m, s, nmax)
            g = measured(closed2.T_UG, m, s, nmax)
            row.append(b - g)
        print(f"{s:>2} | " + " ".join(f"{x:>4}" for x in row))
    print("  → m<=2 では +1（δ=+1 の領域）、m>=3 では -1（δ=-1 の領域）。"
          "\n    これが「定理E が m>=4 で 2 ずつ損をする」ことの直接の証拠。")

    print("\n上包絡: T_UP(n,s) == max_m (2mn - β_m(s))  ← 構成側の目標はこの形")
    env_cnt = 0
    for s in range(2, min(smax, 5) + 1):
        for n in range(1, 61):
            v = closed2.T_UP(n, s)
            if v == INF:
                continue
            env = max(2 * m * n - beta(m, s) for m in range(1, 2 * n + 4))
            env_cnt += 1
            if env != int(v):
                fails.append(f"上包絡 破れ: T_UP({n},{s})={int(v)} != {env}")
    print(f"  {env_cnt} 点")
    print("  → 各傾き 2m は **ある n の区間でだけ** 包絡を与える（s=4 の例）:")
    rng: dict[int, list[int]] = {}
    for n in range(1, 61):
        v = closed2.T_UP(n, 4)
        if v == INF:
            continue
        for m in range(1, 2 * n + 4):
            if 2 * m * n - beta(m, 4) == int(v):
                rng.setdefault(m, [n, n])[1] = n
    for m in sorted(rng):
        print(f"     m={m} (傾き{2 * m}): n ∈ [{rng[m][0]}..{rng[m][1]}]")
    print("  したがって上界（構成）の目標は「任意の m で T_UP ≤ 2mn-β_m(s)」ではなく")
    print("  **各 m について、その傾きが包絡を与える区間で達成する**（定理F と同じ形）。")

    if fails:
        print(f"\nNG {len(fails)} 件（先頭 10）:")
        for f in fails[:10]:
            print("  -", f)
        return 1
    print("\nすべて成立。β は実測と完全一致し、m>=3 で緊密。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
