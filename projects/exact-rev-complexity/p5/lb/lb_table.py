#!/usr/bin/env python3
"""下界 LB(h) = Fc(2^h-1, p_h) の表（PROOF.md の数値の出典）.

p_h は Chan--Lauria--Nordström--Vinyals（arXiv:2305.19104）Theorem 3.3 の式
    persistent price of a complete binary tree of height H = H + g^{-1}(H)
を，高さの規約を合わせて（彼らの H = 原稿の h-1）p_h = (h-1) + g^{-1}(h-1) として計算する（h>=2）．
h<=12 は原稿 表 1 の p_min と，h<=7 は全数探索の値と照合する．

補題 B の明示的な下界（計数関数の優解による）も並べる:
    Fc(n,S) >= (n-1)·v,  v = floor( ((n-1)θ/2)^{1/q} ρ^{-S} ),  θ = 1 - ρ^{-q} - (1+ρ)^{-q}  (ρ > ρ_c(q))
"""

from __future__ import annotations

import math
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from chain import Row  # noqa: E402

PMIN_MS = {1: 1, 2: 3, 3: 5, 4: 6, 5: 7, 6: 8, 7: 10, 8: 11, 9: 12, 10: 13, 11: 14, 12: 15}
MSTAR = {1: 1, 2: 5, 3: 17, 4: 53, 5: 155, 6: 429, 7: 1001}
FSTAR = {8: 2789, 9: 7649, 10: 20995, 11: 56881, 12: 154125}


def g(D: int) -> int:
    return 0 if D == 1 else 2 ** (g(D - 1) + D - 2) + g(D - 1)


def ginv(H: int) -> int:
    D = 1
    while g(D) < H:
        D += 1
    return D


def p_clnv(h: int) -> int:
    return 1 if h == 1 else (h - 1) + ginv(h - 1)


def rho_c(q: float) -> float:
    lo, hi = 1.0, 10.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if mid ** (-q) + (1 + mid) ** (-q) > 1:
            lo = mid
        else:
            hi = mid
    return hi


def explicit_lb(n: int, S: int, q: float, rho: float) -> int:
    th = 1 - rho ** (-q) - (1 + rho) ** (-q)
    assert th > 0
    v = math.floor(((n - 1) * th / 2) ** (1 / q) * rho ** (-S))
    return (n - 1) * max(v, 0)


def main():
    assert all(p_clnv(h) == PMIN_MS[h] for h in PMIN_MS), "p_h の式が原稿の表と合わない"
    jumps = [h for h in range(2, 200) if p_clnv(h) - h != p_clnv(h - 1) - (h - 1)]
    print(f"p_h - h が増える h（h<200）: {jumps}（原稿: h=2,3,7,135）")
    q = 1.5153832361
    rc = rho_c(q)
    print(f"q*={q}, rho_c(q*)={rc:.9f}, V(q*)=1/q-log2 rho_c={1 / q - math.log2(rc):.9f}")
    rho = rc * 1.001
    print("\nh  n  p_h  LB=Fc(n,p_h)  参照値(M* or F*)  参照/LB  log LB/log n  明示式の下界")
    for h in list(range(2, 13)) + [16, 20, 24, 28, 32, 36, 40]:
        n = 2 ** h - 1
        p = p_clnv(h)
        lb = Row.Fc(n, p)
        ref = MSTAR.get(h, FSTAR.get(h))
        refs = f"{ref} ({'M*' if h in MSTAR else 'F*'})" if ref else "-"
        rat = f"{ref / lb:.3f}" if ref else "-"
        ex = explicit_lb(n, p, q, rho)
        print(f"{h} {n} {p} {lb} {refs} {rat} {math.log(lb) / math.log(n):.4f} {ex}")
        if ref:
            assert lb <= ref
        assert ex <= lb


if __name__ == "__main__":
    main()
