#!/usr/bin/env python3
"""INEQ の具体的な破れ（予算を何倍に緩めても，実現可能な P で破れる）を BFS で確かめる.

森 Φ = 長さ L の鎖（頂点 0 が頂，L-1 が底の葉）＋孤立点 z．C = {0, z}，c* = z（最後に置く）．
P = {0, L-1}（頂と底）．P ⊇ C∖{z} ∪ ch(z) = {0}，z ∉ P．
緩めた仮説 Ψ^{(a,b)}_B(X) = Σ_i F_c(m_i, aB + b - i + 1)（m は X の領域の大きさの降順）．
INEQ^{(a,b)}: 1 + Ψ^{(a,b)}_B(P) + Ψ^{(a,b)}_{B-2}^{Φ/C}(P∖C) >= Ψ^{(a,b)}_B(C)．
P の領域は {0..L-2}（大きさ L-1）と {L-1}（1），C の領域は {0..L-1}（L）と {z}（1），
Φ/C での P∖C = {L-1} の領域は {L-1}（1）．よって INEQ ⟺ F_c(L, S') - F_c(L-1, S') <= 2（S' = aB+b），
すなわち δ(L, S') <= 1 ⟺ L <= S'．L > aB + b なら破れる．
ここでは BFS で d_B(∅,P), d_B(∅,C), 後半の距離が有限（実現可能）であることと，補題 D の分解の値を確かめる．
"""
from __future__ import annotations

import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import forest as F  # noqa: E402
from chain import Row, INF  # noqa: E402  (forest.py が lb/ を path に入れる)


def psi_ab(sizes, B, a, b):
    s = 0
    for i, m in enumerate(sorted(sizes, reverse=True)):
        bud = a * B + b - i
        if bud <= 0:
            return INF
        f = Row.Fc(m, bud)
        if f == INF:
            return INF
        s += f
    return s


def check(L, B, a, b):
    n = L + 1
    z = L
    par = [-1] + [i - 1 for i in range(1, L)] + [-1]  # 頂点 i の親は i-1（0 が頂，子は i+1），z は孤立
    C = (1 << 0) | (1 << z)
    P = (1 << 0) | (1 << (L - 1))
    D = F.bfs_all(par, B)
    alive2 = ((1 << n) - 1) & ~C
    par2 = [(-1 if (p >= 0 and (C >> p) & 1) else p) for p in par]
    D2 = F.bfs_all(par2, B - 2, alive2)
    pre, post, dC = D.get(P, INF), D2.get(P & ~C, INF), D.get(C, INF)
    lp = psi_ab([L - 1, 1], B, a, b)
    lq = psi_ab([1], B - 2, a, b)
    tgt = psi_ab([L, 1], B, a, b)
    ok = 1 + lp + lq >= tgt
    opt = (1 + pre + post == dC)
    print(f"L={L} B={B} (a,b)=({a},{b}): d(∅,P)={pre} post={post} d(∅,C)={dC} 分解が最適={opt} | "
          f"Ψ(P)={lp} Ψ(post)={lq} Ψ(C)={tgt} INEQ={'成立' if ok else '破れ'}")
    return ok, pre < INF and post < INF


if __name__ == "__main__":
    for (L, B, a, b) in [(4, 3, 1, 0), (8, 4, 1, 0), (16, 6, 2, 0), (16, 6, 2, 1), (20, 6, 3, 0)]:
        check(L, B, a, b)
