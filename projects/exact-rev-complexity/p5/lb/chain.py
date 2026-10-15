#!/usr/bin/env python3
"""鎖の Knill の再帰 F_c(n,S) を 3 通りに計算する（標準ライブラリだけ）.

定義（arXiv:2609.15062 の式 (1)．Knill 1995）:
    F_c(1,S) = 1 (S>=1),  F_c(n,0) = inf (n>=1),
    F_c(n,S) = min_{1<=m<n} F_c(m,S) + F_c(m,S-1) + F_c(n-m,S-1)   (n>=2).
F_c(n,S) < inf  <=>  n <= 2^(S-1).

3 通り:
  Fc_dp(n,S)     … 上の再帰をそのまま（n が小さいとき）
  chain_bfs(n,S) … 鎖のゲームの全数探索（Knill の定理の数値確認．再帰とは独立）
  Row(S)         … 行の併合 row(S) = {1} ∪ row(S-1) ∪ {δ(i,S)+δ(i,S-1)}（同論文の式 (3)）を
                   (値, 個数) の連長圧縮で持ち，F_c(n,S) = 1 + 2·(row(S) の小さい方から n-1 個の和)
                   で大きな n を計算する．
"""

from __future__ import annotations

import functools
from collections import deque

INF = float("inf")


@functools.lru_cache(maxsize=None)
def Fc_dp(n: int, S: int):
    if n == 0:
        return 0
    if S <= 0:
        return INF
    if n == 1:
        return 1
    if n > 2 ** (S - 1):
        return INF
    best = INF
    for m in range(1, n):
        v = Fc_dp(m, S) + Fc_dp(m, S - 1) + Fc_dp(n - m, S - 1)
        if v < best:
            best = v
    return best


def chain_bfs(n: int, S: int):
    """鎖 1..n（セル i を動かすにはセル i-1 が要る．セル 1 は自由）の最短手数（空 → {n}）."""
    goal = 1 << (n - 1)
    dist = {0: 0}
    q = deque([0])
    while q:
        x = q.popleft()
        d = dist[x]
        if x == goal:
            return d
        pc = bin(x).count("1")
        for i in range(n):
            if i > 0 and not (x >> (i - 1)) & 1:
                continue
            y = x ^ (1 << i)
            if not (x >> i) & 1 and pc + 1 > S:
                continue
            if y not in dist:
                dist[y] = d + 1
                q.append(y)
    return INF


# ----------------------------------------------------------------------------
# 計数関数による行（大きな n 用）
# ----------------------------------------------------------------------------


class Row:
    """row(S) を計数関数 C_S(v) = #{n : δ(n,S) <= v}（v = 0..M_S）で持つ.

    row(S) = {1} ∪ row(S-1) ∪ {a_i + b_i}（a_i, b_i は row(S), row(S-1) の i 番目に小さい値，
    i = 1..|row(S-1)|．arXiv:2609.15062 の式 (3)）から，v >= 1 で
        C_S(v) = 1 + C_{S-1}(v) + max_{0<=τ<=v} min(C_S(τ), C_{S-1}(v-τ)).
    （a_i + b_i <= v ⟺ ある τ で a_i <= τ かつ b_i <= v-τ ⟺ i <= max_τ min(C_S(τ), C_{S-1}(v-τ))．）
    row(1) は空．
    """

    _cache: dict[int, list[int]] = {}

    @classmethod
    def get(cls, S: int) -> list[int]:
        if S in cls._cache:
            return cls._cache[S]
        if S <= 1:
            C = [0]
        else:
            P = cls.get(S - 1)
            top = 2 ** (S - 1) - 1
            C = [0]
            v = 0
            while C[-1] < top:
                v += 1
                Pv = P[v] if v < len(P) else P[-1]
                # max_τ min(C[τ], P[v-τ])，τ in [0, v-1]（τ=v は P[0]=0 で寄与なし）
                # C[τ] は非減少，P[v-τ] は非増加．min の最大を二分探索で探す
                def g(t):
                    k = v - t
                    return P[k] if k < len(P) else P[-1]
                best = 0
                lft, r = 0, v - 1
                while lft <= r:
                    mid = (lft + r) // 2
                    if C[mid] <= g(mid):
                        best = max(best, C[mid])
                        lft = mid + 1
                    else:
                        best = max(best, g(mid))
                        r = mid - 1
                C.append(1 + Pv + best)
            assert C[-1] == top, (S, C[-1], top)
        cls._cache[S] = C
        return C

    @classmethod
    def Fc(cls, n: int, S: int):
        """F_c(n,S) = 1 + 2·Σ_{v>=0} max(0, (n-1) - C_S(v))（行の小さい方から n-1 個の和の書き換え）."""
        if n == 0:
            return 0
        if S <= 0:
            return INF
        if n > 2 ** (S - 1):
            return INF
        N = n - 1
        C = cls.get(S)
        s = 0
        for c in C:
            if c >= N:
                break
            s += N - c
        return 1 + 2 * s


def pmin_chain(n: int) -> int:
    """F_c(n,S) が有限になる最小の S = ceil(log2 n) + 1（n>=1）."""
    return (n - 1).bit_length() + 1 if n >= 1 else 0
