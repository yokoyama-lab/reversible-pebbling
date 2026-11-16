#!/usr/bin/env python3
"""T_h（高さ h の完全二分木）で k 個のペブルを置いた盤の Aut(T_h) 軌道の数 f_h(k).

部分木の軌道は (根のビット, 子の軌道の非順序対) で決まるので
    f_h(k) = Σ_{b∈{0,1}} Σ_{a+c=k-b, a<=c} [a<c ? f_{h-1}(a) f_{h-1}(c) : f_{h-1}(a)(f_{h-1}(a)+1)/2]
BFS の状態数の上界（到達可能とは限らない）に使う。  python3 orbcount.py
"""
K = 12
f = {1: [1, 1] + [0] * (K - 1)}
for h in range(2, 10):
    g = f[h - 1]
    out = [0] * (K + 1)
    for b in (0, 1):
        for k in range(K + 1 - b):
            s = 0
            for a in range(k + 1):
                c = k - a
                if a < c:
                    s += g[a] * g[c]
                elif a == c:
                    s += g[a] * (g[a] + 1) // 2
            out[k + b] += s
    f[h] = out
for h in range(1, 10):
    print(h, f[h], "cum<=10:", sum(f[h][:11]), "cum<=11:", sum(f[h][:12]))
