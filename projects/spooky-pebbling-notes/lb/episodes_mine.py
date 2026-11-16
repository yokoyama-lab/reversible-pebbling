#!/usr/bin/env python3
"""補題 E1（E(c) >= E(親)）と，置く手 >= n + Σ X'(a)|T(a)| の検算（批判者の kprime.py とは独立に書いた）．
使い方: python3 episodes_mine.py <手順> <h> ...   手順は "op v" 行（ヒープ順 0 始まり，# 行と T= 行は無視）
"""
import sys


def check(path, h):
    mv = [ln.split() for ln in open(path) if ln.strip() and not ln.startswith(("#", "T="))]
    n = 2 ** h - 1
    sub = []
    for v in range(n):
        s, q = [], [v]
        while q:
            x = q.pop()
            s.append(x)
            if 2 * x + 1 < n:
                q += [2 * x + 1, 2 * x + 2]
        sub.append(s)
    st = [0] * n
    cnt = [0] * n                       # 部分木内のペブル数
    anc = [[] for _ in range(n)]
    for v in range(n):
        x = v
        while True:
            anc[v].append(x)
            if x == 0:
                break
            x = (x - 1) // 2
    emptied = [True] * n                # 直前の置く手以後に部分木が空になったか（始状態は空）
    E = [0] * n
    places = 0
    for op, v in mv:
        v = int(v)
        new = 1 if op in ("pebble", "unghost") else (2 if op == "ghost" else 0)
        old = st[v]
        if new == 1:
            places += 1
            if emptied[v]:
                E[v] += 1
            emptied[v] = False
        st[v] = new
        d = (new == 1) - (old == 1)
        for a in anc[v]:
            cnt[a] += d
            if cnt[a] == 0:
                emptied[a] = True
    bad = [(c, (c - 1) // 2) for c in range(1, n) if E[c] < E[(c - 1) // 2]]
    Xp = {a: E[a] - E[(a - 1) // 2] for a in range(1, n)}
    lb = n + sum(Xp[a] * len(sub[a]) for a in range(1, n))
    ident = sum(E) == E[0] * n + sum(Xp[a] * len(sub[a]) for a in range(1, n))
    print(f"{path.split('/')[-1]} h={h}: 手数 {len(mv)} 置く手 {places} ΣE {sum(E)} E(根) {E[0]} "
          f"n+ΣX'|T| {lb}  補題 E1 の違反 {len(bad)}  恒等式 {ident}")


for i in range(1, len(sys.argv), 2):
    check(sys.argv[i], int(sys.argv[i + 1]))
