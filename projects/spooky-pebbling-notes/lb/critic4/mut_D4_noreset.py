#!/usr/bin/env python3
"""補題 E1 の無作為検定: 合法な手を無作為に選ぶ歩き（QL 規則．ghost は子が揃っていても打てる）で，全時刻で E(c) >= E(親) か．"""
import random
import sys


def walk(h, cap, steps, rng):
    n = 2 ** h - 1
    st = [0] * n
    anc = []
    for v in range(n):
        a, x = [], v
        while True:
            a.append(x)
            if x == 0:
                break
            x = (x - 1) // 2
        anc.append(a)
    cnt = [0] * n
    emptied = [True] * n
    E = [0] * n
    for _ in range(steps):
        np_ = sum(1 for x in st if x == 1)
        moves = []
        for v in range(n):
            ready = 2 * v + 1 >= n or (st[2 * v + 1] == 1 and st[2 * v + 2] == 1)
            if st[v] == 0 and ready and np_ < cap:
                moves.append((v, 1))
            elif st[v] == 1:
                if ready:
                    moves.append((v, 0))
                moves.append((v, 2))
            elif st[v] == 2 and ready and np_ < cap:
                moves.append((v, 1))
        v, new = rng.choice(moves)
        old = st[v]
        if new == 1:
            if emptied[v]:
                E[v] += 1
        st[v] = new
        d = (new == 1) - (old == 1)
        for a in anc[v]:
            cnt[a] += d
            if cnt[a] == 0:
                emptied[a] = True
        for c in range(1, n):
            if E[c] < E[(c - 1) // 2]:
                return False
    return True


rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
tot = bad = 0
for h in (3, 4, 5):
    for cap in range(h + 1, 2 ** h):
        for _ in range(40):
            tot += 1
            bad += not walk(h, cap, 3000, rng)
print(f"歩き {tot} 本（各 3000 手）: 補題 E1 の違反 {bad}")
