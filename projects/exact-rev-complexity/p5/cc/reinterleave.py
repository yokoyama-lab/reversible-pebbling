#!/usr/bin/env python3
"""仮説 H_RI（並べ替えだけで 2CM が出るか）を試す.

H_RI: 2 本の鎖の手順 σ（A の手の列 α と B の手の列 β を交互に混ぜたもの，相ごとの予算と境目つき）について，
α と β をそれぞれ同じ順に保ったまま混ぜ方と相への割り当てだけを変えて，1 本の鎖（A の下に B）の手順にできる．
（1 本の鎖では A の底の手に B の頂が要る．境目では A の頂だけが要る．）
H_RI が成り立てば 2CM が従う（手数は同じ）．格子 (i, j, 相) の上の到達可能性で判定する．

σ は twochain.c の walk と同じ作り方（無作為な境目の盤を最短路でつなぎ，1 手ごとに相を切り，予算はきつく）．
"""
from __future__ import annotations

import random
import sys
from collections import deque


def chain_need(a, b):
    need = [(1 << (i + 1)) if i + 1 < a else 0 for i in range(a)] + \
           [(1 << (a + i + 1)) if i + 1 < b else 0 for i in range(b)]
    return need


def bfs_path(need, L, x, y, B):
    if bin(x).count("1") > B or bin(y).count("1") > B:
        return None
    par = {x: None}
    q = deque([x])
    while q:
        z = q.popleft()
        if z == y:
            break
        pc = bin(z).count("1")
        for v in range(L):
            if z & need[v] != need[v]:
                continue
            if not (z >> v) & 1 and pc + 1 > B:
                continue
            w = z ^ (1 << v)
            if w not in par:
                par[w] = z
                q.append(w)
    if y not in par:
        return None
    path = []
    z = y
    while z != x:
        path.append(z)
        z = par[z]
    return path[::-1]


def make_sigma(rng, a, b, m):
    L = a + b
    need = chain_need(a, b)
    tops = 1 | (1 << a)
    seq = [0]
    chk_at = set()
    cur = 0
    for i in range(m + 1):
        if i < m:
            target = rng.randrange(1 << L) | tops
        else:
            target = 0
        B = max(bin(cur).count("1"), bin(target).count("1")) + rng.randrange(3)
        path = None
        while B <= L and path is None:
            path = bfs_path(need, L, cur, target, B)
            B += 1
        if path is None:
            return None
        seq += path
        if i < m:
            chk_at.add(len(seq) - 1)
        cur = target
    return seq, chk_at


def swap_ab(a, b, seq, chk_at):
    """2 本の名前を入れ替える（B を上にした併合を試すため）."""
    maskA = (1 << a) - 1
    return [((x >> a) | ((x & maskA) << b)) for x in seq], chk_at


def h_ri(a, b, seq, chk_at):
    """相 j は seq[j] -> seq[j+1]（1 手），予算 = 2 つの盤の大きさの最大．境目は chk_at の添字の盤の後."""
    J = len(seq) - 1
    bud = [max(bin(seq[j]).count("1"), bin(seq[j + 1]).count("1")) for j in range(J)]
    maskA = (1 << a) - 1
    # A の手の列と B の手の列（盤の列として）
    xa = [seq[0] & maskA]
    xb = [seq[0] >> a]
    for j in range(J):
        d = seq[j] ^ seq[j + 1]
        if d & maskA:
            xa.append(seq[j + 1] & maskA)
        else:
            xb.append(seq[j + 1] >> a)
    # 境目: seq の添字 k の盤（k = 1..J-1）の後に相 k-1 と k の境目
    chk = [False] * J
    for k in chk_at:
        if 1 <= k <= J - 1:
            chk[k - 1] = True
    nA, nB = len(xa) - 1, len(xb) - 1
    botA = 1 << (a - 1)

    def pc(i, j):
        return bin(xa[i]).count("1") + bin(xb[j]).count("1")

    start = (0, 0, 0)
    seen = {start}
    q = deque([start])
    while q:
        i, j, p = q.popleft()
        if i == nA and j == nB and p == J - 1:
            return True
        cand = []
        if i < nA:
            # A の手．A の底の手なら B の頂（xb[j] のビット 0）が要る
            moved = xa[i] ^ xa[i + 1]
            if moved != botA or (xb[j] & 1):
                if pc(i + 1, j) <= bud[p]:
                    cand.append((i + 1, j, p))
        if j < nB and pc(i, j + 1) <= bud[p]:
            cand.append((i, j + 1, p))
        if p < J - 1 and pc(i, j) <= bud[p + 1]:
            if not chk[p] or (xa[i] & 1):
                cand.append((i, j, p + 1))
        for s in cand:
            if s not in seen:
                seen.add(s)
                q.append(s)
    return False


def main(trials, maxL, m, seed):
    rng = random.Random(seed)
    fail = tot = 0
    either_ok = [0]
    nonopt = [0]
    for _ in range(trials):
        L = rng.randint(2, maxL)
        a = rng.randint(1, L - 1)
        b = L - a
        r = make_sigma(rng, a, b, rng.randint(1, m))
        if r is None:
            continue
        seq, chk_at = r
        tot += 1
        ok1 = h_ri(a, b, seq, chk_at)
        s2, c2 = swap_ab(a, b, seq, chk_at)
        ok2 = h_ri(b, a, s2, c2)
        if ok1 or ok2:
            either_ok[0] += 1
        if not (ok1 or ok2):
            fail += 1
            import twochain as TC
            J = len(seq) - 1
            bud = [max(bin(seq[j]).count("1"), bin(seq[j + 1]).count("1")) for j in range(J)]
            chk = [False] * (J - 1)
            for k in chk_at:
                if 1 <= k <= J - 1:
                    chk[k - 1] = True
            o2 = TC.opt("two", a, b, bud, chk)
            om = TC.opt("merged", a, b, bud, chk)
            nonopt[0] += (o2 < J)
            print(f"   |σ|={J} OPT_two={o2} OPT_merged={om} {'σ は最適でない' if o2 < J else 'σ は最適'}")
            if fail <= 30:
                print(f"H_RI 不成立: a={a} b={b} 手数={len(seq)-1} 境目={sorted(chk_at)}")
    print(f"試行 {tot}，どちらを上にしても並べ替えだけでは 1 本にできない σ {fail}（うち σ が最適でないもの {nonopt[0]}）")


if __name__ == "__main__":
    a = sys.argv[1:]
    main(int(a[0]) if a else 500, int(a[1]) if len(a) > 1 else 6, int(a[2]) if len(a) > 2 else 3, 1)
