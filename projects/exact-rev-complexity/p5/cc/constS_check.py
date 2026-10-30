"""予算一定 S での到達手数 R_S(X)（森の盤 X，各鎖の頂上に石）と，区間の分解式
   min_{各鎖の下から積む順の併合} Σ_j Fc(長さ_j, S - (j-1)) の比較。"""
import itertools
from collections import deque
from functools import lru_cache
def bfs(lens, S):
    L = sum(lens); st = [sum(lens[:i]) for i in range(len(lens))]
    need = [0] * L
    for i, n in enumerate(lens):
        for j in range(n):
            v = st[i] + j
            need[v] = 1 << (v + 1) if j + 1 < n else 0
    D = {0: 0}; q = deque([0])
    while q:
        x = q.popleft()
        for v in range(L):
            if x & need[v] != need[v]: continue
            y = x ^ (1 << v)
            if bin(y).count('1') > S or y in D: continue
            D[y] = D[x] + 1; q.append(y)
    return D, st
INF = 10**9
@lru_cache(None)
def Fc(n, S):
    D, _ = bfs((n,), S)
    return D.get(1, INF)
def segs(x, s0, n):
    ps = [j for j in range(n) if x >> (s0 + j) & 1]
    return [q - p for p, q in zip(ps, ps[1:] + [n])]
def formula(chs, S):
    # chs: 各鎖の区間（上から）．積む順は各鎖で下から．併合の全列挙
    best = INF
    stacks = [list(reversed(c)) for c in chs]
    def rec(idx, j, acc):
        nonlocal best
        if acc >= best: return
        if all(idx[i] == len(stacks[i]) for i in range(len(stacks))):
            best = acc; return
        for i in range(len(stacks)):
            if idx[i] < len(stacks[i]):
                f = Fc(stacks[i][idx[i]], S - j)
                if f >= INF: continue
                idx[i] += 1; rec(idx, j + 1, acc + f); idx[i] -= 1
    rec([0] * len(stacks), 0, 0)
    return best
bad = tot = 0
for lens in [(4,), (5,), (6,), (7,), (8,), (2, 3), (2, 4), (3, 3), (2, 5), (3, 4), (3, 5), (4, 4), (2, 2, 2), (1, 2, 3), (2, 2, 3), (3, 3, 2)]:
    L = sum(lens)
    for S in range(1, L + 1):
        D, st = bfs(lens, S)
        for x, d in D.items():
            if any(not (x >> s & 1) for s in st): continue
            chs = [segs(x, st[i], n) for i, n in enumerate(lens)]
            f = formula(chs, S)
            tot += 1
            if f != d:
                bad += 1
                if bad <= 10: print('mismatch', lens, S, chs, 'bfs', d, 'formula', f)
        # 到達不能の側も: 式が有限なのに BFS で届かない例
        for x in range(1 << L):
            if x in D or any(not (x >> s & 1) for s in st) or bin(x).count('1') > S: continue
            chs = [segs(x, st[i], n) for i, n in enumerate(lens)]
            if formula(chs, S) < INF:
                bad += 1; print('formula finite but unreachable', lens, S, chs)
print('checked', tot, 'mismatch', bad)
