"""予算の列と境目を与えて，2 本の鎖（A: 長さ a，B: 長さ b）と 1 本の鎖（A の下に B）の最短手数を，
(相の番号, 盤) を頂点とする 0-1 BFS で直接求める（witness.py と別に書いた。盤は頂点名の frozenset）。"""
import sys
from collections import deque
def solve(chains, seq, tops):
    # chains: 鎖のリスト（各鎖は上から下への頂点名の列）．頂点 v の子 = 同じ鎖で 1 つ下の頂点
    child = {}
    for ch in chains:
        for i, v in enumerate(ch):
            child[v] = ch[i+1] if i+1 < len(ch) else None
    V = list(child)
    start = (0, frozenset())
    dist = {start: 0}
    dq = deque([start])
    best = None
    while dq:
        j, X = dq.popleft()
        d = dist[(j, X)]
        B, bd = seq[j]
        if j == len(seq) - 1 and not X:
            best = d if best is None else min(best, d)
        # 相の中の 1 手
        for v in V:
            c = child[v]
            if c is not None and c not in X: continue
            Y = X ^ {v}
            if len(Y) > B: continue
            st = (j, frozenset(Y))
            if st not in dist or dist[st] > d + 1:
                dist[st] = d + 1; dq.append(st)
        # 次の相へ（手数 0）: 境目なら頂がすべて盤にある．次の相の予算に収まる
        if j + 1 < len(seq):
            if bd and not all(t in X for t in tops): continue
            if len(X) > seq[j+1][0]: continue
            st = (j + 1, X)
            if st not in dist or dist[st] > d:
                dist[st] = d; dq.appendleft(st)
    return best
a, b = 2, 5
A = [f"A{i}" for i in range(a)]; Bc = [f"B{i}" for i in range(b)]
seq = [(3, 1), (5, 0), (2, 1), (3, 0), (1, 0), (4, 0)]
two = solve([A, Bc], seq, ["A0", "B0"])
one = solve([A + Bc], seq, ["A0"])
print("OPT_two", two, "OPT_one", one)
