"""closure_real0 が出した列（開始の β と遷移 U/D/P）を，(相, 盤) の 0-1 BFS で厳密に評価する（丸めなし，別のコード）。"""
import sys
from collections import deque
def phases(beta0, moves):
    # 各遷移: (次の β, 盤の大きさの上限, 頂を要るか)
    seq = []; beta = beta0; u = 0
    for mv in moves:
        if mv == 'U': seq.append((beta + 1, beta, False)); beta += 1   # 上限は小さい方 = 今の β
        elif mv == 'D': seq.append((beta - 1, beta - 1, False)); beta -= 1
        else:
            if u == 0: seq.append((beta - 1, beta - 1, True)); beta -= 1; u = 1
            else: seq.append((beta + 1, beta, True)); beta += 1; u = 0
    return seq
def solve(chains, beta0, trans, tops):
    child = {}
    for ch in chains:
        for i, v in enumerate(ch): child[v] = ch[i + 1] if i + 1 < len(ch) else None
    V = list(child); T = len(trans)
    budget = [beta0] + [t[0] for t in trans]
    dist = {(0, frozenset()): 0}; dq = deque([(0, frozenset())]); best = None
    while dq:
        j, X = dq.popleft(); d = dist[(j, X)]
        if j == T and not X: best = d if best is None else min(best, d)
        for v in V:
            c = child[v]
            if c is not None and c not in X: continue
            Y = frozenset(X ^ {v})
            if len(Y) > budget[j]: continue
            if (j, Y) not in dist or dist[(j, Y)] > d + 1: dist[(j, Y)] = d + 1; dq.append((j, Y))
        if j < T:
            nb, lim, needtop = trans[j]
            if len(X) > lim: continue
            if needtop and not all(t in X for t in tops): continue
            if (j + 1, X) not in dist or dist[(j + 1, X)] > d: dist[(j + 1, X)] = d; dq.appendleft((j + 1, X))
    return best
a, b = 2, 5
beta0 = int(sys.argv[1]); moves = sys.argv[2].split()
A = [f"A{i}" for i in range(a)]; Bc = [f"B{i}" for i in range(b)]
tr = phases(beta0, moves)
print("budgets:", [beta0] + [t[0] for t in tr])
print("OPT_two", solve([A, Bc], beta0, tr, ["A0", "B0"]), "OPT_one", solve([A + Bc], beta0, tr, ["A0"]))
