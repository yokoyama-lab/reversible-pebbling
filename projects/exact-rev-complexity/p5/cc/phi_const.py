"""φ の候補（すべての予算の歩みで R'(Y) ≤ R(X)，phi_*.txt）が，一定の予算だけで比べた候補と一致するかを見る。"""
import sys, re
from collections import deque
a, b = int(sys.argv[1]), int(sys.argv[2]); L = a + b; N = 1 << L
need2 = [(1 << (i+1) if i+1 < a else 0) if i < a else (1 << (i+1) if i+1 < L else 0) for i in range(L)]
needM = [1 << (i+1) if i+1 < L else 0 for i in range(L)]
pc = [bin(x).count('1') for x in range(N)]
def bfs(need, B):
    d = [None] * N; d[0] = 0; q = deque([0])
    while q:
        x = q.popleft()
        for v in range(L):
            if x & need[v] != need[v]: continue
            y = x ^ (1 << v)
            if pc[y] > B or d[y] is not None: continue
            d[y] = d[x] + 1; q.append(y)
    return d
R2 = {B: bfs(need2, B) for B in range(L + 1)}; RM = {B: bfs(needM, B) for B in range(L + 1)}
def bits(x, n0, n): return "".join("1" if x >> i & 1 else "." for i in range(n0, n))
true = {}
for ln in open(sys.argv[3] if len(sys.argv) > 3 else f"phi/phi_{a}_{b}.txt"):
    m = re.match(r'\s*A=(\S+) B=(\S+) -> (.*)', ln)
    if m: true[(m.group(1), m.group(2))] = set(m.group(3).split())
same = diff = 0
for x in range(N):
    if not (x & 1 and x >> a & 1): continue
    cand = set()
    for y in range(N):
        if not y & 1 or pc[y] > pc[x]: continue
        if all(R2[B][x] is None or (RM[B][y] is not None and RM[B][y] <= R2[B][x]) for B in range(L + 1)):
            cand.add(bits(y, 0, L))
    t = true[(bits(x, 0, a), bits(x, a, L))]
    if cand == t: same += 1
    else:
        diff += 1
        if diff <= 6: print("  X A=" + bits(x, 0, a), "B=" + bits(x, a, L), "const-only extra:", sorted(cand - t), "missing:", sorted(t - cand))
print(f"a={a} b={b}: same {same}, differ {diff}")
