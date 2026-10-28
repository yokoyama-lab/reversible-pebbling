"""境目 1 つの 2CM の証明の形を探す: 予算の変わり方（±1 の歩み）によらない写像 φ（2 本の盤 X ∋ A0,B0 → 1 本の盤 Y ∋ A0，|Y| ≤ |X|）で，
到達の最短手数 R'(φ(X)) ≤ R(X) がすべての予算の歩みで成り立つものがあるか。到達しうる正規化した (D2, DM) を幅優先で集め，
各 X について条件を満たす Y の候補の共通部分を取る（丸めなし．状態数の上限まで）。"""
import sys
from collections import deque
INF = float('inf')
a, b = int(sys.argv[1]), int(sys.argv[2]); CAP = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
L = a + b; N = 1 << L; BMAX = L
pc = [bin(x).count('1') for x in range(N)]
need2 = [(1 << (i+1) if i+1 < a else 0) if i < a else (1 << (i+1) if i+1 < L else 0) for i in range(L)]
needM = [1 << (i+1) if i+1 < L else 0 for i in range(L)]
def relax(E, need, B):
    E = list(E); ch = True
    while ch:
        ch = False
        for x in range(N):
            if E[x] == INF: continue
            for v in range(L):
                if x & need[v] != need[v]: continue
                y = x ^ (1 << v)
                if pc[y] > B: continue
                if E[x] + 1 < E[y]: E[y] = E[x] + 1; ch = True
    return E
filt = lambda E, B: [E[x] if pc[x] <= B else INF for x in range(N)]
Xs = [x for x in range(N) if x & 1 and x >> a & 1]          # 2 本: A0 と B0
Ys = [y for y in range(N) if y & 1]                          # 1 本: A0
cand = {x: set(y for y in Ys if pc[y] <= pc[x]) for x in Xs}
seen = set(); q = deque()
for b0 in range(BMAX + 1):
    D = [0] + [INF] * (N - 1)
    st = (tuple(relax(D, need2, b0)), tuple(relax(D, needM, b0)), b0)
    seen.add(st); q.append(st)
while q and len(seen) < CAP:
    D2, DM, beta = q.popleft()
    for x in Xs:
        if D2[x] == INF: continue
        cand[x] = {y for y in cand[x] if DM[y] <= D2[x]}
    for nb in (beta - 1, beta + 1):
        if nb < 0 or nb > BMAX: continue
        lim = min(beta, nb)
        E2 = relax(filt(D2, lim), need2, nb); EM = relax(filt(DM, lim), needM, nb)
        m = min(E2)
        if m == INF: continue
        ns = (tuple(v - m for v in E2), tuple(v - m for v in EM), nb)
        if ns not in seen: seen.add(ns); q.append(ns)
def show(x, two=True):
    if two: return "{" + ",".join([f"A{i}" for i in range(a) if x >> i & 1] + [f"B{i}" for i in range(b) if x >> (a+i) & 1]) + "}"
    return "{" + ",".join(f"v{i}" for i in range(L) if x >> i & 1) + "}"
print(f"a={a} b={b}: states {len(seen)} ({'closed' if not q else 'CAP'})")
bad = [x for x in Xs if not cand[x]]
print("X with no valid Y:", [show(x) for x in bad])
def bits(x, n0, n): return "".join("1" if x >> i & 1 else "." for i in range(n0, n))
for x in Xs:
    ys = sorted(cand[x], key=lambda y: [-(y >> i & 1) for i in range(L)])
    print("  A=" + bits(x, 0, a) + " B=" + bits(x, a, L), "->", " ".join(bits(y, 0, L) for y in ys))
