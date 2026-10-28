"""2CM(a,b) の反例の列を，丸めなしの正確な整数で幅優先に探す（closure.c とは独立に書いた）。
状態 = (D2, DM) を D2 の最小で正規化したもの（丸めなし）。作用 = 予算 B の相（その中では盤の大きさ <= B），
続けて境目を入れるか（2 本: A の頂と B の頂がある盤だけ残す / 1 本: A の頂がある盤だけ残す）。"""
import sys
from collections import deque
INF = float('inf')
a, b = int(sys.argv[1]), int(sys.argv[2])
L = a + b; N = 1 << L
def needs(two):
    nd = []
    for i in range(L):
        if two:
            if i < a: nd.append(1 << (i+1) if i+1 < a else 0)
            else: nd.append(1 << (i+1) if i+1 < L else 0)
        else:
            nd.append(1 << (i+1) if i+1 < L else 0)
    return nd
need2, needM = needs(True), needs(False)
tops2, topM = 1 | (1 << a), 1
pc = [bin(x).count('1') for x in range(N)]
def apply(D, need, B, chk, mask):
    E = [D[x] if pc[x] <= B else INF for x in range(N)]
    # 重み 1 の最短路（Bellman-Ford 的に不動点まで）
    changed = True
    while changed:
        changed = False
        for x in range(N):
            if E[x] == INF: continue
            for v in range(L):
                if x & need[v] != need[v]: continue
                y = x ^ (1 << v)
                if pc[y] > B: continue
                if E[x] + 1 < E[y]: E[y] = E[x] + 1; changed = True
    if chk:
        E = [E[x] if x & mask == mask else INF for x in range(N)]
    return E
s0 = (tuple([0] + [INF]*(N-1)), tuple([0] + [INF]*(N-1)))
seen = {s0: None}
q = deque([(s0, 0)])
while q:
    (D2, DM), off = q.popleft()
    for B in range(L+1):
        for chk in (0, 1):
            E2 = apply(D2, need2, B, chk, tops2)
            m = min(E2)
            if m == INF: continue
            EM = apply(DM, needM, B, chk, topM)
            if E2[0] != INF and EM[0] - E2[0] > 0:
                seq = [(B, chk)]
                st = (D2, DM)
                while seen[st] is not None:
                    st, act = seen[st]
                    seq.append(act)
                seq.reverse()
                print("violation gap", EM[0] - E2[0], "OPT_two", E2[0] + off, "OPT_one", EM[0] + off)
                print("sequence (budget, boundary-after):", seq)
                sys.exit(0)
            ns = (tuple(x - m for x in E2), tuple(x - m for x in EM))
            if ns not in seen:
                seen[ns] = ((D2, DM), (B, chk))
                q.append((ns, off + m))
    if len(seen) > 200000: print("no violation up to", len(seen)); break
print("done, states", len(seen))
