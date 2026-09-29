"""最短手順の標本（#path 区切り）と単独ファイルで，高さ別の X' の重み w_k = Σ_{高さ k} X'(a)(2^k-1) と，
「子か孫に X'>=1 がある u」の割合を集計．"""
import sys
from collections import Counter
from common import replay_ql, kids, subtree

def empty_at(S, T, t):
    return t < 0 or all(S[t][x] != 1 for x in T)

def analyze(mv, h, cap):
    n = 2 ** h - 1
    S, _ = replay_ql(mv, h, cap)
    place = {v: [] for v in range(n)}
    for t, (op, v) in enumerate(mv):
        if op in ('pebble', 'unghost'):
            place[v].append(t)
    ep = {}
    for v in range(n):
        T = subtree(v, n); out = []; prev = -1
        for s in place[v]:
            emp = [t for t in range(prev, s) if empty_at(S, T, t)]
            if emp:
                out.append((max(emp), s))
            prev = s
        ep[v] = out
    X = {a: sum(1 for (b, s) in ep[a] if not any(bp <= b and s < sp for (bp, sp) in ep[(a - 1) // 2])) for a in range(1, n)}
    hg = lambda v: h - ((v + 1).bit_length() - 1)
    w = tuple(sum(X[a] * (2 ** k - 1) for a in X if hg(a) == k) for k in range(1, h))
    cg = []
    for u in range(1, n):
        if hg(u) < 3: continue
        desc = list(kids(u, n)) + [g for c in kids(u, n) for g in kids(c, n)]
        cg.append(any(X[a] >= 1 for a in desc))
    npl = sum(len(p) for p in place.values())
    return w, sum(cg), len(cg), npl

h, cap = int(sys.argv[2]), int(sys.argv[3])
paths = []; cur = None
for ln in open(sys.argv[1]):
    if ln.startswith('#path'):
        cur = []; paths.append(cur)
    elif ln.strip() and not ln.startswith('#') and not ln.startswith('T='):
        if cur is None:
            cur = []; paths.append(cur)
        op, v = ln.split(); cur.append((op, int(v)))
c = Counter()
for mv in paths:
    c[analyze(mv, h, cap)] += 1
print(f"{sys.argv[1].split('/')[-1]}: 手順 {len(paths)} 本")
for (w, a, b, npl), k in sorted(c.items(), key=lambda x: -x[1])[:12]:
    print(f"  高さ 1..{h-1} の X' 重み {w}（和 {sum(w)}，置く手 {npl}），子か孫に X'>=1 の u {a}/{b}: {k} 本")
