"""最短手順の標本（#path 区切り）それぞれで，主張 K の成立数・要求数・子を最適化した頂点ごとの最大マッチングを数える．"""
import sys
from collections import Counter
from functools import lru_cache
from common import replay_ql, kids, subtree

def empty_at(S, T, t):
    return t < 0 or all(S[t][x] != 1 for x in T)

def analyze(mv, h, cap):
    n = 2 ** h - 1
    S, _ = replay_ql(mv, h, cap)
    place = {v: [] for v in range(n)}; rem = {v: [] for v in range(n)}
    for t, (op, v) in enumerate(mv):
        (place if op in ('pebble', 'unghost') else rem)[v].append(t)
    win = {}
    for u in range(1, n):
        if 2 * u + 1 >= n: continue
        t0, f = place[u][0], rem[u][-1]
        for c in kids(u, n):
            T = subtree(c, n)
            cand = [t for t in range(t0 + 1, f) if empty_at(S, T, t)]
            if cand: win[(u, c)] = (min(cand), f)
    has = {u for (u, c) in win}
    total = sum(len(subtree(kids(u, n)[0], n)) for u in has)
    def vm(v, ws):
        used = set(); g = 0
        for lo, hi in sorted(ws, key=lambda w: (w[1], w[0])):
            cand = [t for t in place[v] if lo < t < hi and t not in used]
            if cand: used.add(min(cand)); g += 1
        return g
    @lru_cache(None)
    def best(x, A):
        own = vm(x, [win[a] for a in A]); ks = kids(x, n)
        if not ks: return own
        if x in has:
            return max(own + sum(best(k, A | frozenset([(x, c)]) if k == c else A) for k in ks) for c in ks if (x, c) in win)
        return own + sum(best(k, A) for k in ks)
    got = best(0, frozenset())
    # 左優先
    left = {}
    for (u, c) in sorted(win):
        left.setdefault(u, c)
    byv = {}
    for u, c in left.items():
        for v in subtree(c, n): byv.setdefault(v, []).append(win[(u, c)])
    gl = sum(vm(v, ws) for v, ws in byv.items())
    return len(has), total, got, gl

h, cap = int(sys.argv[2]), int(sys.argv[3])
paths = []; cur = None
for ln in open(sys.argv[1]):
    if ln.startswith('#path'):
        cur = []; paths.append(cur)
    elif ln.strip():
        op, v = ln.split(); cur.append((op, int(v)))
stat = Counter(); fails = []
seen = set()
for i, mv in enumerate(paths):
    key = tuple(mv)
    if key in seen: continue
    seen.add(key)
    k, tot, got, gl = analyze(mv, h, cap)
    stat[(k, tot, got, gl)] += 1
    if got < tot: fails.append(i)
print(f"相異な最短手順 {len(seen)} 本（標本 {len(paths)}）")
for (k, tot, got, gl), c in sorted(stat.items()):
    print(f"  事象のある u {k}，要求 {tot}，子最適化の最大 {got}，左優先 {gl}: {c} 本")
print("子を最適化しても満たせない手順の番号（先頭 10）:", fails[:10])
