"""修正案の検定: (a) 1 つの置く手を b 事象まで共有してよい場合の最小 b，(b) 事象ごとに |T(c)| 個の置く手（頂点を問わない）を要求する群版，
(c) 高さを L おきに間引いた版，(d) 高さ <=3 に限った版．いずれも窓は (τ_first, f)．"""
import sys
import random
from collections import deque
from common import kids, subtree
from events import prep, empty_at

def maxflow(N, edges, s, t):
    g = [[] for _ in range(N)]
    for a, b, c in edges:
        g[a].append([b, c, len(g[b])]); g[b].append([a, 0, len(g[a]) - 1])
    flow = 0
    while True:
        lvl = [-1] * N; lvl[s] = 0; q = deque([s])
        while q:
            x = q.popleft()
            for y, c, _ in g[x]:
                if c > 0 and lvl[y] < 0:
                    lvl[y] = lvl[x] + 1; q.append(y)
        if lvl[t] < 0:
            return flow
        it = [0] * N
        def dfs(x, f):
            if x == t:
                return f
            while it[x] < len(g[x]):
                e = g[x][it[x]]
                y, c, r = e
                if c > 0 and lvl[y] == lvl[x] + 1:
                    d = dfs(y, min(f, c))
                    if d:
                        e[1] -= d; g[y][r][1] += d
                        return d
                it[x] += 1
            return 0
        while True:
            f = dfs(s, 10**9)
            if not f:
                break
            flow += f

def setup(path, h, cap):
    mv, S, n, place, rem, remop = prep(path, h, cap)
    win = {}
    for u in range(1, n):
        if 2 * u + 1 >= n:
            continue
        t0, f = place[u][0], rem[u][-1]
        for c in kids(u, n):
            T = subtree(c, n)
            cand = [t for t in range(t0 + 1, f) if empty_at(S, T, t)]
            if cand:
                win[(u, c)] = (min(cand), f)
    return mv, n, place, win

def hgt(u, h):
    return h - ((u + 1).bit_length() - 1)

def per_vertex_flow(events, win, place, n, b=1, group=False):
    """events: list of (u,c)．per-vertex: 各 v∈T(c) に 1 つ．group: 事象ごとに |T(c)| 個（T(c) の任意の頂点の置く手）．
    置く手ノードの容量 b．戻り値: (満たせた数, 要求数)．"""
    pl = [(v, t) for v in range(n) for t in place[v]]
    pid = {p: i for i, p in enumerate(pl)}
    edges = []
    s = 0; base = 1
    if group:
        nd = len(events); t_ = base + nd + len(pl)
        tot = 0
        for i, (u, c) in enumerate(events):
            lo, hi = win[(u, c)]
            T = subtree(c, n); tot += len(T)
            edges.append((s, base + i, len(T)))
            for v in T:
                for t in place[v]:
                    if lo < t < hi:
                        edges.append((base + i, base + nd + pid[(v, t)], 1))
    else:
        dem = [(u, c, v) for (u, c) in events for v in subtree(c, n)]
        nd = len(dem); t_ = base + nd + len(pl); tot = nd
        for i, (u, c, v) in enumerate(dem):
            lo, hi = win[(u, c)]
            edges.append((s, base + i, 1))
            for t in place[v]:
                if lo < t < hi:
                    edges.append((base + i, base + nd + pid[(v, t)], 1))
    for j in range(len(pl)):
        edges.append((base + nd + j, t_, b))
    return maxflow(t_ + 1, edges, s, t_), tot

def main(path, h, cap):
    mv, n, place, win = setup(path, h, cap)
    U = sorted({u for (u, c) in win})
    left = [(u, min(c for (uu, c) in win if uu == u)) for u in U]
    name = path.split('/')[-1]
    for b in (1, 2):
        print(f"{name} (a) 置く手の共有を b={b} まで: {per_vertex_flow(left, win, place, n, b=b)}")
    print(f"{name} (b) 群版（左優先）: {per_vertex_flow(left, win, place, n, group=True)}")
    both = [(u, c) for (u, c) in win]
    print(f"{name} (b') 群版で両方の子の事象を全部要求: {per_vertex_flow(both, win, place, n, group=True)}")
    print(f"{name} (b'') 頂点ごと版で両方の子の事象を全部要求: {per_vertex_flow(both, win, place, n)}")
    # 群版の子の選択: 乱択 2000 通り + 左優先で最小値・最大値
    rng = random.Random(1)
    choices = {u: [c for (uu, c) in win if uu == u] for u in U}
    worst = best = None
    for _ in range(2000):
        ev = [(u, rng.choice(choices[u])) for u in U]
        got, tot = per_vertex_flow(ev, win, place, n, group=True)
        worst = got if worst is None else min(worst, got); best = got if best is None else max(best, got)
    print(f"{name} (b) 群版 子を乱択 2000 通り: 最小 {worst} 最大 {best} / {tot}")
    for L in (2, 3):
        for r in range(L):
            ev = [(u, c) for (u, c) in left if hgt(u, h) % L == r]
            if ev:
                print(f"{name} (c) 高さ ≡ {r} mod {L} の事象だけ（左優先）: {per_vertex_flow(ev, win, place, n)}")
    ev = [(u, c) for (u, c) in left if hgt(u, h) <= 3]
    print(f"{name} (d) 高さ <=3（左優先）: {per_vertex_flow(ev, win, place, n)}")

if __name__ == '__main__':
    for path, h, cap in [(sys.argv[i], int(sys.argv[i+1]), int(sys.argv[i+2])) for i in range(1, len(sys.argv), 3)]:
        main(path, h, cap)
