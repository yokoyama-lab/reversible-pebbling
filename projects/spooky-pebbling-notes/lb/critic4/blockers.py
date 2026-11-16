import sys
from collections import Counter, defaultdict
sys.path.insert(0, '<local>/dev/notes/spooky-pebbling/lb/critic3')
sys.path.insert(0, '.')
from common import load, replay_ql
from pervertex import epis
def run(path, h, cap):
    mv = load(path); S, _ = replay_ql(mv, h, cap); n = 2**h-1; states = [tuple([0]*n)] + S
    E, P, eps = epis(mv, n)
    place = {v: [] for v in range(n)}
    for t, (op, x) in enumerate(mv, start=1):
        if op in ('pebble', 'unghost'): place[x].append(t)
    sub = {}
    for v in range(n):
        out, q = [], [v]
        while q:
            x = q.pop(); out.append(x)
            if 2*x+1 < n: q += [2*x+1, 2*x+2]
        sub[v] = out
    hg = lambda v: h - ((v+1).bit_length()-1)
    free = lambda y, t: all(states[t][x] != 1 for x in sub[y])
    def below2(x):
        return [z for c in (2*x+1, 2*x+2) if c < n for g in (2*c+1, 2*c+2) if g < n for z in sub[g]]
    seen = set(); byh = defaultdict(Counter)
    def explore(x, tau):
        if (x, tau) in seen: return
        seen.add((x, tau))
        if hg(x) >= 3:
            byh[hg(x)][sum(1 for y in below2(x) if states[tau][y] == 1)] += 1
        for y in below2(x):
            if free(y, tau):
                explore(y, next(t for t in place[y] if t > tau))
    explore(0, eps[0][-1])
    print(path.split('/')[-1], {k: dict(sorted(v.items())) for k, v in sorted(byh.items(), reverse=True)}, " (高さ: {妨害数: 切断の数})")
W = '<local>/dev/overleaf/2026-WiNF/code/results_P2_h6_witness333.txt'; L = '<local>/dev/notes/spooky-pebbling/lb/'
run(L+'opt_h4p5.txt', 4, 5); run(L+'opt_h5p6.txt', 5, 6); run(W, 6, 7)
