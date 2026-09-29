"""一般化した連鎖: 切断 x（時刻 τ）の深さ 2 以上下の y は，[τ, f_親(y)) のどこかで T(y) がペブルなしなら連鎖の頂点になる．
次の切断 = そのペブルなし時刻 t の後の最初の y の置く手．E(z) >= E(根) + m(z) を検査し，切断ごとの「否認」数（最大の否認部分木の数）を数える．"""
import sys
from collections import Counter, defaultdict
sys.path.insert(0, '<local>/dev/notes/spooky-pebbling/lb/critic3'); sys.path.insert(0, '.')
from common import replay_ql, load
from pervertex import epis

def analyze(mv, h, cap, verbose=False):
    S, _ = replay_ql(mv, h, cap); n = 2**h-1; states = [tuple([0]*n)] + S
    E, P, eps = epis(mv, n)
    place = {v: [] for v in range(n)}; rem = {v: [] for v in range(n)}
    for t, (op, x) in enumerate(mv, start=1):
        (place if op in ('pebble', 'unghost') else rem)[x].append(t)
    f = {v: rem[v][-1] for v in range(1, n)}
    sub = {}
    for v in range(n):
        out, q = [], [v]
        while q:
            x = q.pop(); out.append(x)
            if 2*x+1 < n: q += [2*x+1, 2*x+2]
        sub[v] = out
    hg = lambda v: h - ((v+1).bit_length()-1)
    free = lambda y, t: all(states[t][x] != 1 for x in sub[y])
    m = [0]*n; best = {}; stats = defaultdict(Counter)
    def explore(x, tau, cnt):
        # 深さ 2 以上下を上から見て，最大の「一般化連鎖の頂点」を取る
        denied = 0; blocked = sum(1 for c in (2*x+1, 2*x+2) if c < n for g in (2*c+1, 2*c+2) if g < n for z in sub[g] if states[tau][z] == 1)
        stack = [g for c in (2*x+1, 2*x+2) if c < n for g in (2*c+1, 2*c+2) if g < n]
        while stack:
            y = stack.pop()
            end = f[(y-1)//2]
            ts = [t for t in range(tau, end) if free(y, t)]
            if ts:
                t0 = ts[0]
                t2 = next(t for t in place[y] if t > t0)
                for z in sub[y]: m[z] = max(m[z], cnt+1)
                if best.get((y, t2), -1) < cnt+1:
                    best[(y, t2)] = cnt+1; explore(y, t2, cnt+1)
            else:
                if 2*y+1 < n: stack += [2*y+1, 2*y+2]
                else: denied += 1
                # 葉まで否認されたものだけ数えるのは粗いので，最大否認部分木の数は別に数える
        if hg(x) >= 3: stats[hg(x)][(blocked)] += 1
    explore(0, eps[0][-1], 0)
    bad = sum(1 for z in range(n) if E[z] < E[0] + m[z])
    return bad, sum(E), sum(1+x for x in m), stats, m

if __name__ == '__main__':
    from chain_many import paths
    W = '<local>/dev/overleaf/2026-WiNF/code/results_P2_h6_witness333.txt'; L = '<local>/dev/notes/spooky-pebbling/lb/'
    for fn, h, cap in [(L+'opt_h4p5.txt', 4, 5), (L+'opt_h5p6.txt', 5, 6), (W, 6, 7)]:
        bad, se, sm, st, m = analyze(load(fn), h, cap)
        print(fn.split('/')[-1], "違反", bad, "ΣE", se, "Σ(1+m_gen)", sm, "葉の m 平均", round(sum(m[(2**h-1)//2:])/2**(h-1), 2))
    for fn, h, cap in [('paths_h4_c5_x0.txt', 4, 5), ('paths_h4_c5_x100.txt', 4, 5), ('paths_h4_c6_x60.txt', 4, 6), ('paths_h4_c8_x40.txt', 4, 8), ('paths_h3_c4_x30.txt', 3, 4)]:
        nb = 0; mr = 9; N = 0
        for mv in paths(fn):
            bad, se, sm, st, m = analyze(mv, h, cap); nb += bad > 0; mr = min(mr, sm/se); N += 1
        print(fn, N, "本 違反の本数", nb, "min Σ(1+m)/ΣE", round(mr, 2))
