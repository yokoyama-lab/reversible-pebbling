"""#path 区切りの手順群で (1) 合法性 (2) 補題 E1 (3) 連鎖の下界 E(z) >= E(根) + m(z) を検査．
連鎖は最終窓（根の最後のエピソード p）から始める．"""
import sys
sys.path.insert(0, '<local>/dev/notes/spooky-pebbling/lb/critic3')
sys.path.insert(0, '/work/tmp/claude-1000/-work-a-dev-overleaf-2026-WiNF/df8de717-8908-461f-b0bb-c6851f9ddf33/scratchpad/critic4')
from common import replay_ql
from pervertex import epis

def chain_check(mv, h, cap):
    S, _ = replay_ql(mv, h, cap); n = 2**h - 1
    states = [tuple([0]*n)] + S
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
    free = lambda y, t: all(states[t][x] != 1 for x in sub[y])
    def below2(x):
        out = []
        for c in (2*x+1, 2*x+2):
            if c < n:
                for g in (2*c+1, 2*c+2):
                    if g < n: out += sub[g]
        return out
    p = eps[0][-1]
    m = [0]*n; best = {}; maxb = [0]
    def explore(x, tau, cnt):
        maxb[0] = max(maxb[0], sum(1 for y in below2(x) if states[tau][y] == 1))
        for y in below2(x):
            if free(y, tau):
                t2 = next(t for t in place[y] if t > tau)
                for z in sub[y]: m[z] = max(m[z], cnt+1)
                if best.get((y, t2), -1) < cnt+1:
                    best[(y, t2)] = cnt+1; explore(y, t2, cnt+1)
    explore(0, p, 0)
    e1bad = sum(1 for c in range(1, n) if E[c] < E[(c-1)//2])
    chbad = sum(1 for z in range(n) if E[z] < E[0] + m[z])
    return e1bad, chbad, sum(E), sum(1+x for x in m), maxb[0], E[0], len(mv)

def paths(fn):
    out = []; cur = None
    for ln in open(fn):
        if ln.startswith('#path'): cur = []; out.append(cur)
        elif ln.strip() and not ln.startswith('#'):
            op, v = ln.split(); cur.append((op, int(v)))
    return out

if __name__ == "__main__":
 for fn, h, cap in [(sys.argv[i], int(sys.argv[i+1]), int(sys.argv[i+2])) for i in range(1, len(sys.argv), 3)]:
     ps = paths(fn); agg = [0, 0]; minratio = 9; maxroot = 0; lens = set(); maxb = 0
     for mv in ps:
         a, b, se, sm, mb, er, L = chain_check(mv, h, cap)
         agg[0] += a > 0; agg[1] += b > 0; minratio = min(minratio, sm/se); maxroot = max(maxroot, er); lens.add(L); maxb = max(maxb, mb)
     print(f"{fn}: {len(ps)} 本 手数{sorted(lens)[:3]} E1違反の本数 {agg[0]} 連鎖下界の違反の本数 {agg[1]}  min Σ(1+m)/ΣE {minratio:.2f}  E(根)最大 {maxroot}  切断の妨害最大 {maxb} (cap-3={cap-3})")
