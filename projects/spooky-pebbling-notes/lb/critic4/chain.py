"""提案する「切断の連鎖」下界の検算: E(z) >= 1 + m(z)（m = 連鎖の長さの最大）を実手順で確かめる．
連鎖: x_0 = 根（切断時刻 τ_0 = 最終窓の根のエピソード），x_i は x_{i-1} の深さ 2 以上下の頂点で T(x_i) が τ_{i-1} にペブルなし，
τ_i = τ_{i-1} より後の最初の x_i の置く手．状態 states[t] = 手 t（1 始まり）の直後．"""
import sys
sys.path.insert(0, '/work/tmp/claude-1000/-work-a-dev-overleaf-2026-WiNF/df8de717-8908-461f-b0bb-c6851f9ddf33/scratchpad/critic4')
sys.path.insert(0, '<local>/dev/notes/spooky-pebbling/lb/critic3')
from common import load, replay_ql
from pervertex import epis

def run(path, h, cap):
    mv = load(path); S, _ = replay_ql(mv, h, cap); n = 2**h - 1
    states = [tuple([0]*n)] + S
    E, P, eps = epis(mv, n)
    assert E[0] == 1
    place = {v: [t for t, (op, x) in enumerate(mv, start=1) if x == v and op in ('pebble', 'unghost')] for v in range(n)}
    sub = {}
    for v in range(n):
        out, q = [], [v]
        while q:
            x = q.pop(); out.append(x)
            if 2*x+1 < n: q += [2*x+1, 2*x+2]
        sub[v] = out
    def free(y, t): return all(states[t][x] != 1 for x in sub[y])
    def below2(x):  # 深さ 2 以上下
        out = []
        for c in (2*x+1, 2*x+2):
            if c < n:
                for g in (2*c+1, 2*c+2):
                    if g < n: out += sub[g]
        return out
    p = place[0][0]
    m = [0]*n; best = {}
    blockers = []
    def explore(x, tau, cnt):
        nb = sum(1 for y in below2(x) if states[tau][y] == 1)
        blockers.append(nb)
        for y in below2(x):
            if free(y, tau):
                nxt = [t for t in place[y] if t > tau]
                if not nxt: raise AssertionError(('no replacement', y, tau))
                t2 = nxt[0]
                for z in sub[y]: m[z] = max(m[z], cnt+1)
                if best.get((y, t2), -1) < cnt+1:
                    best[(y, t2)] = cnt+1
                    explore(y, t2, cnt+1)
    explore(0, p, 0)
    bad = [z for z in range(n) if E[z] < 1 + m[z]]
    print(f"{path.split('/')[-1]}: ΣE={sum(E)}  Σ(1+m)={sum(1+x for x in m)}  n={n}  E<1+m の頂点 {len(bad)}  "
          f"葉の m の平均 {sum(m[(n-1)//2:])/((n+1)//2):.2f}  切断時の深さ2以上下のペブル数の最大 {max(blockers)} (h-2={h-2})")
W = '<local>/dev/overleaf/2026-WiNF/code/results_P2_h6_witness333.txt'; L = '<local>/dev/notes/spooky-pebbling/lb/'
for a in [(L+'opt_h4p5.txt', 4, 5), (L+'opt_h5p6.txt', 5, 6), (W, 6, 7), (L+'critic3/flat_h6.txt', 6, 63)]:
    run(*a)
