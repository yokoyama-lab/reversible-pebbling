import sys
from collections import Counter
sys.path.insert(0, '<local>/dev/notes/spooky-pebbling/lb/critic3'); sys.path.insert(0, '.')
from common import replay_ql
from pervertex import epis
from chain_many import paths
for fn, h, cap in [(sys.argv[i], int(sys.argv[i+1]), int(sys.argv[i+2])) for i in range(1, len(sys.argv), 3)]:
    n = 2**h-1; c = Counter(); minpair = 10**9; worst = None
    for mv in paths(fn):
        replay_ql(mv, h, cap); E, P, eps = epis(mv, n)
        hg = lambda v: h - ((v+1).bit_length()-1)
        w = tuple(sum((E[a]-E[(a-1)//2])*(2**k-1) for a in range(1, n) if hg(a) == k) for k in range(1, h))
        c[w] += 1
        mp = min(w[i]+w[i+1] for i in range(len(w)-1))
        if mp < minpair: minpair, worst = mp, (w, len(mv))
    print(f"{fn}: 最小の連続2段和 {minpair}（0.75*2^(h-1)={0.75*2**(h-1)}） 例 {worst}  最頻 {c.most_common(3)}")
