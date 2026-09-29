import numpy as np, random, sys
from sim import analyze
h,p=4,5; n=15
d=np.fromfile('dist_h4p5.bin',dtype=np.int16)
pw=[3**i for i in range(n)]
def moves(s):
    dig=[(s//pw[i])%3 for i in range(n)]; cnt=dig.count(1); out=[]
    for v in range(n):
        cs=all(dig[c]==1 for c in (2*v+1,2*v+2) if c<n)
        if dig[v]==0 and cs and cnt+1<=p: out.append(('pebble',v,s+pw[v]))
        if dig[v]==1 and cs: out.append(('unpebble',v,s-pw[v]))
        if dig[v]==1: out.append(('ghost',v,s+pw[v]))
        if dig[v]==2 and cs and cnt+1<=p: out.append(('unghost',v,s-pw[v]))
    return out
def walk(D,bias):
    s=0; seq=[]; budget=D
    while d[s]!=0:
        ms=[m for m in moves(s) if d[m[2]]>=0]
        down=[m for m in ms if d[m[2]]<d[s]]
        other=[m for m in ms if d[m[2]]>=d[s]]
        if budget>0 and other and random.random()<bias:
            m=random.choice(other); budget-=1
        else: m=random.choice(down)
        seq.append((m[0],m[1])); s=m[2]
    return seq
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
best=None; hist={}
for it in range(int(sys.argv[2]) if len(sys.argv)>2 else 3000):
    D=random.choice([0,0,5,20,60,200]); bias=random.choice([0.1,0.3,0.6,0.9])
    seq=walk(D,bias)
    T,E,out=analyze(h,p,seq,verbose=False)
    sm=min(o[1] for o in out)
    hist[sm]=hist.get(sm,0)+1
    if best is None or sm<best[0]: best=(sm,T,seq)
print("min sum m",best[0],"T",best[1]); print(sorted(hist.items())[:10])
open('best_h4.txt','w').write('\n'.join(f'{a} {b}' for a,b in best[2]))
