import random, sys
from sim import analyze
sys.setrecursionlimit(100000)
EMPTY,PEB,GH=0,1,2
class Fail(Exception): pass
def gen(h,p,rng,cap=20000,pleave=0.3):
    n=2**h-1
    ch=lambda v:[c for c in (2*v+1,2*v+2) if c<n]
    st=[EMPTY]*n; seq=[]
    def cnt(): return sum(1 for x in st if x==PEB)
    def do(op,v):
        if len(seq)>cap: raise Fail
        cs=all(st[c]==PEB for c in ch(v))
        if op=='pebble': assert st[v]==EMPTY and cs; st[v]=PEB
        elif op=='unpebble': assert st[v]==PEB and cs; st[v]=EMPTY
        elif op=='ghost': assert st[v]==PEB; st[v]=GH
        elif op=='unghost': assert st[v]==GH and cs; st[v]=PEB
        assert cnt()<=p
        seq.append((op,v))
    def evict(pinned):
        cands=[u for u in range(n) if st[u]==PEB and u not in pinned]
        if not cands: raise Fail
        u=rng.choice(cands)
        if all(st[c]==PEB for c in ch(u)) and rng.random()<0.5: do('unpebble',u)
        else: do('ghost',u)
    def compute(v,pinned):
        if st[v]==PEB: return
        cs=ch(v); rng.shuffle(cs); pin=set(pinned)
        for c in cs:
            compute(c,pin|{v}); pin.add(c)
        while cnt()>=p: evict(pin|{v})
        do('pebble' if st[v]==EMPTY else 'unghost',v)
        # optional random cleanup of children
        for c in cs:
            if st[c]==PEB and c not in pinned and rng.random()>pleave:
                if all(st[g]==PEB for g in ch(c)) and rng.random()<0.5: do('unpebble',c)
                else: do('ghost',c)
    compute(0,set())
    while True:
        if st[0]!=PEB: compute(0,set())
        rest=[u for u in range(1,n) if st[u]!=EMPTY]
        if not rest: break
        dmin=min(u.bit_length() for u in [x+1 for x in rest])
        v=rng.choice([u for u in rest if (u+1).bit_length()==dmin])
        pinned={0}
        if st[v]==GH:
            for c in ch(v): compute(c,pinned|{v}); pinned.add(c)
            while cnt()>=p: evict(pinned|{v})
            do('unghost',v)
        for c in ch(v):
            compute(c,pinned|{v}); pinned.add(c)
        if st[v]==PEB and all(st[c]==PEB for c in ch(v)): do('unpebble',v)
    return seq
G={3:3,4:8,5:20,6:44}
h=int(sys.argv[1]); N=int(sys.argv[2]); rng=random.Random(int(sys.argv[3]))
p=h+1; best=None; ok=0; fail=0; hist={}; Tmin=None
for it in range(N):
    try: seq=gen(h,p,rng,pleave=rng.choice([0.0,0.2,0.5,0.8]))
    except Fail: fail+=1; continue
    T,E,out=analyze(h,p,seq,verbose=False); ok+=1
    sm=min(o[1] for o in out); hist[sm]=hist.get(sm,0)+1
    Tmin=T if Tmin is None else min(Tmin,T)
    if best is None or sm<best[0]: best=(sm,T)
    assert sm>=G[h], ("COUNTEREXAMPLE",sm)
print(f"h={h} ok={ok} fail={fail} min sum m={best} G={G[h]} Tmin={Tmin}")
print(sorted(hist.items())[:8])
