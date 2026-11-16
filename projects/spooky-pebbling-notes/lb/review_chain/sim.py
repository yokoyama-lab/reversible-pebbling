import sys
from functools import lru_cache
EMPTY,PEB,GH=0,1,2
def parse(path):
    mv=[]
    for line in open(path):
        line=line.strip()
        if not line or line.startswith('#') or line.startswith('T='): continue
        op,v=line.split(); mv.append((op,int(v)))
    return mv
def analyze(h,p,moves,verbose=True):
    n=2**h-1
    ch=lambda v:[c for c in (2*v+1,2*v+2) if c<n]
    sub=[0]*n
    for v in range(n-1,-1,-1):
        sub[v]=1<<v
        for c in ch(v): sub[v]|=sub[c]
    depth=[0]*n
    for v in range(1,n): depth[v]=depth[(v-1)//2]+1
    st=[EMPTY]*n; peb=[0]  # peb masks S_0..S_T
    placements=[[] for _ in range(n)]
    lastrem=[None]*n
    for t,(op,v) in enumerate(moves,1):
        cs=all(st[c]==PEB for c in ch(v))
        if op=='pebble': assert st[v]==EMPTY and cs
        elif op=='unpebble': assert st[v]==PEB and cs
        elif op=='ghost': assert st[v]==PEB
        elif op=='unghost': assert st[v]==GH and cs
        else: raise
        st[v]={'pebble':PEB,'unpebble':EMPTY,'ghost':GH,'unghost':PEB}[op]
        if op in('pebble','unghost'): placements[v].append(t)
        else: lastrem[v]=(t,op)
        m=sum(1<<u for u in range(n) if st[u]==PEB)
        assert bin(m).count('1')<=p, (t,op,v)
        peb.append(m)
    T=len(moves)
    assert st[0]==PEB and all(st[u]==EMPTY for u in range(1,n)), "final"
    # lemma 3 check
    for v in range(1,n): assert lastrem[v][1]=='unpebble'
    # episodes
    epis=[[] for _ in range(n)]
    for v in range(n):
        prev=0
        for s in placements[v]:
            if prev==0 or any(peb[t]&sub[v]==0 for t in range(prev,s)):
                epis[v].append(s)
            prev=s
    E=[len(e) for e in epis]
    tot_place=sum(len(x) for x in placements)
    assert T==2*tot_place-1
    for v in range(1,n): assert E[v]>=E[(v-1)//2]
    def firstplace_after(y,tau):
        for s in placements[y]:
            if s>tau: return s
        return None
    memo={}
    def M(x,tau):
        key=(x,tau)
        if key in memo: return memo[key]
        res={}
        m=peb[tau]
        # y strictly >=2 below x, free
        stack=[c for c in ch(x)]
        cand=[]
        for c in ch(x):
            for g in ch(c): cand.append(g)
        while cand:
            y=cand.pop()
            if m&sub[y]==0:
                ty=firstplace_after(y,tau)
                assert ty is not None, ("lemmaC1 fail",x,tau,y)
                # lemma C(2) check
                for z in range(n):
                    if sub[y]>>z&1:
                        fz=firstplace_after(z,tau)
                        assert fz is not None and tau<fz<=ty, ("C2 window",x,tau,y,z)
                        assert fz in epis[z], ("C2 episode",x,tau,y,z)
                sub_res=M(y,ty)
                for z in range(n):
                    if sub[y]>>z&1:
                        val=1+sub_res.get(z,0)
                        if val>res.get(z,0): res[z]=val
            cand.extend(ch(y))
        memo[key]=res
        return res
    out=[]
    lastep=epis[0][-1]
    for tau0 in [s for s in placements[0] if s>=lastep]:
        memo.clear()
        mm=M(0,tau0)
        for z in range(n):
            k=len([s for s in epis[0] if s<=tau0])
            assert E[z]>=k+mm.get(z,0), ("chain bound",z,E[z],k,mm.get(z,0))
        out.append((tau0,sum(mm.values())))
    S=sum(E)-n*E[0]
    if verbose:
        print(f"h={h} p={p} T={T} n={n} place={tot_place} E(root)={E[0]} sumE={sum(E)} sum_z(E(z)-E(root))={S}")
        print("  root placements", placements[0], "episodes", epis[0])
        print("  (tau0, sum m) :", out)
    return T,E,out
if __name__=="__main__":
    h=int(sys.argv[1]); p=int(sys.argv[2])
    analyze(h,p,parse(sys.argv[3]))
