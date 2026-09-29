import sys
sys.setrecursionlimit(100000)
from claimk import load, sub
def run(mv,h,all_children):
    n=2**h-1; code={"pebble":1,"unghost":1,"unpebble":0,"ghost":2}
    st=[0]*n; hist=[]; place={v:[] for v in range(n)}; rem={v:[] for v in range(n)}
    for t,(o,v) in enumerate(mv):
        v=int(v); st[v]=code[o]; hist.append(tuple(st)); (place if code[o]==1 else rem)[v].append(t)
    demands=[]  # (v, 許される置く手の時刻の集合)
    for u in range(1,n):
        if 2*u+1>=n: continue
        t0=place[u][0]; f=rem[u][-1]
        for c in (2*u+1,2*u+2):
            T=sub(c,n)
            tau=next((t for t in range(t0,f) if all(hist[t][x]!=1 for x in T)),None)
            if tau is None: continue
            for v in T: demands.append([(v,t) for t in place[v] if tau<t<f])
            if not all_children: break
    match={}
    def aug(i,seen):
        for s in demands[i]:
            if s in seen: continue
            seen.add(s)
            if s not in match or aug(match[s],seen):
                match[s]=i; return True
        return False
    got=sum(aug(i,set()) for i in range(len(demands)))
    print(f"h={h} {'子すべて' if all_children else 'u ごとに子 1 つ'}: 要求 {len(demands)} / 互いに異なる手で満たせる最大 {got}")
for path,h in [(sys.argv[i],int(sys.argv[i+1])) for i in range(1,len(sys.argv),2)]:
    for a in (False,True): run(load(path),h,a)
