import sys
def load(path):
    return [l.split() for l in open(path) if l.strip() and not l.startswith(('#','T='))]
def sub(v,n):
    out=[];q=[v]
    while q:
        x=q.pop(); out.append(x)
        if 2*x+1<n: q+=[2*x+1,2*x+2]
    return out
def analyze(mv,h):
    n=2**h-1; code={"pebble":1,"unghost":1,"unpebble":0,"ghost":2}
    st=[0]*n; hist=[]
    place={v:[] for v in range(n)}; rem={v:[] for v in range(n)}
    for t,(o,v) in enumerate(mv):
        v=int(v); st[v]=code[o]; hist.append(tuple(st))
        (place if code[o]==1 else rem)[v].append(t)
    res={}
    for u in range(1,n):
        if 2*u+1>=n: continue
        t0=place[u][0]; f=rem[u][-1]
        ok=False
        for c in (2*u+1,2*u+2):
            T=sub(c,n)
            if any(all(hist[t][x]!=1 for x in T) for t in range(t0,f)): ok=True
        d=(u+1).bit_length()-1; hgt=h-d
        res.setdefault(hgt,[]).append(ok)
    return {k:f"{sum(v)}/{len(v)}" for k,v in sorted(res.items())}
if __name__ == "__main__":
  for path,h in [(sys.argv[i],int(sys.argv[i+1])) for i in range(1,len(sys.argv),2)]:
    print(h, "高さ別: 子の部分木が (初回配置, 最後の除去) の間に一度空になる u の数", analyze(load(path),h))
