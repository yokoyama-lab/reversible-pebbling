# Third independent check: replay witness walks in pure Python (phase-by-phase Dijkstra via heapq).
import sys, heapq
def R(lens, walk):
    # vertices: list of (chain, pos); bit index = running offset
    req=[]; off=0
    for l in lens:
        for p in range(l): req.append(off+p+1 if p<l-1 else None)
        off+=l
    n=off
    D={0:0}
    for i,b in enumerate(walk):
        D={x:d for x,d in D.items() if bin(x).count('1')<=b}
        pq=[(d,x) for x,d in D.items()]; heapq.heapify(pq); best=dict(D)
        while pq:
            d,x=heapq.heappop(pq)
            if best.get(x)!=d: continue
            for v in range(n):
                if req[v] is not None and not (x>>req[v])&1: continue
                y=x^(1<<v)
                if bin(y).count('1')>b: continue
                if best.get(y,10**9)>d+1: best[y]=d+1; heapq.heappush(pq,(d+1,y))
        D=best
    return D
ok=bad=0
for line in open(sys.argv[1]):
    t=line.split(); mp=int(t[0].split('=')[1])
    i=t.index('walk'); lens=list(map(int,t[2:t.index(next(s for s in t if s.startswith('X=')))]))
    X=int(t[i-2].split('=')[1]); Y=int(t[i-1].split('=')[1]); walk=list(map(int,t[i+1:]))
    if walk[0] not in range(0,sum(lens)+1) or any(abs(walk[j+1]-walk[j])!=1 for j in range(len(walk)-1)): print("badwalk",line); bad+=1; continue
    D2=R(lens,walk); D1=R([sum(lens)],walk)
    r1=D1.get(Y,float('inf')); r2=D2.get(X,float('inf'))
    if r1>r2: ok+=1
    else: bad+=1; print("NOT A VIOLATION",line.strip(),r1,r2)
print("witnesses confirmed",ok,"failed",bad)
