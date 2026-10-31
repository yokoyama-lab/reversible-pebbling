# GRAFT 最小の場合（予算一定）: 2 本 {A0,D0} と 1 本 {v0,v_c} の最短手数，および候補式との比較
import sys
from collections import deque
INF=10**9
def bfs(need, L, S):
    N=1<<L; dist=[INF]*N; dist[0]=0; q=deque([0])
    while q:
        x=q.popleft()
        for v in range(L):
            if x & need[v] != need[v]: continue
            y=x^(1<<v)
            if bin(y).count('1')>S: continue
            if dist[y]==INF: dist[y]=dist[x]+1; q.append(y)
    return dist
def chain_need(lens):
    need=[];st=0
    for l in lens:
        for j in range(l):
            need.append(1<<(st+j+1) if j+1<l else 0)
        st+=l
    return need
Fc={}
def F(n,S):
    if (n,S) not in Fc:
        d=bfs(chain_need([n]),n,S); Fc[(n,S)]=d[1]
    return Fc[(n,S)]
LMAX=int(sys.argv[1])
bad=0;rows=0;notmin=0
for L in range(2,LMAX+1):
  for c in range(1,L//2+1):
    d=L-c
    for S in range(1,L+1):
        dP=bfs(chain_need([c,d]),L,S); dQ=bfs(chain_need([L]),L,S)
        rp=dP[1|(1<<c)]; rq=dQ[1|(1<<c)]
        if rp>=INF and rq>=INF: continue
        rows+=1
        cand=min(F(d,S)+F(c,S-1) if S>1 else INF, F(c,S)+F(d,S-1) if S>1 else INF)
        a1=F(d,S)+F(c,S-1) if S>1 else INF
        if rp!=rq: bad+=1; print("NEQ",c,d,S,rp,rq)
        if rp!=a1: notmin+=1; print("formula",c,d,S,"R=",rp,"F(d,S)+F(c,S-1)=",a1,"other=",F(c,S)+F(d,S-1) if S>1 else None)
print("rows",rows,"neq",bad,"formula_miss",notmin)
