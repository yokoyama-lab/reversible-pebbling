# 歩みでの森の値と「最後に空だった時刻」の下界式，1 本の sorted の値の比較
# 歩み w = [β_0,...,β_J]（隣は ±1）．相 k では盤 ≤ β_k，切り替えの瞬間は ≤ min(β_k,β_{k+1})．
import sys, itertools
from collections import deque
INF=10**9
def chain_need(lens):
    need=[];st=0
    for l in lens:
        for j in range(l): need.append(1<<(st+j+1) if j+1<l else 0)
        st+=l
    return need
PC=[bin(i).count('1') for i in range(1<<14)]
def walkdist(need,L,w):
    N=1<<L; d=[INF]*N; d[0]=0
    for k,b in enumerate(w):
        if k>0:
            lim=min(w[k-1],b)
            d=[x if PC[i]<=lim else INF for i,x in enumerate(d)]
        # 相 k の中で BFS（0-1 でなく単位重み．多始点 Dijkstra をバケットで）
        buckets={}
        for i,x in enumerate(d):
            if x<INF and PC[i]<=b: buckets.setdefault(x,[]).append(i)
            elif PC[i]>b: d[i]=INF
        if not buckets: return d
        cur=min(buckets); mx=max(buckets)
        while cur in buckets or cur<=mx:
            for x in buckets.pop(cur,[]):
                if d[x]!=cur: continue
                for v in range(L):
                    if x&need[v]!=need[v]: continue
                    y=x^(1<<v)
                    if PC[y]>b: continue
                    if cur+1<d[y]:
                        d[y]=cur+1; buckets.setdefault(cur+1,[]).append(y); mx=max(mx,cur+1)
            cur+=1
    return d
Cc={}
def C(l,w):
    w=tuple(max(0,b) for b in w)
    if (l,w) not in Cc: Cc[(l,w)]=walkdist(chain_need([l]),l,list(w))[1]
    return Cc[(l,w)]
def walks(J,bmax,start_min=1):
    for b0 in range(start_min,bmax+1):
        def rec(w):
            if len(w)==J: yield list(w); return
            for d in (-1,1):
                nb=w[-1]+d
                if 0<=nb<=bmax: yield from rec(w+[nb])
        yield from rec([b0])
def parts(L,mx):
    if L==0: yield []; return
    for k in range(min(L,mx),0,-1):
        for r in parts(L-k,k): yield [k]+r
LMAX=int(sys.argv[1]); JMAX=int(sys.argv[2])
stat=dict(rows=0,forest_ne_formula=0,forest_gt=0,forest_lt=0,one_ne=0,one_gt_formula=0,one_gt_forest=0,desc_not_best=0)
ex={}
for L in range(2,LMAX+1):
  for p in parts(L,L):
    if len(p)<2: continue
    st=[];s=0
    for l in p: st.append(s); s+=l
    X=sum(1<<a for a in st)
    Y=0;s=0
    for l in sorted(p): Y|=1<<s; s+=l
    for J in range(1,JMAX+1):
      for w in walks(J,L):
        rf=walkdist(chain_need(p),L,w)[X]
        if rf>=INF: continue
        stat['rows']+=1
        best=INF;bestperm=None
        for perm in set(itertools.permutations(p)):
            v=sum(C(l,[b-j for b in w]) for j,l in enumerate(perm))
            if v<best: best=v;bestperm=perm
        desc=sum(C(l,[b-j for b in w]) for j,l in enumerate(p))
        if desc!=best: stat['desc_not_best']+=1; ex.setdefault('desc',(p,w,desc,best,bestperm))
        if rf!=best:
            stat['forest_ne_formula']+=1
            if rf>best: stat['forest_gt']+=1; ex.setdefault('fgt',(p,w,rf,best))
            else: stat['forest_lt']+=1; ex.setdefault('flt',(p,w,rf,best))
        r1=walkdist(chain_need([L]),L,w)[Y]
        if r1!=best: stat['one_ne']+=1
        if r1>best: stat['one_gt_formula']+=1; ex.setdefault('1gt',(p,w,r1,best,rf))
        if r1>rf: stat['one_gt_forest']+=1; ex.setdefault('SORTVIOL',(p,w,r1,rf))
print(stat)
for k,v in ex.items(): print(k,v)
