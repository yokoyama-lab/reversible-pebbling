# (3) 森（頂上だけに石）の予算一定の最短手数 = Σ_j F(s_j, S-j+1)（s を長い順）．(4) 1 本の sorted(X) はそれ以下．BFS で合計 ≤ 12．
exec(open('g1.py').read().split('Fc={}')[0])
from itertools import combinations_with_replacement
Fm={}
def F(n,S):
  if S<=0: return INF
  if (n,S) not in Fm: Fm[(n,S)]=bfs(chain_need([n]),n,S)[1]
  return Fm[(n,S)]
def parts(L,mx):
  if L==0: yield []; return
  for k in range(min(L,mx),0,-1):
    for r in parts(L-k,k): yield [k]+r
neq=0;up=0;rows=0
for L in range(2,13):
  for p in parts(L,L):  # 長い順
    if len(p)<2: continue
    st=[];s=0
    for l in p: st.append(s); s+=l
    X=sum(1<<a for a in st)
    asc=sorted(p); Y=0;s=0
    for l in asc: Y|=1<<s; s+=l
    for S in range(1,L+1):
      rf=bfs(chain_need(p),L,S)[X]; formula=sum(F(l,S-j) for j,l in enumerate(p))
      if formula>=INF: formula=INF
      if rf>=INF and formula>=INF: continue
      rows+=1
      if rf!=formula: neq+=1; print("NEQ",p,S,rf,formula)
      rq=bfs(chain_need([L]),L,S)[Y]
      if rq>formula: up+=1; print("UP",p,S,rq,formula)
print("rows",rows,"forest!=formula",neq,"onechain>formula",up)
