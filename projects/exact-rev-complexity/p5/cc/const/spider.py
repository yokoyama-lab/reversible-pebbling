# 蜘蛛型の木（根 u と長さ ℓ_1..ℓ_k の脚）で M(G,S) を BFS で求め，(a) M ≥ F_c(n,S)，
# (b) 帰着の形 M = 1 + min_X [R_S(X) + R_{S-1}(X)]（X は脚の盤，全脚の頂上を含む，|X| ≤ S-1）を確かめる．
exec(open('g1.py').read().split('Fc={}')[0])
Fm={}
def Fc(n,S):
  if S<=0: return INF
  if (n,S) not in Fm: Fm[(n,S)]=bfs(chain_need([n]),n,S)[1]
  return Fm[(n,S)]
def parts(L,mx):
  if L==0: yield []; return
  for k in range(min(L,mx),0,-1):
    for r in parts(L-k,k): yield [k]+r
bad=0;rows=0;dec=0
for n in range(3,14):
  for legs in parts(n-1,n-1):
    if len(legs)<2: continue
    L=n-1; need=chain_need(legs)+[0]; st=[];s=0
    for l in legs: st.append(s); s+=l
    tops=sum(1<<a for a in st); need[L]=tops  # 根 u = 頂点 L
    for S in range(2,n+1):
      M=bfs(need,n,S)[1<<L]
      if M>=INF: continue
      rows+=1
      if M<Fc(n,S): bad+=1; print("CC viol",legs,S,M,Fc(n,S))
      dS=bfs(chain_need(legs),L,S); dS1=bfs(chain_need(legs),L,S-1)
      best=min((dS[X]+dS1[X] for X in range(1<<L) if X&tops==tops and bin(X).count('1')<=S-1),default=INF)+1
      if best!=M: dec+=1; print("decomp",legs,S,M,best)
print("rows",rows,"CC_viol",bad,"decomp_mismatch",dec)
