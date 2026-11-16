# 予想の閉じた形: 鎖の森（頂上だけ）の歩み w での値 = Σ_j F(s_j, T_j)（s は長い順），
#   T_j = max{β_k : k は「β ≤ j−1 の最後の相」より後} − (j−1)（そのような相が無ければ ∞ 扱いで不可）
# と，1 本の sorted の値が同じかを BFS で確かめる．あわせて 1 本の鎖の C(ℓ,w) = F(ℓ, T_1)．
exec(open('w1.py').read().split('LMAX=')[0])
Fm={}
def F(n,S):
    if S<=0: return INF
    if (n,S) not in Fm: Fm[(n,S)]=walkdist(chain_need([n]),n,[S])[1]
    return Fm[(n,S)]
def T(w,j):
    last=-1
    for k,b in enumerate(w):
        if b<=j-1: last=k
    suf=w[last+1:]
    if not suf: return 0
    return max(suf)-(j-1)
def parts(L,mx):
    if L==0: yield []; return
    for k in range(min(L,mx),0,-1):
        for r in parts(L-k,k): yield [k]+r
LMAX=int(sys.argv[1]); JMAX=int(sys.argv[2])
st_=dict(rows=0,forest_ne=0,one_ne=0,C_ne=0,one_gt_forest=0,tight=0)
ex={}
LMIN=int(sys.argv[3]) if len(sys.argv)>3 else 1
for L in range(LMIN,LMAX+1):
  for p in parts(L,L):
    st=[];s=0
    for l in p: st.append(s); s+=l
    X=sum(1<<a for a in st)
    Y=0;s=0
    for l in sorted(p): Y|=1<<s; s+=l
    for J in range(1,JMAX+1):
      for w in walks(J,L):
        formula=sum(F(l,T(w,j+1)) for j,l in enumerate(p))
        formula=min(formula,INF)
        rf=walkdist(chain_need(p),L,w)[X] if len(p)>1 else None
        r1=walkdist(chain_need([L]),L,w)[Y]
        if len(p)==1:
            if r1!=formula: st_['C_ne']+=1; ex.setdefault('C',(p,w,r1,formula))
            continue
        if rf>=INF and formula>=INF and r1>=INF: continue
        st_['rows']+=1
        if any(F(l,T(w,j+1))!=F(l,max(w)-j) for j,l in enumerate(p)): st_['tight']+=1
        if rf!=formula: st_['forest_ne']+=1; ex.setdefault('forest',(p,w,rf,formula))
        if r1!=formula: st_['one_ne']+=1; ex.setdefault('one',(p,w,r1,formula))
        if r1>rf: st_['one_gt_forest']+=1
print(st_)
for k,v in ex.items(): print(k,v)
