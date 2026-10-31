# 2CM_2（規則版）の最適解の形: 境目 1（u を置く，予算 −1）と境目 2（u を外す，+1）の間の脚の動き．
# 森の最適 = min_{X1,X2 ⊇ 頂上} pre(X1) + mid(X1→X2) + post(X2)．
# 調べること: (a) 最適の中に X1 = X2・中間 0 手のものがあるか，(b) 無いとき，sorted(X1)→sorted(X2) の 1 本の中間が森の中間以下か．
import sys, itertools
INF=10**9
def need_of(lens):
    need=[];st=0
    for l in lens:
        for j in range(l): need.append(1<<(st+j+1) if j+1<l else 0)
        st+=l
    return need
def phase_closure(d,need,L,b):
    N=1<<L
    d=[x if bin(i).count('1')<=b else INF for i,x in enumerate(d)]
    ch=True
    while ch:
        ch=False
        for x in range(N):
            if d[x]>=INF: continue
            for v in range(L):
                if x&need[v]!=need[v]: continue
                y=x^(1<<v)
                if bin(y).count('1')>b: continue
                if d[x]+1<d[y]: d[y]=d[x]+1; ch=True
    return d
def run(d,need,L,phases):
    # phases: list of budgets; between phases the board must fit both
    for k,b in enumerate(phases):
        if k>0:
            lim=min(phases[k-1],b); d=[x if bin(i).count('1')<=lim else INF for i,x in enumerate(d)]
        d=phase_closure(d,need,L,b)
    return d
def sorted_board(lens,X):
    st=[];s=0
    for l in lens: st.append(s); s+=l
    seg=[]
    for i,l in enumerate(lens):
        prev=None
        for j in range(l):
            if X>>(st[i]+j)&1:
                if prev is not None: seg.append(j-prev)
                prev=j
        seg.append(l-prev)
    seg.sort(); Y=0;p=0
    for g in seg: Y|=1<<p; p+=g
    return Y
def instances(L,J):
    mode=sys.argv[3]
    for p in range(1,J):
        for q in range(p+1,J):
            def rec(w):
                k=len(w)
                if k==J: yield list(w); return
                if k==0:
                    for b in range(0,L+2): yield from rec([b])
                    return
                if k==p and mode in ('t1','rule'): ds=[-1]
                elif k==q and mode in ('t2','rule'): ds=[1]
                elif mode=='rule': ds=[-1,1]
                else: ds=[-2,-1,1,2]
                for dd in ds:
                    nb=w[-1]+dd
                    if 0<=nb<=L+1: yield from rec(w+[nb])
            for w in rec([]): yield p,q,w
lens=[int(x) for x in sys.argv[1].split(',')]; J=int(sys.argv[2])
L=sum(lens); N=1<<L
needP=need_of(lens)
st=[];s=0
for l in lens: st.append(s); s+=l
tops=sum(1<<a for a in st)
K=len(lens)

from collections import Counter
C=Counter()
for p,q,w in instances(L,J):
    pre=w[:p]; mid=w[p:q]; post=w[q:]
    m=min(mid)
    d0=[INF]*N; d0[0]=0
    dpre=run(d0,needP,L,pre); dpre=[x if (i&tops)==tops and bin(i).count('1')<=w[p] else INF for i,x in enumerate(dpre)]
    dpost=run(d0,needP,L,post[::-1]); dpost=[x if (i&tops)==tops and bin(i).count('1')<=w[q-1] else INF for i,x in enumerate(dpost)]
    def hv(Y):
        if bin(Y).count('1')>m or (Y&tops)!=tops: return INF
        return dpre[Y]+dpost[Y]
    for X1 in range(N):
        if dpre[X1]>=INF: continue
        dd=[INF]*N; dd[X1]=0; dm=run(dd,needP,L,mid)
        for X2 in range(N):
            if dpost[X2]>=INF or dm[X2]>=INF: continue
            v=dpre[X1]+dm[X2]+dpost[X2]
            C['pairs']+=1
            cands={'X1':X1,'X2':X2,'cap':X1&X2,'cup':X1|X2}
            ok=[k for k,Y in cands.items() if hv(Y)<=v]
            for k in ok: C[k]+=1
            if 'cap' not in ok:
                hbest=min(hv(Y) for Y in range(N))
                if hbest>=INF: C['capfail_infeas']+=1
                else:
                    C['capfail_feas']+=1
                    if C['capfail_feas']<=3: print(w,p,q,bin(X1),bin(X2),dpre[X1],dm[X2],dpost[X2],'cap',bin(X1&X2),hv(X1&X2),'hbest',hbest)
            if hv(X1)<=v or hv(X2)<=v: C['X1orX2']+=1
print(lens,J,sys.argv[3],dict(C))
