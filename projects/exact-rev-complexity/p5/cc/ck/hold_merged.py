import sys
src=open('hold.py').read()
exec(src[:src.index('lens=[int(x)')])
def solve(lens,w,p,q):
    L=sum(lens); N=1<<L; need=need_of(lens)
    st=[];s=0
    for l in lens: st.append(s); s+=l
    tops=sum(1<<a for a in st)
    pre=w[:p]; mid=w[p:q]; post=w[q:]
    d0=[INF]*N; d0[0]=0
    dpre=run(d0,need,L,pre); dpre=[x if (i&tops)==tops and bin(i).count('1')<=w[p] else INF for i,x in enumerate(dpre)]
    dpost=run(d0,need,L,post[::-1]); dpost=[x if (i&tops)==tops and bin(i).count('1')<=w[q-1] else INF for i,x in enumerate(dpost)]
    best=INF;arg=None
    for X1 in range(N):
        if dpre[X1]>=INF: continue
        dd=[INF]*N; dd[X1]=0; dm=run(dd,need,L,mid)
        for X2 in range(N):
            if dpost[X2]<INF and dm[X2]<INF:
                v=dpre[X1]+dm[X2]+dpost[X2]
                if v<best: best=v; arg=(bin(X1),bin(X2),dpre[X1],dm[X2],dpost[X2])
    return best,arg
lens=[int(x) for x in sys.argv[1].split(',')]
w=[int(x) for x in sys.argv[2].split(',')]; p=int(sys.argv[3]); q=int(sys.argv[4])
print('forest',solve(lens,w,p,q)); print('merged',solve([sum(lens)],w,p,q))
