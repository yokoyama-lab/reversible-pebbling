# 対照: (a) シフト j−1 を 0 にする（予算を減らさない）, (b) 短い順を最善とする, (c) クランプなし（負の予算は不可）
exec(open('w1.py').read().split('LMAX=')[0])
import itertools
LMAX=int(sys.argv[1]); JMAX=int(sys.argv[2])
a=b=c=rows=0
for L in range(2,LMAX+1):
  for p in parts(L,L):
    if len(p)<2: continue
    st=[];s=0
    for l in p: st.append(s); s+=l
    X=sum(1<<q for q in st)
    for J in range(1,JMAX+1):
      for w in walks(J,L):
        rf=walkdist(chain_need(p),L,w)[X]
        if rf>=INF: continue
        rows+=1
        if sum(C(l,w) for l in p)!=rf: a+=1
        asc=sorted(p)
        if sum(C(l,[x-j for x in w]) for j,l in enumerate(asc))!=rf: b+=1
        # (c) ここでは「j 番目は一律 β−j」(1 つ多く引く)
        v=sum(C(l,[x-j-1 for x in w]) if j>0 else C(l,w) for j,l in enumerate(p))
        if v!=rf: c+=1
print("rows",rows,"shift0_mismatch",a,"ascending_mismatch",b,"overshift_mismatch",c)
