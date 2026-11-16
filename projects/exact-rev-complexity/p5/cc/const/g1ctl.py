# 対照: c > d（GRAFT の条件の外）で R^Q > R^P が出るか，F(c,S)+F(d,S-1) が c<d で R より大きいことがあるか
exec(open('g1.py').read().split('LMAX=')[0])
gt=0;strict=0;rows=0
for L in range(2,13):
  for c in range(1,L):
    d=L-c
    for S in range(2,L+1):
        dP=bfs(chain_need([c,d]),L,S); dQ=bfs(chain_need([L]),L,S)
        rp=dP[1|(1<<c)]; rq=dQ[1|(1<<c)]
        if rp>=INF: continue
        rows+=1
        if c>d and rq>rp: gt+=1
        if c<d and F(c,S)+F(d,S-1)>rp: strict+=1
print("rows",rows,"c>d で R^Q>R^P:",gt,"c<d で逆順の式が真に大きい:",strict)
