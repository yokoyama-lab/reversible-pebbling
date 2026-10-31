# (1) F(.,S) は凸で，増分の列 = (2) ++ merge(I_G, I_{S-1})，I_G(m) = I_S(m)+I_{S-1}(m)．(2) 有限域は 1..2^{S-1}．
import heapq
INF=float('inf'); N=1024; SM=11
F=[[INF]*(N+1) for _ in range(SM+1)]
for S in range(1,SM+1):
  for n in range(1,N+1):
    F[S][n]=1 if n==1 else min((F[S][m]+F[S-1][m]+F[S-1][n-m] for m in range(1,n)),default=INF)
def inc(S): return [F[S][n+1]-F[S][n] for n in range(1,N) if F[S][n+1]<INF]
bad=0
for S in range(2,SM+1):
  dom=max(n for n in range(1,N+1) if F[S][n]<INF)
  if dom!=min(2**(S-1),N): bad+=1; print("dom",S,dom)
  I=inc(S); Ip=inc(S-1)
  if any(I[i]>I[i+1] for i in range(len(I)-1)): bad+=1; print("nonconvex",S)
  IG=[I[m]+Ip[m] for m in range(min(len(I),len(Ip)))]
  pred=[2]+sorted(IG+Ip)
  if pred[:len(I)]!=I: bad+=1; print("merge mismatch",S)
print("bad",bad)
