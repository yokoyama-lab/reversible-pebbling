# Exact minimum sequential pebbling cost of KMRV's chain game from our Lean-proved chain formulas:
#   W*_KMRV(l,s) = T_UG(l,s)/2 + l,   T_UG = T_UP + delta,  T_UP = max_m(2 m l - beta_m(s)),  delta = +1 (l<theta) / -1 (l>=theta), theta = s(s+1)/2
# (T_round = T_UG observed by BFS for l<=12, s<=6; W = T_round/2 + l by the work identity with all vertices ending empty.)
import sys
from functools import lru_cache
sys.path.insert(0, __file__.rsplit('/',1)[0])
@lru_cache(None)
def b(m,s):
    if m==0: return 1
    if m==1: return s
    if s==2: return m
    return b(m-1,s)+b(m,s-1)
def beta(m,s): return 1+sum(2*b(j,s) for j in range(1,m))
def tup(n,s):
    m,best=1,2*n-1
    while True:
        v=2*(m+1)*n-beta(m+1,s)
        if v<best: return best
        best,m=v,m+1
def theta(s): return s*(s+1)//2
def tug(n,s): return tup(n,s)+(1 if n<theta(s) else -1)
def Wk(l,s): 
    t=tug(l,s); assert t%2==0; return t//2+l
if __name__=="__main__":
    from kmrv_bfs import solve as kmrv
    from kmrv_relate import TUG
    bad=0
    for n in range(2,13):
        for s in range(2,min(n,6)+1):
            W=kmrv(n,s,0); Tr=kmrv(n,s,1); f=Wk(n,s)
            ok=(W==f and Tr==tug(n,s) and TUG(n,s)==tug(n,s)); bad+= not ok
            if not ok: print("MISMATCH",n,s,W,f,Tr,tug(n,s),TUG(n,s))
    print("validation n<=12 s<=6: bad =",bad)
    print("\nKMRV Tables 5/6 rows: l, s, Per run (their depth-optimal solution), W*(l,s) exact min cost, ratio")
    rows=[(88,5,500),(88,7,370),(88,12,295),(82,5,451),(82,7,341),(82,12,266),(79,5,429),(79,7,326),(79,12,253),
          (106,5,652),(106,7,475),(106,8,444),(100,5,600),(100,7,446),(100,12,381),(97,5,575),(97,7,432),(97,12,345),(94,5,550),(94,7,419),(94,12,326)]
    for l,s,per in rows:
        w=Wk(l,s); print(l,s,per,w, round(per/w,3), " 2l=",2*l)
    print("\ns=4 (they say 'in the thousands'):", [(l,Wk(l,4)) for l in (79,82,88,94,97,100,106)])
    print("s=3:", [(l,Wk(l,3)) for l in (79,88,106)])
    print("theta(s):", {s:theta(s) for s in (4,5,7,8,12)})
