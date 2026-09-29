# Independent DP: G(h) = min over adversary (<= b=h-2 pebbles at depth>=2 below each chain vertex,
# chosen independently at each chain step) of sum over maximal free subtrees Y of (|Y| + F(ht Y)).
import sys, math
import numpy as np
INF=10**18
def minplus(a,b):
    n=len(a); out=np.full(n,INF,dtype=np.int64)
    for i in range(n):
        v=a[i]+b[:n-i]
        np.minimum(out[i:],v,out=out[i:])
    return out
def G(h):
    b=h-2
    F=[0]*(h+1)   # F[k], k=height (leaf=1)
    C=[None]*(h+1)
    for k in range(1,h+1):
        # F[k] needs C[k-2]
        if k<=2: F[k]=0
        else:
            c=C[k-2]
            acc=c.copy()
            for _ in range(3): acc=minplus(acc,c)
            F[k]=int(acc.min())   # <= b pebbles total
        # C[k]: subtree of height k at depth>=2, c pebbles inside
        size=2**k-1
        arr=np.full(b+1,INF,dtype=np.int64)
        arr[0]=size+F[k]
        if k==1:
            arr[1:]=0
        else:
            ch=minplus(C[k-1],C[k-1])  # split among children
            # no pebble on vertex: need >=1 pebble in children
            for cc in range(1,b+1):
                arr[cc]=min(arr[cc],ch[cc])
                arr[cc]=min(arr[cc],ch[cc-1])  # pebble on vertex itself
        # allow wasting pebbles: monotone (<=) for c>=1 only
        for cc in range(2,b+1): arr[cc]=min(arr[cc],arr[cc-1])
        C[k]=arr
    return F[h]
for h in [3,4,5,6,7,8]:
    g=G(h); n=2**h-1
    print(h,g,"T>=",2*(n+g)-1,"4n-2p-1=",4*n-2*(h+1)-1)
for h in [16,32,64,128]:
    g=G(h); n=2**h-1
    print(h,g/n,(g/n)/(h/math.log2(h)))
