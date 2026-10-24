# Relate KMRV round-trip T (all moves counted) to our TP/TUP/TUG on the chain (P1 model: vertices 1..n, vertex 1 always ready).
import sys
from collections import deque
sys.path.insert(0, __file__.rsplit('/',1)[0])
from kmrv_bfs import solve as kmrv
def bfs(n, s, start, goal):
    dist={start:0}; dq=deque([start])
    while dq:
        st=dq.popleft(); d=dist[st]; P,G=st
        if st==goal: return d
        for i in range(n):
            b=1<<i; prev = True if i==0 else bool(P&(1<<(i-1)))
            nxt=[]
            if not P&b and not G&b and prev and bin(P).count('1')<s: nxt.append((P|b, G))      # pebble
            if P&b and prev: nxt.append((P&~b, G))                                               # unpebble
            if P&b: nxt.append((P&~b, G|b))                                                      # ghost (free of precondition)
            if G&b and prev and bin(P).count('1')<s: nxt.append((P|b, G&~b))                     # unghost
            for k in nxt:
                if k not in dist: dist[k]=d+1; dq.append(k)
    return None
def TP(n,s): return bfs(n,s,(0,0),(1<<(n-1),0))
def TUP(n,s): return bfs(n,s,(1<<(n-1),0),(0,0))
def TUG(n,s): return bfs(n,s,(0,1<<(n-1)),(0,0))
print("n s | T_round W | TP(n,s) TUP(n,s) TUG(n,s) | TUG(n-1,s-1) TUP(n-1,s-1) TP(n,s-1)+? ")
for n in range(2,13):
    for s in range(2,min(n,6)+1):
        Tr=kmrv(n,s,1); W=kmrv(n,s,0)
        vals=[TP(n,s),TUP(n,s),TUG(n,s),TUG(n-1,s-1) if s>1 else None,TUP(n-1,s-1) if s>1 else None]
        print(n,s,'|',Tr,W,'|',vals, ' W-(Tr/2+n)=',W-(Tr//2+n))
