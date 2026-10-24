# KMRV (arXiv:2510.08432 v3, Def 2.1-2.8) sequential chain game: vertices 1..L (0 always pebbled),
# start=end=all empty, must visit state_L=pebble; Pebble(i): i-1 pebbled, i in {ghost,empty};
# Unpebble(i): i-1, i pebbled; Ghost(i): i pebbled, free. cost = #Pebble+#Unpebble. space = max pebbles.
# Also: steps-counting variant (ghost=1) for the same game, to relate to T.
import sys
from collections import deque
def solve(L, s, ghost_cost):
    # state: (P bitmask, G bitmask, visited flag)
    start=(0,0,0); dist={start:0}; dq=deque([start]); top=1<<(L-1)
    while dq:
        st=dq.popleft(); d=dist[st]; P,G,f=st
        if f==1 and P==0 and G==0: return d
        for i in range(L):
            b=1<<i; prev = True if i==0 else bool(P&(1<<(i-1)))
            nxt=[]
            if not P&b and prev and bin(P).count('1')<s: nxt.append((P|b, G&~b, 1))
            if P&b and prev: nxt.append((P&~b, G, 1))
            if P&b: nxt.append((P&~b, G|b, ghost_cost))
            for P2,G2,c in nxt:
                f2 = 1 if (f or (P2&top)) else 0
                k=(P2,G2,f2); nd=d+c
                if k not in dist or nd<dist[k]:
                    dist[k]=nd; (dq.appendleft if c==0 else dq.append)(k)
    return None
if __name__=="__main__":
  Lmax=int(sys.argv[1]) if len(sys.argv)>1 else 12
  print("L s W_kmrv T_kmrv(ghost=1)")
  for L in range(1,Lmax+1):
    row=[]
    for s in range(1,min(L,6)+1):
        W=solve(L,s,0); T=solve(L,s,1)
        row.append((s,W,T))
    print(L, row)
