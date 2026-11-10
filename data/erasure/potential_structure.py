#!/usr/bin/env python3
"""Structural checks on the gap potential `phi` of ErasurePebbling/UpperBound.lean
(gap-merge form; see ErasurePebbling/NOTES.md §3, second attempt).

usage: potential_structure.py p G
Enumerates all gap sequences B_1..B_m (1 ≤ m ≤ p, 1 ≤ B_i ≤ G) and checks
  (R')  B_i ≤ T_m  ⟹  phi(merge_i B) ≤ phi(B)
  (S)   phi(merge_i B) ≤ phi(B) + max(0, B_i − T_m)
  (DEL) for every optimal removal order O of B and every free i, deleting i's
        step from O gives an order of merge_i B of cost ≤ phi(B).
T_m = 2^(p−m).  Exit code 0 iff no failure.  (p = 5, G = 14: ~2 min.)
"""
import sys, itertools
from functools import lru_cache
p=int(sys.argv[1]); G=int(sys.argv[2])
T=lambda m: 2**(p-m)
def merge(B,i):
    B=list(B)
    if i==len(B)-1: return tuple(B[:-1])
    return tuple(B[:i]+[B[i]+B[i+1]]+B[i+2:])
@lru_cache(None)
def phi(B):
    if not B: return 0
    m=len(B)
    return min(max(0,B[i]-T(m))+phi(merge(B,i)) for i in range(m))
def optorders(B, idx, acc=()):
    if not B: yield acc; return
    m=len(B)
    for i in range(m):
        if max(0,B[i]-T(m))+phi(merge(B,i))==phi(B):
            yield from optorders(merge(B,i), idx[:i]+idx[i+1:], acc+(idx[i],))
def cost_of(B, order, idx):
    tot=0
    for r in order:
        i=idx.index(r); m=len(B)
        tot+=max(0,B[i]-T(m)); B=merge(B,i); idx=idx[:i]+idx[i+1:]
    return tot
fR=fS=fD=0; nR=nS=0
for m in range(1,p+1):
    for B in itertools.product(range(1,G+1),repeat=m):
        f=phi(B)
        for i in range(m):
            Bx=merge(B,i); f2=phi(Bx); E=max(0,B[i]-T(m)); nS+=1
            if f2>f+E: fS+=1; print("S FAIL",B,i)
            if B[i]<=T(m):
                nR+=1
                if f2>f: fR+=1; print("R' FAIL",B,i)
                idx=tuple(r for r in range(m) if r!=i)
                for O in optorders(B, tuple(range(m))):
                    O2=tuple(r for r in O if r!=i)
                    if cost_of(Bx,O2,idx)>f: fD+=1; print("DEL FAIL",B,i,O); break
print(f"p={p} G={G}: R' {nR} checked {fR} fails | S {nS} checked {fS} fails | DEL {fD} fails")
sys.exit(0 if fR==fS==fD==0 else 1)
