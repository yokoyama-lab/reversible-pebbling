#!/usr/bin/env python3
"""Component structure of reversible chain pebbling with peak p, and a normal-form search for reach(p,e).

Config = sorted tuple of pebbled nodes (1-based; node 0 is the free entrance).
Pebble x in config C with k pebbles is *removable* iff gap(x) <= 2^(p-k), where gap(x) = x - (largest pebble
below x, or 0).  (Touch x-1 from the pebble below with the p-k free pebbles -- classical touch-reach 2^f - 1 --
remove x, undo.)  Removability is preserved when another removable pebble is removed (if X sits directly below
Y then Y's new gap is g_X+g_Y <= 2^f+2^f = 2^(f+1), the new budget), so by Newman's lemma greedy elimination
has a unique normal form nf(C).  Placing a pebble creates a removable pebble (gap 1 <= 2^0), hence nf is
invariant under reversible moves, and nf(C) lies in C's component.  THEOREM: C ~ D (reversibly connected
within peak p) iff nf(C) = nf(D); in particular {n} is reachable from the empty config iff n <= 2^(p-1).

Search over normal forms: N_0 = {()}, N_{e+1} = N_e U { nf(C \\ {x}) : nf(C) in N_e, x in C, x-1 not in C }.
Components comp(N) = {C : nf(C) = N} are enumerated *without a visited set* by canonical reverse elimination
(insert x only if x is the LOWEST removable pebble of the new config), so each C is generated exactly once.
reach(p,e) = max n with nf({n}) in N_e  (nf({n}) = () if n <= 2^(p-1), else {n}).
"""
import sys, time

def gap_of(C, i):
    return C[i] - (C[i - 1] if i > 0 else 0)

def removable(C, i, p):
    return gap_of(C, i) <= (1 << (p - len(C)))

def nf(C, p):
    C = list(C)
    changed = True
    while changed:
        changed = False
        for i in range(len(C)):
            if removable(C, i, p):
                del C[i]; changed = True; break
    return tuple(C)

def lowest_removable(C, p):
    for i in range(len(C)):
        if removable(C, i, p):
            return i
    return -1

def component(Nf, p, nmax):
    """Yield every config C (nodes <= nmax) with nf(C) == Nf, each exactly once."""
    stack = [tuple(Nf)]
    while stack:
        C = stack.pop()
        yield C
        k = len(C)
        if k >= p:
            continue
        # candidate insert positions: any empty node x <= nmax; x removable in C+{x} needs gap <= 2^(p-k-1)
        budget = 1 << (p - k - 1)
        prev = 0
        for i in range(k + 1):
            nxt = C[i] if i < k else nmax + 1
            # x in (prev, nxt), gap x-prev <= budget
            for x in range(prev + 1, min(nxt, prev + budget + 1)):
                D = C[:i] + (x,) + C[i:]
                if lowest_removable(D, p) == i:
                    stack.append(D)
            prev = nxt

def erasure_successors(C, p):
    """Normal forms obtainable by one erasure from C."""
    out = set()
    for i, x in enumerate(C):
        if x >= 2 and (i == 0 or C[i - 1] != x - 1):
            out.add(nf(C[:i] + C[i + 1:], p))
    return out

def search(p, E, nmax, verbose=False, collect_configs=False):
    """Returns (levels: dict normalform -> e at which discovered, reach: list reach(p,e) for e<=E, ncfg)."""
    level = {(): 0}
    frontier = [()]
    ncfg = 0
    allcfg = set() if collect_configs else None
    t0 = time.time()
    for e in range(E + 1):
        new = []
        for Nf in frontier:
            for C in component(Nf, p, nmax):
                ncfg += 1
                if collect_configs:
                    allcfg.add((C, e))
                if e < E:
                    for N2 in erasure_successors(C, p):
                        if N2 not in level:
                            level[N2] = e + 1
                            new.append(N2)
        if verbose:
            print(f"  p={p} e={e}: {len(frontier)} new normal forms, configs so far {ncfg}, t={time.time()-t0:.1f}s", file=sys.stderr, flush=True)
        frontier = new
    reach = []
    for e in range(E + 1):
        r = 1 << (p - 1)
        for Nf, lv in level.items():
            if len(Nf) == 1 and lv <= e and Nf[0] > r:
                r = Nf[0]
        reach.append(r)
    return level, reach, ncfg, allcfg

if __name__ == '__main__':
    p = int(sys.argv[1]); E = int(sys.argv[2]); nmax = int(sys.argv[3]) if len(sys.argv) > 3 else (E + 2) * 2 ** (p - 2) + 1
    level, reach, ncfg, _ = search(p, E, nmax, verbose=True)
    print(f"p={p} nmax={nmax}: reach = {reach}; conj = {[(e+2)*2**(p-2) for e in range(E+1)]}; normal forms = {len(level)}; configs enumerated = {ncfg}")
