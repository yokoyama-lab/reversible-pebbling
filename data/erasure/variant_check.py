#!/usr/bin/env python3
"""Variant check: the 'touch' model (goal = node n pebbled at some moment, no clean end) does NOT reproduce the note's numbers."""
import pebble
def bfs_touch(N, p, E):
    E1 = E + 1; mask = (1 << N) - 1
    seen = {0}; frontier = [0]; d = 0; first = {}
    while frontier:
        d += 1; nxt = []
        for s in frontier:
            c, eu = divmod(s, E1); avail = ((c << 1) | 1) & mask; k = bin(c).count('1')
            x = avail
            while x:
                b = x & -x; x ^= b
                if c & b: nc = c ^ b
                else:
                    if k >= p: continue
                    nc = c | b
                ns = nc * E1 + eu
                if ns not in seen:
                    seen.add(ns); nxt.append(ns)
                    top = nc.bit_length()
                    for n in range(1, N + 1):
                        if (nc >> (n - 1)) & 1 and (n, eu) not in first: first[(n, eu)] = d
            if eu < E:
                x = c & ~avail
                while x:
                    b = x & -x; x ^= b; nc = c ^ b; ns = nc * E1 + eu + 1
                    if ns not in seen:
                        seen.add(ns); nxt.append(ns)
                        for n in range(1, N + 1):
                            if (nc >> (n - 1)) & 1 and (n, eu + 1) not in first: first[(n, eu + 1)] = d
        frontier = nxt
    return first
if __name__ == '__main__':
    N = 17
    for p in (5, 6, 7):
        f = bfs_touch(N, p, 3)
        M = pebble.mstar_from_first(f, N, 3) if hasattr(pebble, 'mstar_from_first') else None
        best = lambda n, e: min([f.get((n, eu), float('inf')) for eu in range(e + 1)])
        print(f"touch variant p={p}: M_touch(16,p,e)={[best(16,e) for e in range(4)]}, M_touch(17,p,0)={best(17,0)}, reach_touch(p,0) within N=17: {max(n for n in range(1,N+1) if best(n,0)<float('inf'))}")
    print("clean variant (the note's model): M*(16,5,e)=[71,45,37,31], M*(16,6,0)=51, M*(16,7,0)=49, reach(5,0)=16")
