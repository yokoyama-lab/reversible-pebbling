import math
from functools import lru_cache
def bound(h, B):
    @lru_cache(None)
    def G(k):
        if k <= 2: return 0
        cur = [0]*(B+1)
        for _ in range(4):
            nxt = [math.inf]*(B+1)
            for s in range(B+1):
                for b in range(B+1-s):
                    nxt[s+b] = min(nxt[s+b], cur[s] + H(k-2, b))
            cur = nxt
        return min(cur)
    @lru_cache(None)
    def H(k, b):
        if b == 0: return (2**k - 1) + G(k)
        if k == 1: return 0
        return min(H(k-1, b1) + H(k-1, b-b1) for b1 in range(b+1))
    return G(h)
for B in (0, 1, 2, 4, 8):
    row = []
    for h in (8, 16, 24, 32, 48, 64):
        n = 2**h - 1; row.append(f"h={h}:{(bound(h,B))/n/h:.3f}")
    print(f"B={B}: G(h)/(n h) ", " ".join(row))
