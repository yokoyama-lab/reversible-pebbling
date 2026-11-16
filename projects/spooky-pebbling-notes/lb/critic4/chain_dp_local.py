"""妨害数が切断の高さ k に依存する場合: B(k) = k-2（データで観測された値）と B(k) = min(h-2, c) など．"""
import math, sys
from functools import lru_cache
sys.setrecursionlimit(100000)
def bound(h, Bf):
    @lru_cache(None)
    def G(k):
        if k <= 2: return 0
        B = Bf(k)
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
for h in (16, 32, 64, 128, 256):
    n = 2**h - 1
    a = bound(h, lambda k: k-2); b = bound(h, lambda k: h-2)
    print(h, f"B=k-2: G/n/h={a/n/h:.3f} G/n/(h/log2h)={a/n/(h/math.log2(h)):.3f}   B=h-2: G/n/h={b/n/h:.3f}")
