"""仮説モデル: ある切断で使った妨害ペブルは，その下の連鎖の切断の間も生きている（連鎖に沿って妨害の和 <= h-2）．"""
import math, sys
from functools import lru_cache
sys.setrecursionlimit(100000)
def bound(h):
    B = h - 2
    @lru_cache(None)
    def G(k, R):
        if k <= 2: return 0
        best = math.inf
        for bt in range(R+1):
            cur = [0] + [math.inf]*bt
            for _ in range(4):
                nxt = [math.inf]*(bt+1)
                for s in range(bt+1):
                    if cur[s] == math.inf: continue
                    for b in range(bt+1-s):
                        nxt[s+b] = min(nxt[s+b], cur[s] + H(k-2, b, R-bt))
                cur = nxt
            best = min(best, cur[bt])
        return best
    @lru_cache(None)
    def H(k, b, R):
        if b == 0: return (2**k - 1) + G(k, R)
        if k == 1: return 0
        return min(H(k-1, b1, R) + H(k-1, b-b1, R) for b1 in range(b+1))
    return G(h, B)
for h in (6, 8, 12, 16, 24, 32, 48):
    n = 2**h - 1; g = bound(h)
    print(h, f"ΣE>={n+g}", f"G/n/h={g/n/h:.3f}", f"T>={2*(n+g)-1}")
