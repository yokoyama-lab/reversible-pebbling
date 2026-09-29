"""chain_dp.py の G(k) を，妨害集合の全列挙で独立に計算して照合（h<=6）．"""
import itertools, math
from functools import lru_cache
from chain_dp import bound
def brute(h):
    B = h - 2
    @lru_cache(None)
    def G(k):
        if k <= 2: return 0
        n = 2**k - 1   # 高さ k の木（ヒープ順），深さ 2 以上の頂点
        verts = [v for v in range(3, n)]
        def sub(v):
            out, q = [], [v]
            while q:
                x = q.pop(); out.append(x)
                if 2*x+1 < n: q += [2*x+1, 2*x+2]
            return out
        hgt = lambda v: k - ((v+1).bit_length()-1)
        best = math.inf
        for r in range(0, min(B, len(verts))+1):
            for S in itertools.combinations(verts, r):
                Sset = set(S); tot = 0
                def rec(y):
                    nonlocal tot
                    if not any(z in Sset for z in sub(y)):
                        tot += (2**hgt(y) - 1) + G(hgt(y)); return
                    for c in (2*y+1, 2*y+2):
                        if c < n: rec(c)
                for g in (3, 4, 5, 6):
                    if g < n: rec(g)
                best = min(best, tot)
        return best
    return G(h)
for h in (3, 4, 5, 6):
    print(h, "brute", brute(h), "dp", bound(h))
