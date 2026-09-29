"""連鎖の議論の最悪値: 各切断で深さ 2 以上下に最大 B = h-2 個の妨害ペブル（敵が配置を選ぶ）．
ΣE >= n + G(h)．T >= 2(n + G(h)) - 1．"""
import math, sys
from functools import lru_cache

def bound(h):
    B = h - 2
    @lru_cache(None)
    def G(k):
        if k <= 2: return 0
        # 4 つの孫の部分木（高さ k-2）に b1..b4（和 <= B）を配る
        best = [0] + [math.inf]*B   # 部分木を 1 つずつ足す畳み込み
        cur = [0]*(B+1)
        for _ in range(4):
            nxt = [math.inf]*(B+1)
            for s in range(B+1):
                if cur[s] == math.inf: continue
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

if __name__ == "__main__":
  for h in list(range(3, 13)) + [16, 20, 24, 28, 32, 40]:
    n = 2**h - 1; g = bound(h)
    SE = n + g; T = 2*SE - 1
    print(f"h={h:2d} n={n}  ΣE>={SE}  T>={T}  4n-2p-1={4*n-2*(h+1)-1}  ΣE/n={SE/n:.3f}  (ΣE/n-1)*log2(h)/h={(SE/n-1)*math.log2(h)/h:.3f}")
