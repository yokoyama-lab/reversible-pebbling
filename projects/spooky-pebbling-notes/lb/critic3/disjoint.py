"""「窓を入れ子にしない」版: 各 u に (子 c, 補題 R の締まった窓 W=(b,s]) を高々 1 つ選ぶ．b = T(c) が空の最後の時刻，s = その後の c の最初の配置，
t0_u < b, s < f_u．祖先 u' の選んだ子が u の祖先か u 自身なら W_u ∩ W_u' = ∅ を要求．このとき置く手 >= n + Σ|T(c_u)| が補題 R だけで出る．
選べる Σ|T(c_u)| の最大を木の DP で求める．あわせて (1) 最初に空になる子を選ぶ規則での頂点ごとのマッチング，(2) 高さ<=3 に限った子最適化も出す．"""
import sys
from functools import lru_cache
from common import kids, subtree
from events import prep, empty_at

def main(path, h, cap):
    mv, S, n, place, rem, remop = prep(path, h, cap)
    END = len(mv)
    W = {}
    first_empty = {}
    for u in range(1, n):
        if 2 * u + 1 >= n:
            continue
        t0, f = place[u][0], rem[u][-1]
        for c in kids(u, n):
            T = subtree(c, n)
            ws = []
            b = None
            for t in range(t0 + 1, f):
                if empty_at(S, T, t):
                    b = t
                    first_empty.setdefault((u, c), t)
                op, x = mv[t]
                if x == c and op in ('pebble', 'unghost') and b is not None and b < t:
                    ws.append((b, t)); b = None
            if ws:
                W[(u, c)] = ws
    size = lambda u: 2 ** (h - ((u + 1).bit_length() - 1) - 1) - 1
    has = sorted({u for (u, c) in first_empty})
    full = sum(size(u) for u in has)

    def disj(a, b):
        return a[1] <= b[0] or b[1] <= a[0]   # (lo,hi] 同士

    @lru_cache(None)
    def best(x, A):
        ks = kids(x, n)
        if not ks:
            return 0
        opts = [sum(best(k, A) for k in ks)]  # x では選ばない
        if x != 0:
            for c in ks:
                for w in W.get((x, c), []):
                    if all(disj(w, a) for a in A):
                        opts.append(size(x) + sum(best(k, A | frozenset([w])) if k == c else best(k, A) for k in ks))
        return max(opts)
    got = best(0, frozenset())
    name = path.split('/')[-1]
    print(f"{name}: 入れ子にしない締まった窓で選べる要求の最大 {got} / 主張 K の要求 {full}")
    # 最初に空になる子を選ぶ規則
    D = []
    for u in has:
        cs = [(first_empty[(u, c)], c) for c in kids(u, n) if (u, c) in first_empty]
        tau, c = min(cs)
        for v in subtree(c, n):
            D.append((v, tau, rem[u][-1]))
    byv = {}
    for v, lo, hi in D:
        byv.setdefault(v, []).append((lo, hi))
    got2 = 0
    for v, ws in byv.items():
        used = set()
        for lo, hi in sorted(ws, key=lambda w: (w[1], w[0])):
            cand = [t for t in place[v] if lo < t < hi and t not in used]
            if cand:
                used.add(min(cand)); got2 += 1
    print(f"{name}: 「最初に空になる子」規則の頂点ごとマッチング {got2}/{len(D)}")
    bad = [u for u in range(1, n) if 2 * u + 1 < n and u not in has]
    print(f"{name}: 主張 K が成り立たない u = {bad}")

for path, h, cap in [(sys.argv[i], int(sys.argv[i+1]), int(sys.argv[i+2])) for i in range(1, len(sys.argv), 3)]:
    main(path, h, cap)
