"""子の選択を最適化した最大マッチング（木の DP で厳密）．
頂点 v への要求は祖先 u のうち選ばれた子 c_u が v の祖先か v 自身であるものから来る．
頂点ごとのマッチングは独立なので，部分木 T(x) の最適値は「T(x) を覆う選択をした祖先の集合 A」だけで決まる．"""
import sys
from functools import lru_cache
from common import kids, subtree
from events import prep, empty_at

def vertex_match(v, wins, place):
    """v の置く手を区間 wins=[(lo,hi)] に互いに異なるように割り当てる最大数（右端昇順の貪欲）．"""
    used = set(); got = 0
    for lo, hi in sorted(wins, key=lambda w: (w[1], w[0])):
        cand = [t for t in place[v] if lo < t < hi and t not in used]
        if cand:
            used.add(min(cand)); got += 1
    return got

def run(path, h, cap, lo_rule='window', hi_rule='f'):
    mv, S, n, place, rem, remop = prep(path, h, cap)
    END = len(mv)
    win = {}  # (u,c) -> (lo,hi)
    for u in range(1, n):
        if 2 * u + 1 >= n:
            continue
        t0, f = place[u][0], rem[u][-1]
        for c in kids(u, n):
            T = subtree(c, n)
            if lo_rule == 'window':
                cand = [t for t in range(t0 + 1, f) if empty_at(S, T, t)]
            else:
                cand = [t for t in range(place[c][0] + 1, f) if empty_at(S, T, t)]
            if cand:
                win[(u, c)] = (min(cand), END if hi_rule == 'end' else f)
    has = {u for (u, c) in win}
    total = sum(2 ** (h - ((u + 1).bit_length() - 1) - 1) - 1 for u in has)

    @lru_cache(None)
    def best(x, A):
        # A: 祖先側から x を覆う要求の窓の組（frozenset of (u,c)）
        own = vertex_match(x, [win[a] for a in A], place)
        ks = kids(x, n)
        if not ks:
            return own
        opts = []
        if x in has and x != 0:
            for c in ks:
                if (x, c) in win:
                    opts.append(own + sum(best(k, A | frozenset([(x, c)]) if k == c else A) for k in ks))
        else:
            opts.append(own + sum(best(k, A) for k in ks))
        return max(opts)
    got = best(0, frozenset())
    print(f"{path.split('/')[-1]} h={h} lo={lo_rule} hi={hi_rule}: 子の選択を最適化した最大 {got}/{total}")

if __name__ == '__main__':
    for path, h, cap in [(sys.argv[i], int(sys.argv[i+1]), int(sys.argv[i+2])) for i in range(1, len(sys.argv), 3)]:
        for lo in ('window', 'after_c_first'):
            for hi in ('f', 'end'):
                run(path, h, cap, lo, hi)
