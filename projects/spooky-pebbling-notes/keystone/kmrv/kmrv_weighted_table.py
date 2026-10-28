# KMRV 表 5・6 の (ℓ, s) に，逐次 cost（Pebble+Unpebble＝mod N 乗算の数）の最小を，重み c∈{0,1,2} と
# 終わり方（round: 終端も外す / tng: 終端は置いてすぐ測定）ごとに並べる．値は kmrv_weighted.py の構成
# （replay で合法性と空間を検査）．c=0・round は Lean の閉じた形と一致（kmrv_formula.Wk）．
import sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from kmrv_weighted import make_dp, replay, work, INF
from kmrv_formula import Wk
ROWS = [(88, 5, 465, 500), (88, 7, None, 370), (88, 12, 175, 295), (82, 5, None, 451), (82, 7, None, 341), (82, 12, 163, 266),
        (79, 5, None, 429), (79, 7, None, 326), (79, 12, 157, 253), (106, 5, None, 652), (106, 7, None, 475), (106, 8, 287, 444),
        (100, 5, None, 600), (100, 7, None, 446), (100, 12, 200, 381), (97, 5, None, 575), (97, 7, None, 432), (97, 12, 193, 345),
        (94, 5, 513, 550), (94, 7, 286, 419), (94, 12, 187, 326)]
DP = {c: make_dp(c) for c in (0, 1, 2)}


def cost(L, s, c, mode):
    total, moves = DP[c]
    T = total(L, s, mode)
    if T == INF: return None
    n, _, sp = replay(L, s, c, moves(L, s, mode), mode); assert n == T and sp <= s
    return work(T, L, mode)


if __name__ == '__main__':
    print('ℓ s | Per run | round c0 c1 c2 | tng c0 c1 c2 | Per/tng_c1 Per/tng_c2')
    for L, s, _, per in ROWS:
        r = [cost(L, s, c, 'round') for c in (0, 1, 2)]; t = [cost(L, s, c, 'tng') for c in (0, 1, 2)]
        assert r[0] == Wk(L, s)
        f = lambda x: '-' if x is None else '%.3f' % (per / x)
        print(L, s, '|', per, '|', *r, '|', *t, '|', f(t[1]), f(t[2]))
    print()
    for s in (2, 3, 4):
        print('s=%d feasible (ℓ=79):' % s, {(c, m): cost(79, s, c, m) for c in (0, 1, 2) for m in ('round', 'tng')})
    print('s=4 tng c=2:', [(L, cost(L, 4, 2, 'tng')) for L in (79, 82, 88, 94, 97, 100, 106)])
