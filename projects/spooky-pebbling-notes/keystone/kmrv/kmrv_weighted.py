# KMRV の鎖の逐次ゲームに「アンシラの重み」を入れた版（arXiv:2510.08432v3 付録 B 末尾，w=2）．
# 重み c（論文に数値が無いので 0・1・2 を並べる）: i ≡ 1 (mod 3) の位置への Pebble(i)・Unpebble(i) は
# 一時値 t の分だけペブル c 個ぶんの空間を余計に使う．Ghost は余計な空間を使わない．
# 空間 = その手の前後どちらかでペブルの位置の数（Def 2.8）＋その手の重み．
# 終わり方 mode:
#   'round': 始状態・終状態とも空（ゴーストも無し），途中で L にペブル（KMRV Def 2.1 そのもの）
#   'tng'  : touch-and-go（4.1 節 項目 2．終端は置いた直後に測定して消える．ゴーストは残らない）
#   bfs(L,s,c,mode): 全手数（Ghost も 1）の最小．全数探索．
#   make_dp(c): 分解 TUG(n,s)=min_k[2k-1+TUP(k,s)+TUG(n-k,s-1)]（Lean の decomp_ug_le）と
#               TUP<=1+TUG（終端を先にゴースト）を位置の重みつきにした構成（上界）．手順も出す．
#   replay: 手順を規則どおりに打ち直して合法性・空間・手数を確かめる（dp とは別の実装）．
# cost（Pebble+Unpebble）の最小 = 全手数の最小/2 + L（round）．非最後の Unpebble を Ghost に替えても制約は緩むだけなので，
# 重みつきでも成り立つ．tng では終端の Unpebble が無いので (全手数の最小 + 1)/2 + L - 1．
import sys
from collections import deque
from functools import lru_cache
sys.setrecursionlimit(1000000)


def weight(c):
    return lambda i: c if i % 3 == 1 else 0   # i は 1..L の大域の位置


def bfs(L, s, c, mode='round'):
    wt = weight(c)
    start = (0, 0, 0); dist = {start: 0}; dq = deque([start]); top = 1 << (L - 1)
    while dq:
        st = dq.popleft(); d = dist[st]; P, G, f = st
        if f and P == 0 and G == 0: return d
        cnt = bin(P).count('1')
        for i in range(L):
            b = 1 << i; prev = (i == 0) or bool(P & (1 << (i - 1))); w = wt(i + 1)
            nxt = []
            if not P & b and prev and cnt + 1 + w <= s:
                if mode == 'tng' and i == L - 1: nxt.append((P, G & ~b, 1))   # 置いてすぐ測定して消える
                else: nxt.append((P | b, G & ~b, 1 if (f or b == top) else 0))
            if P & b and prev and cnt + w <= s: nxt.append((P & ~b, G, f))
            if P & b: nxt.append((P & ~b, G | b, f))
            for k in nxt:
                if k not in dist: dist[k] = d + 1; dq.append(k)
    return None


INF = float('inf')


def make_dp(c):
    wt = weight(c)

    @lru_cache(None)
    def tup(a, n, s):
        # 区間 a+1..a+n．a はペブル（区間の外），a+n にペブル，ほかは空かゴースト → 区間を空に．区間内のペブル数 ≤ s．
        if n == 1:
            return (1, None) if 1 + wt(a + 1) <= s else (INF, None)
        best = (INF, None)
        for k in range(1, n):
            # 掃き: a+1 を置く（区間内 2 個），a+i を置いて a+i-1 をゴースト（区間内 3 個）
            if 2 + wt(a + 1) > s: break
            if any(3 + wt(a + i) > s for i in range(2, k + 1)): continue
            v = 2 * k - 1 + tup(a + k, n - k, s - 1)[0] + tup(a, k, s)[0]
            if v < best[0]: best = (v, k)
        # 終端を先にゴーストにして往復に帰着（Cap2 の形．ゴーストは重みなし）
        v = 1 + tug(a, n, s)[0]
        if v < best[0]: best = (v, 'g')
        return best

    def mk_round(base):
        @lru_cache(None)
        def f(a, n, s):
            # 区間を空から始めて a+n に一度ペブルを置き，空に戻す（base=2: 置いて外す，base=1: 置いて測定）
            if n == 1:
                return (base, None) if 1 + wt(a + 1) <= s else (INF, None)
            best = (INF, None)
            for k in range(1, n):
                if 1 + wt(a + 1) > s: break
                if any(2 + wt(a + i) > s for i in range(2, k + 1)): continue
                v = 2 * k - 1 + f(a + k, n - k, s - 1)[0] + tup(a, k, s)[0]
                if v < best[0]: best = (v, k)
            return best
        return f
    tug = mk_round(2)
    tng = mk_round(1)

    def moves_tup(a, n, s):
        if n == 1: return [('U', a + 1)]
        k = tup(a, n, s)[1]
        if k == 'g': return [('G', a + n)] + moves_r(tug, 2, a, n, s)
        ms = [('P', a + 1)]
        for i in range(2, k + 1): ms += [('P', a + i), ('G', a + i - 1)]
        return ms + moves_tup(a + k, n - k, s - 1) + moves_tup(a, k, s)

    def moves_r(f, base, a, n, s):
        if n == 1: return [('P', a + 1), ('U', a + 1)] if base == 2 else [('P', a + 1)]
        k = f(a, n, s)[1]
        ms = [('P', a + 1)]
        for i in range(2, k + 1): ms += [('P', a + i), ('G', a + i - 1)]
        return ms + moves_r(f, base, a + k, n - k, s - 1) + moves_tup(a, k, s)

    def total(L, s, mode='round'):
        return (tug if mode == 'round' else tng)(0, L, s)[0]

    def moves(L, s, mode='round'):
        return moves_r(tug, 2, 0, L, s) if mode == 'round' else moves_r(tng, 1, 0, L, s)
    return total, moves


def replay(L, s, c, ms, mode='round'):
    """手順を打ち直す．合法なら (全手数, Pebble+Unpebble, 最大空間) を返す．違反なら例外．"""
    wt = weight(c)
    peb = [False] * (L + 1); peb[0] = True; gh = [False] * (L + 1); seen = False; maxsp = 0; cost = 0
    for op, i in ms:
        assert 1 <= i <= L, (op, i)
        cnt = sum(peb[1:])
        if op == 'P':
            assert not peb[i] and peb[i - 1], ('P', i)
            sp = cnt + 1 + wt(i); cost += 1; gh[i] = False
            if i == L: seen = True
            if not (mode == 'tng' and i == L): peb[i] = True
        elif op == 'U':
            assert peb[i] and peb[i - 1], ('U', i); sp = cnt + wt(i); peb[i] = False; cost += 1
        elif op == 'G':
            assert peb[i], ('G', i); sp = cnt; peb[i] = False; gh[i] = True
        else: raise ValueError(op)
        assert sp <= s, ('space', op, i, sp, s)
        maxsp = max(maxsp, sp)
    assert seen and not any(peb[1:]) and not any(gh[1:]), 'final state'
    return len(ms), cost, maxsp


def work(T, L, mode='round'):
    """全手数の最小 T から cost（Pebble+Unpebble）の最小へ．"""
    if mode == 'round':
        assert T % 2 == 0; return T // 2 + L
    assert T % 2 == 1; return (T + 1) // 2 + L - 1


if __name__ == '__main__':
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    sys.path.insert(0, __file__.rsplit('/', 1)[0])
    from kmrv_formula import tug as tug_formula
    total0, _ = make_dp(0)
    bad = sum(total0(n, s) != tug_formula(n, s) for n in range(2, 60) for s in range(2, 9))
    print('c=0 round: dp vs closed form (2<=n<60, 2<=s<=8): bad =', bad)
    for c in (0, 1, 2):
        for mode in ('round', 'tng'):
            total, moves = make_dp(c); bad = 0; n_ok = 0
            for L in range(1, Lmax + 1):
                for s in range(1, 8):
                    b = bfs(L, s, c, mode); d = total(L, s, mode)
                    if d != INF:
                        n_, _, sp_ = replay(L, s, c, moves(L, s, mode), mode); assert n_ == d and sp_ <= s
                    ok = (b is None and d == INF) or b == d; bad += not ok; n_ok += ok
                    if not ok: print('MISMATCH c=%d %s L=%d s=%d bfs=%s dp=%s' % (c, mode, L, s, b, d))
            print('c=%d %-5s dp vs BFS (L<=%d, 1<=s<=7): ok %d, bad %d' % (c, mode, Lmax, n_ok, bad))
