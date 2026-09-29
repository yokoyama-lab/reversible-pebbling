"""各頂点 v の置く手のうち，直前の v の置く手（無ければ開始）以後に T(v) が一度ペブルなしになってから置かれたもの（= T(v) の作り直し）の数．
あわせて補題 R の区間族（v 自身と祖先 c の「T(c) 空 → c を置く」）の穿孔数 π(v) の和を，区間が本当に v の置く手を含むかの検査つきで出す．"""
import sys
from common import kids, subtree
from events import prep, empty_at

def anc(v):
    out = []
    while v > 0:
        v = (v - 1) // 2
        out.append(v)
    return out

def main(path, h, cap):
    mv, S, n, place, rem, remop = prep(path, h, cap)
    END = len(mv)
    tot = 0; epi = 0; tot_pi = 0; exc = []
    for v in range(n):
        T = subtree(v, n)
        prev = -1; e = 0
        for s in place[v]:
            if any(empty_at(S, T, t) for t in range(prev, s)):
                e += 1
            else:
                exc.append((v, s))
            prev = s
        epi += e; tot += len(place[v])
        ivs = []
        for c in [v] + anc(v):
            Tc = subtree(c, n); b = -1
            for t in range(END):
                op, x = mv[t]
                if x == c and op in ('pebble', 'unghost') and b is not None:
                    assert any(b < s <= t for s in place[v]), ('補題 R 違反?', v, c, b, t)
                    ivs.append((b, t)); b = None
                if empty_at(S, Tc, t):
                    b = t
        ivs.sort(key=lambda w: w[1]); last = -10; k = 0
        for lo, hi in ivs:
            if lo >= last:
                k += 1; last = hi
        assert k <= len(place[v])
        tot_pi += k
    print(f"{path.split('/')[-1]}: 置く手 {tot}，うち T(v) を空にしてからの置き直し（初回を含む）{epi}，Σπ(v) {tot_pi}；例外 (v, 時刻) {exc}")

for path, h, cap in [(sys.argv[i], int(sys.argv[i+1]), int(sys.argv[i+2])) for i in range(1, len(sys.argv), 3)]:
    main(path, h, cap)
