"""h=6 の未充足 3 件の中身，最小の多重度 b，補題 R が強制する置く手の数 Σπ(v)．"""
import sys
from common import kids, subtree
from events import prep, empty_at

path, h, cap = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
mv, S, n, place, rem, remop = prep(path, h, cap)
END = len(mv)
def anc(v):
    out = []
    while v > 0:
        v = (v - 1) // 2; out.append(v)
    return out
win = {}
for u in range(1, n):
    if 2 * u + 1 >= n: continue
    t0, f = place[u][0], rem[u][-1]
    for c in kids(u, n):
        T = subtree(c, n)
        cand = [t for t in range(t0 + 1, f) if empty_at(S, T, t)]
        if cand: win[(u, c)] = (min(cand), f, t0)
if len(sys.argv) > 4:
    for v in map(int, sys.argv[4].split(',')):
        print(f"v={v} 置く手 {place[v]} 除去 {rem[v]}")
        for u in anc(v):
            for c in kids(u, n):
                if (u, c) in win and v in subtree(c, n):
                    lo, hi, t0 = win[(u, c)]
                    print(f"   u={u}(初回配置 {t0}, 最後の除去 {hi}) 子 c={c}: τ={lo}  窓内の v の置く手 {[t for t in place[v] if lo < t < hi]}")
# 補題 R の区間族と穿孔数 π(v)
tot_pi = 0; rows = []
for v in range(n):
    ivs = []
    for c in [v] + anc(v):
        T = subtree(c, n)
        prev_empty = True; b = -1  # 時刻 -1 = 初期状態（空）
        for t in range(END):
            e = empty_at(S, T, t)
            op, x = mv[t]
            if x == c and op in ('pebble', 'unghost') and b is not None:
                ivs.append((b, t))  # v は (b, t] に置かれる
                b = None
            if e:
                b = t
        # b is None: 直前の空の区間は既に使った
    ivs.sort(key=lambda w: w[1])
    last = -10; k = 0
    for lo, hi in ivs:
        if lo >= last:  # (lo,hi] が前に選んだ区間と交わらない（整数の手の番号で）
            k += 1; last = hi
    tot_pi += k; rows.append((v, k, len(place[v])))
npl = sum(len(place[v]) for v in range(n))
print(f"{path.split('/')[-1]}: 置く手 {npl}，補題 R が強制する置く手の下界 Σπ(v) = {tot_pi}，n = {n}，n+事象の要求 = {n}+{sum(2**(h-((u+1).bit_length()-1)-1)-1 for u in {u for (u,c) in win})}")
bad = [(v, k, p) for v, k, p in rows if k < p]
print(f"  π(v) < 置き回数 の頂点 {len(bad)}/{n}: {bad[:20]}")
