"""二重計上の無い版の検定．
v のエピソード = v の置く手 s のうち，直前の v の置く手より後に T(v) が一度ペブルなしになったもの．区間 (b,s]（b = s 前で T(v) が空の最後の時刻）．
X'(a) = a のエピソードのうち，親 p のどのエピソードにも含まれないものの数．
主張: 置く手 >= Σ_v E(v) >= n + Σ_{a≠根} X'(a)|T(a)|（補題 R だけから出る．証明は報告に書いた素描）．
主張 K': u の子 c で X'(c) >= 1 のものがある．"""
import sys
from common import kids, subtree
from events import prep, empty_at

def episodes(v, S, n, place):
    T = subtree(v, n); out = []; prev = -1
    for s in place[v]:
        emp = [t for t in range(prev, s) if empty_at(S, T, t)]
        if emp:
            out.append((max(emp), s))
        prev = s
    return out

def main(path, h, cap):
    mv, S, n, place, rem, remop = prep(path, h, cap)
    ep = {v: episodes(v, S, n, place) for v in range(n)}
    X = {}
    for a in range(1, n):
        p = (a - 1) // 2
        X[a] = sum(1 for (b, s) in ep[a] if not any(bp <= b and s < sp for (bp, sp) in ep[p]))
        assert len(ep[a]) >= len(ep[p]) + X[a], (a, len(ep[a]), len(ep[p]), X[a])
    npl = sum(len(place[v]) for v in range(n))
    E = sum(len(ep[v]) for v in range(n))
    bound = n + sum(X[a] * len(subtree(a, n)) for a in X)
    print(f"{path.split('/')[-1]}: 置く手 {npl}，ΣE(v) {E}，下界 n+ΣX'|T| = {bound}")
    byh = {}; byhK = {}
    for u in range(0, n):
        if 2 * u + 1 >= n: continue
        k = h - ((u + 1).bit_length() - 1)
        byh.setdefault(k, []).append(sum(1 for c in kids(u, n) if X[c] >= 1))
    print("  主張 K'（X'>=1 の子の数ごとの u の数，高さ別）", {k: {i: v.count(i) for i in (0, 1, 2)} for k, v in sorted(byh.items())})
    xs = {}
    for a in X:
        k = h - ((a + 1).bit_length() - 1)
        xs.setdefault(k, []).append(X[a])
    print("  高さ別の X'(a) の和 / 頂点数", {k: f"{sum(v)}/{len(v)}" for k, v in sorted(xs.items())})

for path, h, cap in [(sys.argv[i], int(sys.argv[i+1]), int(sys.argv[i+2])) for i in range(1, len(sys.argv), 3)]:
    main(path, h, cap)
