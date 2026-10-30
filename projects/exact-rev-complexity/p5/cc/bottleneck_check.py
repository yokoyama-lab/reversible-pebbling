"""仮説 BN: 予算の歩み w（各相で ±1）の到達手数ベクトル R_w は，後ろからの最小値の集合 T(w)（0 を除く）だけで決まり，
R_T(X) = min_{Z_1..Z_{r-1}, |Z_i| ≤ v_i} d(∅,Z_1) + d(Z_1,Z_2) + ... + d(Z_{r-1},X)（d は予算なしの最短距離），ただし |X| ≤ v_r。
森（鎖の長さの並び）で無作為の歩みについて直接計算と比べる。"""
import random
import sys
import heapq
INF = 10**6
def mk(lens):
    L = sum(lens)
    need = [0] * L
    s = 0
    for n in lens:
        for j in range(n):
            need[s + j] = 1 << (s + j + 1) if j + 1 < n else 0
        s += n
    return L, need
def relax(E, need, L, B):
    E = list(E)
    h = [(e, x) for x, e in enumerate(E) if e < INF]
    heapq.heapify(h)
    while h:
        e, x = heapq.heappop(h)
        if e > E[x]:
            continue
        for v in range(L):
            if x & need[v] != need[v]:
                continue
            y = x ^ (1 << v)
            if bin(y).count('1') > B or E[y] <= e + 1:
                continue
            E[y] = e + 1
            heapq.heappush(h, (e + 1, y))
    return E
def walk_vec(lens, w):
    L, need = mk(lens)
    N = 1 << L
    D = relax([0] + [INF] * (N - 1), need, L, w[0])
    for b0, b1 in zip(w, w[1:]):
        lim = min(b0, b1)
        D = relax([D[x] if bin(x).count('1') <= lim else INF for x in range(N)], need, L, b1)
    return D
def suffix_min_set(w):
    T, m = set(), INF
    for b in reversed(w):
        m = min(m, b)
        T.add(m)
    T.add(0)  # 始めの ∅ は予算 0 と同じ
    m2, T2 = INF, set()
    for b in reversed([0] + list(w)):
        m2 = min(m2, b)
        T2.add(m2)
    return sorted(v for v in T2 if v > 0)
def bn_vec(lens, T):
    L, need = mk(lens)
    N = 1 << L
    D = relax([0] + [INF] * (N - 1), need, L, L)
    for v in T[:-1]:
        D = relax([D[x] if bin(x).count('1') <= v else INF for x in range(N)], need, L, L)
    return [D[x] if bin(x).count('1') <= T[-1] else INF for x in range(N)]
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
bad = 0
cases = [(5,), (6,), (7,), (2, 3), (2, 4), (3, 4), (2, 5), (1, 2, 3)]
for lens in cases:
    L = sum(lens)
    for trial in range(150):
        n = random.randint(1, 25)
        w = [random.randint(0, L)]
        for _ in range(n):
            w.append(min(L, max(0, w[-1] + random.choice((-1, 1)))))
        if w[-1] == 0:
            continue
        D = walk_vec(lens, w)
        T = suffix_min_set(w)
        B = bn_vec(lens, T)
        m = min(D)
        D = [d - m if d < INF else INF for d in D]
        mb = min(B)
        B = [d - mb if d < INF else INF for d in B]
        if D != B:
            bad += 1
            if bad <= 5:
                print('MISMATCH', lens, w, T)
print('mismatch', bad)
