#!/usr/bin/env python3
"""2CM(a,b) を「すべての長さの予算の列と境目」について示す有限の証明書（先読みあり＝最適値どうしの比較）.

2 本の問題と 1 本の問題の動的計画法のベクトルを同時に進める:
  D2(x) = 2 本の鎖が盤 x にいる最小手数，DM(y) = 1 本の鎖が盤 y にいる最小手数．
1 つの相（予算 β）は両方に min-plus の作用 D <- D ⊗ dist_β をかけ，境目は頂を含まない盤を ∞ にする．
どの時点で終わってもよいので，到達しうるすべての組で DM(∅) <= D2(∅) なら 2CM(a,b) が成り立つ．
組を「D2 の有限な値の最小」を引いて正規化すると，到達しうる組は有限になる（とは限らないので上限 K で打ち切る）．
DM の値を上げる方向の丸め（-K 未満を -K に，K 超を ∞ に）は味方に不利なだけなので，丸めた上で勝てば証明になる．
丸めが起きたかどうかも数える．

使い方: python3 closure.py a b [K]
"""
from __future__ import annotations

import sys
from collections import deque

INF = 10 ** 9


def graphs(a, b):
    L = a + b
    need2 = [(1 << (i + 1)) if i + 1 < a else 0 for i in range(a)] + \
            [(1 << (a + i + 1)) if i + 1 < b else 0 for i in range(b)]
    needM = [(1 << (i + 1)) if i + 1 < L else 0 for i in range(L)]
    return L, need2, (1 | (1 << a)), needM, 1


def apsp(L, need, B):
    N = 1 << L
    out = []
    for s in range(N):
        d = [INF] * N
        if bin(s).count("1") <= B:
            d[s] = 0
            q = deque([s])
            while q:
                x = q.popleft()
                pc = bin(x).count("1")
                for v in range(L):
                    if x & need[v] != need[v]:
                        continue
                    if not (x >> v) & 1 and pc + 1 > B:
                        continue
                    y = x ^ (1 << v)
                    if d[y] == INF:
                        d[y] = d[x] + 1
                        q.append(y)
        out.append(d)
    return out


def step(D, dist, mask, N):
    E = [INF] * N
    for y in range(N):
        if D[y] >= INF:
            continue
        dy = dist[y]
        base = D[y]
        for x in range(N):
            if dy[x] < INF:
                v = base + dy[x]
                if v < E[x]:
                    E[x] = v
    if mask is not None:
        for x in range(N):
            if x & mask != mask:
                E[x] = INF
    return E


def main(a, b, K):
    L, need2, tops2, needM, topM = graphs(a, b)
    N = 1 << L
    d2 = [apsp(L, need2, B) for B in range(L + 1)]
    dM = [apsp(L, needM, B) for B in range(L + 1)]
    start = (tuple([0] + [INF] * (N - 1)), tuple([0] + [INF] * (N - 1)))
    seen = {start}
    q = deque([start])
    rounded = 0
    worst = -INF
    while q:
        D2, DM = q.popleft()
        for B in range(L + 1):
            for chk in (False, True):
                E2 = step(D2, d2[B], tops2 if chk else None, N)
                EM = step(DM, dM[B], topM if chk else None, N)
                fin = [v for v in E2 if v < INF]
                if not fin:
                    continue  # 2 本の側が実行不能な列
                m = min(fin)
                E2 = tuple(v - m if v < INF else INF for v in E2)
                EMl = []
                for v in EM:
                    if v >= INF:
                        EMl.append(INF)
                        continue
                    w = v - m
                    if w < -K:
                        w = -K
                        rounded += 1
                    elif w > K:
                        w = INF
                        rounded += 1
                    EMl.append(w)
                EM = tuple(EMl)
                # 終わりの判定: 2 本が ∅ にいられるなら 1 本も同じ以下で ∅ にいる
                if E2[0] < INF:
                    gap = EM[0] - E2[0] if EM[0] < INF else INF
                    worst = max(worst, gap)
                    if gap > 0:
                        print(f"破れ（丸めを含むかもしれない）: a={a} b={b} gap={gap}")
                        return False
                st = (E2, EM)
                if st not in seen:
                    seen.add(st)
                    q.append(st)
                    if len(seen) > 2_000_000:
                        print("状態が多すぎる（打ち切り．結果ではない）")
                        return None
    print(f"a={a} b={b} K={K}: 到達しうる正規化された組 {len(seen)} 個で閉じた．"
          f"DM(∅) − D2(∅) の最大 {worst}（<= 0 なら 2CM(a,b) が成り立つ．計算機援用の決定）．丸めの回数 {rounded}")
    return worst <= 0


if __name__ == "__main__":
    a, b = int(sys.argv[1]), int(sys.argv[2])
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 64
    main(a, b, K)
