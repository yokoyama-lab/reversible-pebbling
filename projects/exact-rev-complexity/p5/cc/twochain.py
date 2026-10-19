#!/usr/bin/env python3
"""2 本の鎖の併合の補題 2CM を，時間とともに変わる予算と「頂がある」時刻の制約の下で確かめる.

文脈（木の残り）から見た脚の問題: 時刻は文脈の出来事で区切られた相 j = 0..J に分かれ，相 j では
脚に使えるペブルが β_j 個以下（S − 文脈のペブル数）．相 j と j+1 の境目が u の手なら，その瞬間に
脚の頂にペブルが要る（2 本なら両方の頂，併合した 1 本なら頂だけ）．初めと終わりは脚が空．
  OPT_two(a,b)   : 長さ a と b の独立な 2 本の鎖（底は自由）の手数の和の最小
  OPT_merged(a,b): 長さ a+b の 1 本の鎖（上の a 個が元の A，下の b 個が元の B）の手数の最小
2CM: OPT_merged(a,b) <= OPT_two(a,b)．
これが任意の予算の列と境目の集合で成り立てば，文脈つきの脚の併合（move_check.py の legmerge）が従い，
くもを道に直す操作を繰り返して CC が従う（PROOF.md §3 定理 R）．

鎖の頂点は 0 が頂，len-1 が底（底の葉は自由．頂点 i の手は i+1 がペブル済み（または i が底）のとき合法）．
"""
from __future__ import annotations

import random
import sys
from collections import deque

INF = float("inf")


def graph_two(a, b):
    """状態 = (A のビット) | (B のビット) << a．各頂点の要求マスク．"""
    need = []
    for i in range(a):
        need.append(1 << (i + 1) if i + 1 < a else 0)
    for i in range(b):
        need.append(1 << (a + i + 1) if i + 1 < b else 0)
    tops = (1 << 0) | (1 << a) if b > 0 else 1
    return a + b, need, tops


def graph_merged(a, b):
    L = a + b
    need = [1 << (i + 1) if i + 1 < L else 0 for i in range(L)]
    return L, need, 1


def apsp(L, need, B):
    """予算 B での全点対の距離（辞書の辞書ではなくリストのリスト）."""
    N = 1 << L
    dist = []
    for s in range(N):
        if bin(s).count("1") > B:
            dist.append(None)
            continue
        d = [INF] * N
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
        dist.append(d)
    return dist


_cache = {}


def opt(kind, a, b, budgets, checks):
    """budgets[j] は相 j の予算，checks[j] が真なら相 j の終わり（j+1 の初め）に頂が要る."""
    L, need, tops = graph_two(a, b) if kind == "two" else graph_merged(a, b)
    N = 1 << L
    D = [INF] * N
    D[0] = 0
    for j, B in enumerate(budgets):
        key = (kind, a, b, B)
        if key not in _cache:
            _cache[key] = apsp(L, need, B)
        dist = _cache[key]
        E = [INF] * N
        for y in range(N):
            if D[y] == INF or dist[y] is None:
                continue
            dy = dist[y]
            for x in range(N):
                v = D[y] + dy[x]
                if v < E[x]:
                    E[x] = v
        if j < len(budgets) - 1 and checks[j]:
            for x in range(N):
                if x & tops != tops:
                    E[x] = INF
        D = E
    return D[0]


def random_profile(rng, L, J, step1=True):
    budgets = []
    b = rng.randint(1, L)
    for _ in range(J):
        budgets.append(b)
        if step1:
            b = max(0, min(L, b + rng.choice((-1, 0, 1))))
        else:
            b = rng.randint(0, L)
    checks = [rng.random() < 0.4 for _ in range(J - 1)]
    if not any(checks):
        checks[rng.randrange(J - 1)] = True
    return budgets, checks


def main(trials=2000, maxlen=6, seed=1, step1=True):
    rng = random.Random(seed)
    bad = 0
    done = 0
    for t in range(trials):
        a = rng.randint(1, maxlen - 1)
        b = rng.randint(1, maxlen - a)
        J = rng.randint(2, 9)
        budgets, checks = random_profile(rng, a + b, J, step1)
        o2 = opt("two", a, b, budgets, checks)
        om = opt("merged", a, b, budgets, checks)
        done += 1
        if om > o2:
            bad += 1
            if bad <= 8:
                print(f"破れ a={a} b={b} 予算={budgets} 境目={[int(c) for c in checks]} two={o2} merged={om}")
    print(f"試行 {done}，破れ {bad}（maxlen={maxlen}，step1={step1}）")
    return bad


if __name__ == "__main__":
    args = sys.argv[1:]
    trials = int(args[0]) if args else 2000
    maxlen = int(args[1]) if len(args) > 1 else 6
    step1 = (args[2] != "0") if len(args) > 2 else True
    main(trials, maxlen, 1, step1)


def exhaustive(maxL=5, maxJ=5):
    """a+b <= maxL，相の数 <= maxJ，予算 0..L，境目の全部分集合を総当たり."""
    import itertools
    bad = tot = 0
    mut = 0
    for L in range(2, maxL + 1):
        for a in range(1, L):
            b = L - a
            for J in range(2, maxJ + 1):
                for budgets in itertools.product(range(0, L + 1), repeat=J):
                    for checks in itertools.product((False, True), repeat=J - 1):
                        if not any(checks):
                            continue
                        o2 = opt("two", a, b, list(budgets), list(checks))
                        if o2 == INF:
                            continue
                        om = opt("merged", a, b, list(budgets), list(checks))
                        tot += 1
                        if om > o2:
                            bad += 1
                            if bad <= 5:
                                print(f"破れ a={a} b={b} 予算={budgets} 境目={checks} two={o2} merged={om}")
                        # 変異: 併合側の予算を 1 減らす（破れが出るべき）
                        if b >= 1:
                            mm = opt("merged", a, b, [max(0, x - 1) for x in budgets], list(checks))
                            if mm > o2:
                                mut += 1
    print(f"総当たり: 有限の点 {tot}，破れ {bad}，変異（併合側の予算 -1）で検出 {mut}")
    return bad
