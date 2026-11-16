#!/usr/bin/env python3
"""lip_sat.py が出力した写像 ψ を，SAT の符号化とは独立に検査する.

入力: 行ごとに「A Z」（A は木の配置のビット集合．頂点番号は括弧表記の出現順で 0 が根．Z は鎖の配置．
ビット i がセル i+1）．
検査（--space S のとき）:
  (1) ψ(∅) = ∅,  (2) ψ({根}) = {先端},  (3) |A| <= S の全 A で |ψ(A)| <= S,
  (4) |A|,|A'| <= S の合法な木の 1 手 A -> A' について，ψ(A) = ψ(A') か鎖の合法な 1 手で移り合う．
これが成り立てば，木の S 個以下の手順は同じ手数以下の鎖の S 個以下の手順に写るので
M(木,S) >= Fc(|木|,S)．さらに両側を幅優先探索で数えて，その不等式を直接確かめる．
"""

from __future__ import annotations

import argparse
import sys
from collections import deque

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from chain import Row  # noqa: E402
from lip_sat import parse  # noqa: E402


def bfs(start, goal, moves, S):
    dist = {start: 0}
    q = deque([start])
    while q:
        x = q.popleft()
        if x == goal:
            return dist[x]
        for y in moves(x):
            if bin(y).count("1") <= S and y not in dist:
                dist[y] = dist[x] + 1
                q.append(y)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tree")
    ap.add_argument("mapfile")
    ap.add_argument("--space", type=int, required=True)
    a = ap.parse_args()
    ch = parse(a.tree)
    n = len(ch)
    S = a.space
    need = [sum(1 << c for c in ch[v]) for v in range(n)]
    psi = {}
    for line in open(a.mapfile):
        A, Z = map(int, line.split())
        psi[A] = Z

    def tmoves(A):
        return [A ^ (1 << v) for v in range(n) if (A & need[v]) == need[v]]

    def cmoves(Z):
        return [Z ^ (1 << i) for i in range(n) if i == 0 or (Z >> (i - 1)) & 1]

    dom = [A for A in range(1 << n) if bin(A).count("1") <= S]
    ok = True
    ok &= psi.get(0) == 0
    ok &= psi.get(1) == 1 << (n - 1)
    bad_w = sum(1 for A in dom if bin(psi[A]).count("1") > S)
    bad_e = 0
    edges = 0
    for A in dom:
        for A2 in tmoves(A):
            if bin(A2).count("1") > S:
                continue
            edges += 1
            z, z2 = psi[A], psi[A2]
            if z != z2 and z2 not in cmoves(z):
                bad_e += 1
    print(f"定義域 {len(dom)} 配置，木の手 {edges}（向きつき），重さの破れ {bad_w}，Lipschitz の破れ {bad_e}，"
          f"端点 {'ok' if ok else 'NG'}")
    mt = bfs(0, 1, tmoves, S)
    mc = bfs(0, 1 << (n - 1), cmoves, S)
    print(f"M(木,{S}) = {mt}（BFS），Fc({n},{S}) = {mc}（鎖の BFS），{Row.Fc(n, S)}（再帰）")
    good = ok and bad_w == 0 and bad_e == 0 and mc == Row.Fc(n, S) and (mt is None or mt >= mc)
    print("写像は条件を満たす" if good else "写像は条件を満たさない")
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
