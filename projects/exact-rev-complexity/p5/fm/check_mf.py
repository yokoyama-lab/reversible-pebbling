#!/usr/bin/env python3
"""M（幅優先探索 bfs_m.c）と F（ftree.py）を全根付き木で突き合わせる.

使い方:
  python3 check_mf.py gen  --nmin 11 --nmax 13 [--maxdeg 2] > trees.txt   # 木を列挙（個数を OEIS で自己検査）
  ./bfs_m < trees.txt > m.txt                                              # 全数探索（分割して並列でもよい）
  python3 check_mf.py cmp trees.txt m.txt                                  # 突き合わせ
"""

from __future__ import annotations

import argparse
import sys

import ftree as ft


def from_parents(par: list[int]) -> int:
    n = len(par)
    kids: list[list[int]] = [[] for _ in range(n)]
    for i in range(1, n):
        kids[par[i]].append(i)

    def build(v: int) -> int:
        return ft.node([build(c) for c in kids[v]])

    return build(0)


def cmd_gen(a):
    by = ft.enumerate_trees(a.nmax, a.maxdeg)
    ref = ft.A000081 if a.maxdeg is None else (ft.A001190s if a.maxdeg == 2 else None)
    tid = 0
    for n in range(1, a.nmax + 1):
        if ref is not None:
            assert len(by[n]) == ref[n - 1], (n, len(by[n]), ref[n - 1])
        if n < a.nmin:
            continue
        for g in by[n]:
            par = ft.parents(g)
            assert from_parents(par) == g
            print(tid, n, *par[1:])
            tid += 1
    print(f"# generated {tid} trees, n in [{a.nmin},{a.nmax}], maxdeg={a.maxdeg}", file=sys.stderr)


def cmd_cmp(a):
    trees = {}
    with open(a.trees) as f:
        for line in f:
            xs = list(map(int, line.split()))
            tid, n, par = xs[0], xs[1], [-1] + xs[2:]
            trees[tid] = (n, par)
    seen = set()
    pts = mism = above = 0
    first = []
    nmin = nmax = None
    with open(a.m) as f:
        for line in f:
            xs = list(map(int, line.split()))
            tid, n, ms = xs[0], xs[1], xs[2:]
            assert trees[tid][0] == n and len(ms) == n
            seen.add(tid)
            g = from_parents(trees[tid][1])
            nmin = n if nmin is None else min(nmin, n)
            nmax = n if nmax is None else max(nmax, n)
            for S in range(1, n + 1):
                fv = ft.F(g, S)
                mv = ms[S - 1]
                mv = ft.INF if mv < 0 else mv
                pts += 1
                if mv > fv:
                    above += 1  # M > F は F が構成（上界）であることに反する
                if mv != fv:
                    mism += 1
                    if len(first) < 10:
                        first.append((tid, n, ft.show(g), S, fv, mv))
    missing = set(trees) - seen
    print(f"trees in file {len(trees)}, compared {len(seen)}, missing {len(missing)}, n in [{nmin},{nmax}]")
    print(f"(tree,S) points {pts}, mismatches F!=M {mism}, of which M>F {above}")
    for x in first:
        print("  mismatch (id,n,shape,S,F,M):", x)
    return 0 if (mism == 0 and not missing) else 1


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    g = sub.add_parser("gen")
    g.add_argument("--nmin", type=int, default=1)
    g.add_argument("--nmax", type=int, required=True)
    g.add_argument("--maxdeg", type=int, default=None)
    c = sub.add_parser("cmp")
    c.add_argument("trees")
    c.add_argument("m")
    a = ap.parse_args()
    if a.cmd == "gen":
        cmd_gen(a)
    else:
        sys.exit(cmd_cmp(a))


if __name__ == "__main__":
    main()
