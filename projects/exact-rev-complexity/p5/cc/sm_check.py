#!/usr/bin/env python3
"""予想 SM（文脈つきの「くも → 道」の単調性）を，p5/fm の全数探索の M の表で確かめる.

SM: 木 G の頂点 u の部分木 G_u が「くも」（u 以外の頂点は子が高々 1 個）で u の子が 2 個以上のとき，
G_u を同じ頂点数の道（u の位置に頂を置く）に置き換えた木 G' について，すべての S で M(G,S) >= M(G',S)．
SM が成り立てば CC が従う（いちばん下の分岐頂点の部分木はくもなので，置き換えを繰り返すと道に着き，
M は増えない）．

さらに強い版 SUB（任意の部分木 G_u を道に置き換えても M は増えない）も同時に数える．
入力: 木の列（"id n p_1 ... p_{n-1}"）と M の表（"id n M(1) ... M(n)"，-1 は ∞）．
"""
from __future__ import annotations

import sys


def canon(par):
    n = len(par)
    ch = [[] for _ in range(n)]
    for v in range(1, n):
        ch[par[v]].append(v)
    memo = {}

    def enc(v):
        if v in memo:
            return memo[v]
        s = "(" + "".join(sorted(enc(c) for c in ch[v])) + ")"
        memo[v] = s
        return s

    import sys as _s
    _s.setrecursionlimit(10000)
    return enc(0), ch


def build_from_canon(s):
    """括弧列から親の配列（頂点 0 が根）."""
    par = []
    stack = []
    for ch_ in s:
        if ch_ == "(":
            par.append(stack[-1] if stack else -1)
            stack.append(len(par) - 1)
        else:
            stack.pop()
    return par


def main(tree_paths, m_paths):
    # 木の id は各ファイルで振り直されているので，ファイルの組で対応を取る
    by_canon = {}
    for tp, mp in zip(tree_paths, m_paths):
        mt = {}
        for line in open(mp):
            xs = line.split()
            if xs and not xs[0].startswith("#"):
                mt[xs[0]] = [int(x) for x in xs[2:]]
        for line in open(tp):
            xs = line.split()
            if not xs:
                continue
            n = int(xs[1])
            par = [-1] + [int(x) for x in xs[2:]]
            c, _ = canon(par)
            by_canon[c] = mt[xs[0]]
    print(f"表の木の数 {len(by_canon)}")
    pts = viol_sm = viol_sub = cases_sm = cases_sub = 0
    shown = 0
    for c, ms in by_canon.items():
        par = build_from_canon(c)
        n = len(par)
        ch = [[] for _ in range(n)]
        for v in range(1, n):
            ch[par[v]].append(v)
        # 部分木の大きさと「くもか」
        size = [1] * n
        spider = [True] * n  # u の下（u を除く）の頂点がすべて子 <= 1
        for v in range(n - 1, -1, -1):
            for w in ch[v]:
                size[v] += size[w]
                spider[v] = spider[v] and spider[w] and len(ch[w]) <= 1
        for u in range(n):
            if len(ch[u]) < 2:
                continue
            # u の部分木を道に置き換える: 括弧列で u の部分を "(((...)))" に
            # 置換は親配列で行う
            sub = set()
            stack = [u]
            while stack:
                x = stack.pop()
                sub.add(x)
                stack.extend(ch[x])
            keep = [v for v in range(n) if v not in sub or v == u]
            newpar = {}
            for v in keep:
                newpar[v] = par[v]
            # 道: u, 新頂点 k1..k_{size-1}，ki の親は k_{i-1}
            nid = n
            prev = u
            extra = []
            for _ in range(size[u] - 1 + MUT):
                newpar[nid] = prev
                extra.append(nid)
                prev = nid
                nid += 1
            verts = keep + extra
            ren = {v: i for i, v in enumerate(sorted(verts, key=lambda x: (x != 0, x)))}
            p2 = [-1] * len(verts)
            for v in verts:
                if v != 0:
                    p2[ren[v]] = ren[newpar[v]]
            c2, _ = canon(p2)
            ms2 = by_canon.get(c2)
            if ms2 is None:
                continue
            bad = False
            for S in range(1, n + 1):
                a, b = ms[S - 1], ms2[S - 1]
                a = float("inf") if a < 0 else a
                b = float("inf") if b < 0 else b
                pts += 1
                if a < b:
                    bad = True
                    if shown < 10:
                        print(f"破れ: G={c} u={u}（くも={spider[u]}，|G_u|={size[u]}） S={S} M(G)={a} M(G')={b}")
                        shown += 1
            cases_sub += 1
            viol_sub += bad
            if spider[u]:
                cases_sm += 1
                viol_sm += bad
    print(f"SUB: 置き換え {cases_sub} 件，破れ {viol_sub} 件 | SM（くもだけ）: {cases_sm} 件，破れ {viol_sm} 件 | 点 {pts}")


MUT = 0  # 変異: SM_MUTANT=1 なら道を 1 頂点長くする（破れが出るべき）

if __name__ == "__main__":
    import os
    MUT = int(os.environ.get("SM_MUTANT", "0"))
    a = sys.argv[1:]
    half = len(a) // 2
    main(a[:half], a[half:])
