#!/usr/bin/env python3
"""局所的な木の操作で M が増えないか（文脈つきの単調性）を，全数探索の M の表で確かめる.

操作（どれも頂点数を保ち，木を道に近づける）:
  leafany   葉 ℓ（親の子が 2 個以上）を外し，別の葉 ℓ' の子にする（ℓ' は任意）
  leafsib   同上．ただし ℓ' は ℓ の兄弟の部分木の葉
  legmerge  くもの頂点 u（u の下はすべて子 <= 1）の 2 本の脚 a, b を 1 本の脚（長さ a+b）にする
  legmerge2 同上．ただし u の他の子の部分木は任意（u の子のうち道であるもの 2 本を併合）
  sub       任意の頂点 u の部分木を同じ頂点数の道にする（sm_check.py と同じ）
各操作について，「すべての選び方で単調」（∀）と，「分岐のある木ごとに単調な選び方が 1 つはある」（∃）を数える．
入力: 木の列と M の表（p5/fm の形式）を同じ順に．
"""
from __future__ import annotations


import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from sm_check import canon, build_from_canon  # noqa: E402

INF = float("inf")


def load(tree_paths, m_paths):
    by = {}
    for tp, mp in zip(tree_paths, m_paths):
        mt = {}
        for line in open(mp):
            xs = line.split()
            if xs and not xs[0].startswith("#"):
                mt[xs[0]] = [INF if int(x) < 0 else int(x) for x in xs[2:]]
        for line in open(tp):
            xs = line.split()
            if xs:
                par = [-1] + [int(x) for x in xs[2:]]
                by[canon(par)[0]] = mt[xs[0]]
    return by


def kids(par):
    ch = [[] for _ in par]
    for v in range(1, len(par)):
        ch[par[v]].append(v)
    return ch


def subtree(ch, u):
    out, st = [], [u]
    while st:
        x = st.pop()
        out.append(x)
        st.extend(ch[x])
    return out


def reparent(par, v, newp):
    p = list(par)
    p[v] = newp
    return p


def moves(par, op):
    n = len(par)
    ch = kids(par)
    leaves = [v for v in range(n) if not ch[v]]
    if op in ("leafany", "leafsib"):
        for l in leaves:
            if l == 0:
                continue
            u = par[l]
            if len(ch[u]) < 2:
                continue
            if op == "leafany":
                targets = [x for x in leaves if x != l]
            else:
                targets = []
                for s in ch[u]:
                    if s != l:
                        targets += [x for x in subtree(ch, s) if not ch[x]]
            for t in targets:
                yield (l, t), reparent(par, l, t)
    elif op in ("legmerge", "legmerge2"):
        for u in range(n):
            if len(ch[u]) < 2:
                continue
            pathkids = [c for c in ch[u] if all(len(ch[x]) <= 1 for x in subtree(ch, c))]
            if op == "legmerge" and len(pathkids) != len(ch[u]):
                continue
            legs = []
            for c in pathkids:
                path = [c]
                while ch[path[-1]]:
                    path.append(ch[path[-1]][0])
                legs.append(path)
            for i in range(len(legs)):
                for j in range(len(legs)):
                    if i == j:
                        continue
                    # 脚 j の頂を脚 i の底の子にする
                    yield (u, i, j), reparent(par, legs[j][0], legs[i][-1])
    elif op in ("legtransfer", "legtransfer_up", "legtransfer_down"):
        # u の道の子 2 本（脚 i, j）．脚 j の底の葉を脚 i の底の子にする（長さ (li, lj) -> (li+1, lj-1)）
        # _up: li >= lj のときだけ（長い脚へ移す），_down: li < lj のときだけ
        for u in range(n):
            pathkids = [c for c in ch[u] if all(len(ch[x]) <= 1 for x in subtree(ch, c))]
            legs = []
            for c in pathkids:
                path = [c]
                while ch[path[-1]]:
                    path.append(ch[path[-1]][0])
                legs.append(path)
            for i in range(len(legs)):
                for j in range(len(legs)):
                    if i == j:
                        continue
                    li, lj = len(legs[i]), len(legs[j])
                    if op == "legtransfer_up" and li < lj:
                        continue
                    if op == "legtransfer_down" and li >= lj:
                        continue
                    yield (u, li, lj), reparent(par, legs[j][-1], legs[i][-1])
    elif op == "pushleg":
        # u の道の子 t, c（どちらも脚）．c を t の子にする（脚の併合を 1 段ずつ行う最初の段）
        for u in range(n):
            pk = [c for c in ch[u] if all(len(ch[x]) <= 1 for x in subtree(ch, c))]
            for t in pk:
                for c in pk:
                    if c != t:
                        yield (u, t, c, len(subtree(ch, t)), len(subtree(ch, c))), reparent(par, c, t)
    elif op in ("push", "push_tpath", "push_tleaf1"):
        # u の子 t, c（t != c）．c を t の子にする（分岐点を 1 段下げる）．
        # push_tpath: t の部分木が道のときだけ．push_tleaf1: t の子がちょうど 1 個のときだけ
        for u in range(n):
            if len(ch[u]) < 2:
                continue
            for t in ch[u]:
                if op == "push_tpath" and not all(len(ch[x]) <= 1 for x in subtree(ch, t)):
                    continue
                if op == "push_tleaf1" and len(ch[t]) != 1:
                    continue
                for c in ch[u]:
                    if c != t:
                        yield (u, t, c), reparent(par, c, t)
    elif op == "sub":
        for u in range(n):
            if len(ch[u]) < 2:
                continue
            sub = subtree(ch, u)
            sub.remove(u)
            p = list(par)
            prev = u
            for x in sorted(sub):
                p[x] = prev
                prev = x
            yield (u,), p


def main(op, tree_paths, m_paths):
    by = load(tree_paths, m_paths)
    tot = bad = 0
    trees = trees_noexist = 0
    shown = 0
    for c, ms in by.items():
        par = build_from_canon(c)
        n = len(par)
        if all(len(k) <= 1 for k in kids(par)):
            continue  # 道
        trees += 1
        exist = False
        any_move = False
        for key, p2 in moves(par, op):
            c2 = canon(p2)[0]
            ms2 = by.get(c2)
            if ms2 is None:
                continue
            any_move = True
            tot += 1
            viol = [S for S in range(1, n + 1) if ms[S - 1] < ms2[S - 1]]
            if viol:
                bad += 1
                if shown < 6:
                    S = viol[0]
                    print(f"  破れ {op}: G={c} 操作={key} G'={c2} S={S} M(G)={ms[S-1]} M(G')={ms2[S-1]}")
                    shown += 1
            else:
                exist = True
        if any_move and not exist:
            trees_noexist += 1
            if trees_noexist <= 5:
                print(f"  単調な選び方が無い: G={c}")
    print(f"{op}: 分岐のある木 {trees}，操作 {tot} 件，単調でない操作 {bad} 件，単調な選び方が無い木 {trees_noexist}")


if __name__ == "__main__":
    a = sys.argv[2:]
    h = len(a) // 2
    main(sys.argv[1], a[:h], a[h:])
