#!/usr/bin/env python3
"""校正3: KSS（Komarath–Sarma–Sawlani, JCSS 2019）の定理との突き合わせ。

定理: 根つき木の可逆ペブリング数 = 台となる無向木の edge rank coloring 数 + 1。

edge rank coloring: 辺に整数色を付け、同色 i の 2 辺の間の路に必ず i より大きい色の辺がある。
その最小色数 χ'_e。ここでは全探索で χ'_e を求め、abandon.py の treeroot の
最小実行可能 p と一致するかを見る。**abandon.py とは完全に独立な計算。**
"""
import itertools
import subprocess
import sys


def cbt_edges(h):
    """完全二分木（高さ h）の辺集合。頂点 0 が根、子は 2v+1, 2v+2。"""
    n = 2 ** (h + 1) - 1
    return [(v, (v - 1) // 2) for v in range(1, n)]


def path_between(e1, e2, edges, h):
    """2 辺の間の路上の辺（両端の 2 辺を除く）を返す。木なので根への道で計算。"""
    def anc(v):
        out = [v]
        while v != 0:
            v = (v - 1) // 2
            out.append(v)
        return out

    # 辺 (c,p) を「子 c」で代表する。辺の間の路 = 子の間の路
    a, b = e1[0], e2[0]
    pa, pb = anc(a), anc(b)
    common = next(x for x in pa if x in pb)
    # a→common と b→common の辺を集める（e1, e2 自身を含む）
    def up(v):
        out = []
        while v != common:
            out.append((v, (v - 1) // 2))
            v = (v - 1) // 2
        return out
    seg = set(up(a)) | set(up(b))
    return seg - {e1, e2}


def is_edge_ranking(color, edges, h):
    for e1, e2 in itertools.combinations(edges, 2):
        if color[e1] != color[e2]:
            continue
        mid = path_between(e1, e2, edges, h)
        if not any(color[e] > color[e1] for e in mid):
            return False
    return True


def chi_e(h):
    """枝刈りつきバックトラックで χ'_e を求める。

    辺を 1 本ずつ塗り、**間の路が全部塗り終わっている**組だけを検査する
    （まだ塗っていない辺が救う可能性を潰さないため、これは健全な枝刈り）。
    """
    edges = cbt_edges(h)
    mid = {(e1, e2): path_between(e1, e2, edges, h)
           for e1, e2 in itertools.combinations(edges, 2)}

    def ok(color, e_new):
        for e_old in color:
            if e_old == e_new or color[e_old] != color[e_new]:
                continue
            key = (e_old, e_new) if (e_old, e_new) in mid else (e_new, e_old)
            seg = mid[key]
            if any(e not in color for e in seg):
                continue  # まだ決まっていないので判定を保留（枝刈りしない）
            if not any(color[e] > color[e_new] for e in seg):
                return False
        return True

    def search(i, k, color):
        if i == len(edges):
            return is_edge_ranking(color, edges, h)
        for c in range(1, k + 1):
            color[edges[i]] = c
            if ok(color, edges[i]) and search(i + 1, k, color):
                return True
            del color[edges[i]]
        return False

    for k in range(1, len(edges) + 1):
        if search(0, k, {}):
            return k
    return None


def min_pebbles(h, cap=8):
    for p in range(2, cap + 1):
        r = subprocess.run(
            [sys.executable, "abandon.py", "treeroot", str(h), "--p", str(p),
             "--e", "0", "--final", "keep"],
            capture_output=True, text=True)
        last = r.stdout.strip().splitlines()[-1]
        if "-" not in last.split()[2]:
            return p, last.split()[2]
    return None, None


if __name__ == "__main__":
    print("# h  χ'_e  χ'_e+1  最小p(実測)  そのときの手数  一致")
    for h in (1, 2, 3):
        c = chi_e(h)
        p, moves = min_pebbles(h)
        print(f"  {h}   {c}     {c + 1}        {p}          {moves}"
              f"       {'OK' if c + 1 == p else 'NG'}")
