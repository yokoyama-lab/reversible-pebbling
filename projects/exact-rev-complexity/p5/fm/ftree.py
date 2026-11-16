#!/usr/bin/env python3
"""木の Knill 型再帰 F の独立実装（p5_tree_count.py とは別に書いた．標準ライブラリだけ）.

ゲーム（persistent 可逆ペブリング）:
  頂点 v を置く／外す手は v の子がすべてペブル済みのときだけ合法．
  空の盤から根だけがペブルされた盤へ．同時に置けるペブルは S 個まで．M(T,S) は最短手数．

再帰（原稿 P5 の定義 1）:
  F(T,S) = inf (S <= 0)
  F(葉,S) = 1 (S >= 1)
  F(T,S) = min_{u != root} F(T_u,S) + F(T_u,S-1) + F(T - T_u, S-1)

枝刈りは S < chain_space(高さ) だけを使う（p5_tree_count.py の完全二分木の PMIN による枝刈りは使わない）．
正当性: S 個で T をペブリングする手順を根から最も深い葉への道 P に制限すると，P の各頂点への手は
P 上の子がペブル済みのときだけ起こるので，|P|=高さ 頂点の鎖のペブリングになる．よって M < inf なら
S >= chain_space(高さ)（Knill Thm 2.3: 鎖 n 頂点は S >= ceil(log2 n)+1 で可能，かつそのときに限る）．
F（と構成の F2）は M 以上なので，同じ条件で inf としてよい．

木の形は「子の形の番号の昇順タプル」で正規化し，番号を振る（intern）．
"""

from __future__ import annotations

import functools
import sys

sys.setrecursionlimit(100000)
INF = float("inf")

KIDS: list[tuple[int, ...]] = []
_IDX: dict[tuple[int, ...], int] = {}


def node(kids) -> int:
    key = tuple(sorted(kids))
    i = _IDX.get(key)
    if i is None:
        i = len(KIDS)
        _IDX[key] = i
        KIDS.append(key)
    return i


LEAF = node(())


@functools.lru_cache(None)
def nverts(g: int) -> int:
    return 1 + sum(nverts(c) for c in KIDS[g])


def chain(n: int) -> int:
    g = LEAF
    for _ in range(n - 1):
        g = node((g,))
    return g


def cbt(h: int) -> int:
    g = LEAF
    for _ in range(h - 1):
        g = node((g, g))
    return g


@functools.lru_cache(None)
def cuts(g: int) -> tuple[tuple[int, int], ...]:
    """根以外の頂点 u ごとに (T_u, T - T_u) の形の組（重複は除く）."""
    ks = KIDS[g]
    res = set()
    for k in range(len(ks)):
        rest = ks[:k] + ks[k + 1:]
        res.add((ks[k], node(rest)))
        for (s, r) in cuts(ks[k]):
            res.add((s, node(rest + (r,))))
    return tuple(sorted(res))


@functools.lru_cache(None)
def height(g: int) -> int:
    return 1 + max((height(c) for c in KIDS[g]), default=0)


def chain_space(L: int) -> int:
    """L 頂点の鎖の persistent 最小空間（L>=1）."""
    return 1 if L <= 1 else (L - 1).bit_length() + 1


PRUNE = True  # False で枝刈りなし（検査用）

# 完全二分木による枝刈り（KSS の定理は使わず，F 自身の性質だけで正当化する）:
#   補題 A: F(g,S) < inf なら，g の任意の頂点 v について F(g_v,S) < inf，かつ
#           g から任意の部分木を除いた木 g' についても F(g',S) < inf．
#     （F の再帰についての帰納法．分割頂点 u と v・除く部分木の位置関係で場合分けすると，
#       同じ u か u での分割がそのまま使える．S について有限性が単調なことも同じ帰納法で出る．）
#   よって g が Bt_k を「根から子へそのまま」含む（ある頂点 v から下へ，各頂点が 2 つの子を持つ形で
#   k 段とれる）なら，S < PMIN_F[k] のとき F(g,S) = inf．PMIN_F[k] は F 自身で下から求めた値．
#   F2（cross_fast.py）は有限性が F と同じ（交差の手順が有限なら v を外側にした入れ子も有限）なので同じ枝刈りが使える．
PMIN_F: dict[int, int] = {1: 1}


@functools.lru_cache(None)
def direct_cbt(g: int) -> int:
    """g の根から子へそのまま埋め込める完全二分木の最大の高さ."""
    ds = sorted((direct_cbt(c) for c in KIDS[g]), reverse=True)
    return 1 + ds[1] if len(ds) >= 2 else 1


@functools.lru_cache(None)
def max_cbt(g: int) -> int:
    """g のどこかの頂点から根へそのまま埋め込める完全二分木の最大の高さ."""
    return max([direct_cbt(g)] + [max_cbt(c) for c in KIDS[g]])


def lb_space(g: int) -> int:
    return max(chain_space(height(g)), PMIN_F.get(max_cbt(g), 0))


def pmin_cbt(h: int) -> int:
    """PMIN_F[h] を（h-1 までを使って）求めて登録する．F のキャッシュは消さずに済む順で呼ぶこと."""
    for k in range(2, h + 1):
        if k in PMIN_F:
            continue
        g = cbt(k)
        S = PMIN_F[k - 1]  # 補題 A より Bt_{k-1} を含むので下界（+1 は F については示していないので使わない）
        while F(g, S) == INF:
            S += 1
        PMIN_F[k] = S
    return PMIN_F[h]


@functools.lru_cache(None)
def F(g: int, S: int):
    if S <= 0:
        return INF
    if PRUNE and S < lb_space(g):
        return INF
    if not KIDS[g]:
        return 1
    best = INF
    for (s, r) in cuts(g):
        v = F(s, S) + F(s, S - 1) + F(r, S - 1)
        if v < best:
            best = v
    return best


def enumerate_trees(nmax: int, maxdeg: int | None = None) -> dict[int, list[int]]:
    """頂点数ごとの根付き木の形（子の数の上限 maxdeg，None は無制限）."""
    by: dict[int, list[int]] = {1: [LEAF]}
    for n in range(2, nmax + 1):
        acc: set[int] = set()

        # 子の多重集合を (頂点数, 番号) の非減少列として作る
        def rec(rem: int, lo: tuple[int, int], kids: list[int]):
            if rem == 0:
                acc.add(node(kids))
                return
            if maxdeg is not None and len(kids) >= maxdeg:
                return
            for s in range(lo[0], rem + 1):
                for c in by[s]:
                    if (s, c) < lo:
                        continue
                    kids.append(c)
                    rec(rem - s, (s, c), kids)
                    kids.pop()

        rec(n - 1, (1, -1), [])
        by[n] = sorted(acc)
    return by


def parents(g: int) -> list[int]:
    """形 g を頂点番号つきに展開し，親の配列を返す（根は 0，親は -1）."""
    par: list[int] = []

    def build(x: int, p: int):
        v = len(par)
        par.append(p)
        for c in KIDS[x]:
            build(c, v)

    build(g, -1)
    return par


@functools.lru_cache(None)
def canon(g: int) -> str:
    """実行によらない正準な文字列（子の文字列を整列して並べる）."""
    ks = KIDS[g]
    if not ks:
        return "."
    return "(" + "".join(sorted(canon(c) for c in ks)) + ")"


def show(g: int) -> str:
    ks = KIDS[g]
    if not ks:
        return "."
    return "(" + "".join(show(c) for c in ks) + ")"


# OEIS A000081（頂点数 n の根付き木，n=1..），子が 2 個以下の根付き木（A001190 を 1 つずらしたもの，n=1..）
A000081 = [1, 1, 2, 4, 9, 20, 48, 115, 286, 719, 1842, 4766, 12486, 32973, 87811, 235381, 634847, 1721159]
A001190s = [1, 1, 2, 3, 6, 11, 23, 46, 98, 207, 451, 983, 2179, 4850, 10905, 24631, 56011, 127912, 293547]
