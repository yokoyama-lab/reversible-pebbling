#!/usr/bin/env python3
"""F の再帰から完全二分木 T_h の具体的な手順を組み立てる（上界 M*(h) <= F*(h) の証人）.

F の値そのものは P5 の code/p5_tree_count.py を読み込んで使う（形の上の再帰）。
ここで足すのは「どの u で分割したか」の復元と、ラベルつきの頂点での手順の展開だけ。
手順の合法性はこのファイルでは検査しない（検査は独立に書いた check_seq.py が行う）。

頂点の番号はヒープ順: 根 = 0、v の子 = 2v+1, 2v+2（T_h は 2^h - 1 頂点）。
出力: 1 行 1 手（置く／外す頂点の番号）。先頭の # 行に h, S, 手数。

    python3 witness.py 8 11 > logs/witness_h8_p11.txt
"""
from __future__ import annotations

import sys
from pathlib import Path

CODE = Path("<local>/dev/overleaf/2026-WiNF/code")
sys.path.insert(0, str(CODE))
import p5_tree_count as P5  # noqa: E402

sys.setrecursionlimit(100000)


def children_in(v: int, G: frozenset, n: int) -> list[int]:
    return [c for c in (2 * v + 1, 2 * v + 2) if c < n and c in G]


def shape(v: int, G: frozenset, n: int) -> int:
    """G の中で v を根とする部分の形（P5 の正規形の番号）."""
    return P5.mk(tuple(shape(c, G, n) for c in children_in(v, G, n)))


def subtree(u: int, G: frozenset, n: int) -> frozenset:
    out, st = [], [u]
    while st:
        x = st.pop()
        out.append(x)
        st.extend(children_in(x, G, n))
    return frozenset(out)


def seq(root: int, G: frozenset, S: int, n: int) -> list[int]:
    """G（root を根とする頂点集合）で、空から {root} へ S 個以下で移る手順（F の構成）."""
    target = P5.F(shape(root, G, n), S)
    if target == P5.INF:
        raise ValueError("infinite")
    if len(G) == 1:
        return [root]
    for u in sorted(G - {root}):
        Gu = subtree(u, G, n)
        rest = G - Gu
        a = P5.F(shape(u, Gu, n), S)
        b = P5.F(shape(root, rest, n), S - 1)
        c = P5.F(shape(u, Gu, n), S - 1)
        if a + b + c == target:
            s1 = seq(u, Gu, S, n)          # u を S 個で置く
            s2 = seq(root, rest, S - 1, n)  # u を持ったまま残りの根を S-1 個で置く
            s3 = seq(u, Gu, S - 1, n)       # 根を持ったまま u を S-1 個で外す（逆順に打つ）
            out = s1 + s2 + s3[::-1]
            assert len(out) == target
            return out
    raise AssertionError("no split attains F")


def main() -> None:
    h, S = int(sys.argv[1]), int(sys.argv[2])
    n = (1 << h) - 1
    for k in range(1, h + 1):  # PMIN を下から埋める（F の枝刈りが参照する）
        P5.pmin_and_F(k)
    G = frozenset(range(n))
    moves = seq(0, G, S, n)
    print(f"# h={h} S={S} n={n} moves={len(moves)} F={P5.F(P5.Bt(h), S)}")
    for v in moves:
        print(v)


if __name__ == "__main__":
    main()
