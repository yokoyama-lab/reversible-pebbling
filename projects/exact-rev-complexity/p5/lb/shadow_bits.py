#!/usr/bin/env python3
"""影のゲーム（shadow.py と同じ）を，鎖の側の集合をビット列（Python の整数）で持って解く高速版.

木の側は Aut(X) の軌道の代表だけを持つ．影のゲームの勝ちの領域は木の自己同型で不変
（σ を掛けても条件と手の集合が変わらない）なので，これは制限ではない．

不変条件（pluggable 版，slack δ）:
  A = ∅ ⇒ Z = ∅,  A = {根} ⇒ Z = {先端},  それ以外は |Z| <= |A| + δ かつ（根 ∈ A ⇒ 先端 ∈ Z）．
space 版（--space S）: |A| <= S の範囲で |Z| <= S，A = {根} ⇒ Z = {先端}，A = ∅ ⇒ Z = ∅．

使い方: python3 shadow_bits.py '<木>' [--nt 長さ] [--slack δ | --space S]
"""

from __future__ import annotations

import argparse
import sys
import time

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from lip_sat import canon_fn, parse  # noqa: E402


def popcount_masks(nt):
    """weight[k] = {Z : |Z| = k} のビット列."""
    NC = 1 << nt
    w = [0] * (nt + 1)
    for Z in range(NC):
        w[bin(Z).count("1")] |= 1 << Z
    return w


def solve(children, nt, slack=0, space=None, verbose=False):
    n = len(children)
    NC = 1 << nt
    FULL = (1 << NC) - 1
    need = [sum(1 << c for c in children[v]) for v in range(n)]
    pcw = popcount_masks(nt)
    upto = [0] * (nt + 2)
    acc = 0
    for k in range(nt + 1):
        acc |= pcw[k]
        upto[k] = acc
    upto[nt + 1] = acc
    top = 1 << (nt - 1)
    has_top = 0
    for Z in range(NC):
        if Z & top:
            has_top |= 1 << Z
    # flip_i: {Z : Z ^ e_i ∈ X}．bit i が 0 の位置のマスク M_i
    Mi = []
    for i in range(nt):
        m = 0
        blk = 1 << i
        # 位置 Z の bit i が 0 のもの
        pat = ((1 << blk) - 1)
        x = 0
        for s in range(0, NC, 2 * blk):
            x |= pat << s
        Mi.append(x)
        _ = m
    legal = []
    for i in range(nt):
        if i == 0:
            legal.append(FULL)
        else:
            # Z の bit i-1 が 1 の位置
            legal.append(FULL & ~Mi[i - 1])

    def flip(x, i):
        b = 1 << i
        return ((x & Mi[i]) << b) | ((x >> b) & Mi[i])

    def pre(Wp):
        """{Z : N[Z] ∩ Wp ≠ ∅}（N[Z] は Z 自身と合法な 1 手の行き先）."""
        r = Wp
        for i in range(nt):
            r |= flip(Wp, i) & legal[i]
        return r

    cf = canon_fn(children)
    key = {}
    rep = []
    NT = 1 << n
    orb = [-1] * NT
    for A in range(NT):
        if space is not None and bin(A).count("1") > space:
            continue
        k = cf(A)
        if k not in key:
            key[k] = len(rep)
            rep.append(A)
        orb[A] = key[k]
    m = len(rep)
    succ = []
    for A in rep:
        s = set()
        for v in range(n):
            if (A & need[v]) == need[v]:
                o2 = orb[A ^ (1 << v)]
                if o2 >= 0:
                    s.add(o2)
        succ.append(sorted(s))
    W = []
    for A in rep:
        w = bin(A).count("1")
        if A == 0:
            W.append(1 << 0)
        elif A == 1:
            W.append(1 << top)
        elif space is None:
            x = upto[min(nt, w + slack)]
            if A & 1:
                x &= has_top
            W.append(x)
        else:
            W.append(upto[min(nt, space)])
    it = 0
    t0 = time.time()
    while True:
        it += 1
        P = [pre(x) for x in W]
        changed = False
        for o in range(m):
            x = W[o]
            for o2 in succ[o]:
                x &= P[o2]
                if not x:
                    break
            if x != W[o]:
                W[o] = x
                changed = True
        if verbose:
            print(f"  反復 {it}: 空でない位置 {sum(1 for x in W if x)}/{m}  {time.time() - t0:.0f}s", flush=True)
        if not changed:
            break
    win = bool(W[orb[0]] & 1)
    return win, it, m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("trees", nargs="+")
    ap.add_argument("--nt", type=int, default=None)
    ap.add_argument("--slack", type=int, default=0)
    ap.add_argument("--space", type=int, default=None)
    ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    for t in a.trees:
        ch = parse(t)
        nt = a.nt or len(ch)
        win, it, m = solve(ch, nt, a.slack, a.space, a.v)
        mode = f"S={a.space}" if a.space is not None else (f"pluggable+{a.slack}" if a.slack else "pluggable")
        print(f"{t}（{len(ch)} 頂点 → 鎖 {nt}，{mode}，木の軌道 {m}）: {'鎖が勝つ' if win else '鎖が負ける'}（反復 {it}）", flush=True)


if __name__ == "__main__":
    main()
