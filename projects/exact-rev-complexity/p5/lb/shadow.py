#!/usr/bin/env python3
"""影のゲーム: 木の手順を鎖が 1 手ずつ（0 手か 1 手で）追いかけられるか.

位置 (A, Z): A は木 X の配置，Z は長さ nt の鎖の配置．木の側が任意の合法な 1 手 A -> A' を打つと，
鎖の側は Z をそのままにするか合法な 1 手 Z -> Z' を打つ．鎖の側は次の不変条件を保ちたい:
  pluggable 版:  |Z| <= |A|，かつ 根 ∈ A ⇒ 先端 ∈ Z
  space 版:      |A| <= S の範囲で |Z| <= S，かつ A = {根} ⇒ Z = {先端}
(∅,∅) から不変条件を保ち続けられる（安全ゲームの勝ち）なら，木の手順を手数を増やさずに鎖の手順へ写せる．
写像（lip_sat.py）はこの特別な場合（Z が A だけで決まる）で，影のゲームのほうが強い．
pluggable 版で勝てれば，X を含むどの木でも X を長さ nt の鎖に置き換えて M(·,S) は増えない
（X の外の手はそのまま，X の親の手は「根 ⇒ 先端」で合法のまま，ペブル数は |Z| <= |A| で増えない）．

勝ちの領域は最大不動点 W = {(A,Z) 有効 : すべての木の手 A->A' に，Z' ∈ N[Z] で (A',Z') ∈ W なるものがある}．

使い方: python3 shadow.py '<木>' [--nt 長さ] [--space S]
"""

from __future__ import annotations

import argparse
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from lip_sat import parse  # noqa: E402


def solve(children, nt: int, space: int | None = None, slack: int = 0):
    n = len(children)
    NT = 1 << n
    NC = 1 << nt
    need = [sum(1 << c for c in children[v]) for v in range(n)]
    pc = [bin(x).count("1") for x in range(max(NT, NC))]
    top = 1 << (nt - 1)

    def tmoves(A):
        out = []
        for v in range(n):
            if (A & need[v]) == need[v]:
                B = A ^ (1 << v)
                if space is None or pc[B] <= space:
                    out.append(B)
        return out

    cnbr = []
    for Z in range(NC):
        s = [Z]
        for i in range(nt):
            if i == 0 or (Z >> (i - 1)) & 1:
                s.append(Z ^ (1 << i))
        cnbr.append(s)

    def valid(A, Z):
        if space is None:
            if A == 0:
                return Z == 0
            if A == 1:
                return Z == top
            if pc[Z] > pc[A] + slack:
                return False
            if (A & 1) and not (Z & top):
                return False
            return True
        if pc[A] > space or pc[Z] > space:
            return False
        if A == 1 and Z != top:
            return False
        return True

    As = [A for A in range(NT) if space is None or pc[A] <= space]
    W = {A: set(Z for Z in range(NC) if valid(A, Z)) for A in As}
    tm = {A: tmoves(A) for A in As}
    changed = True
    rounds = 0
    while changed:
        changed = False
        rounds += 1
        for A in As:
            keep = set()
            for Z in W[A]:
                ok = True
                for A2 in tm[A]:
                    W2 = W[A2]
                    if not any(Z2 in W2 for Z2 in cnbr[Z]):
                        ok = False
                        break
                if ok:
                    keep.add(Z)
            if len(keep) != len(W[A]):
                W[A] = keep
                changed = True
    return (0 in W[0]), W, rounds


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("trees", nargs="+")
    ap.add_argument("--nt", type=int, default=None)
    ap.add_argument("--space", type=int, default=None)
    ap.add_argument("--slack", type=int, default=0, help="pluggable 版で |Z| <= |A| + slack を許す（∅ と {根} では厳密）")
    a = ap.parse_args()
    for t in a.trees:
        ch = parse(t)
        nt = a.nt or len(ch)
        win, W, rounds = solve(ch, nt, a.space, a.slack)
        mode = (f"pluggable+{a.slack}" if a.slack else "pluggable") if a.space is None else f"S={a.space}"
        print(f"{t}（{len(ch)} 頂点 → 鎖 {nt}，{mode}）: {'鎖が勝つ' if win else '鎖が負ける'}（反復 {rounds}）", flush=True)


if __name__ == "__main__":
    main()
