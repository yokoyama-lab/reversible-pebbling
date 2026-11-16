#!/usr/bin/env python3
"""木 X の配置グラフから長さ |X| の鎖の配置グラフへの「1-Lipschitz・ペブル数非増加」写像を SAT で探す.

subtree_sat.py と同じ条件
  (1) ψ(∅)=∅  (2) |ψ(A)| <= |A|  (3) X の合法な 1 手は ψ では 0 手か鎖の合法な 1 手  (4) 根 ∈ A ⇒ 鎖の先端 ∈ ψ(A)
を，像をビット列（|X| 個の変数）で符号化して解く．--sym を付けると Aut(X) で不変な写像に限る
（配置を自己同型の軌道にまとめる．軌道あたり変数 |X| 個）．
存在すれば，X を含むどの木でも X を鎖に置き換えて M(·,S) は増えない．とくに X 自身について
M(X,S) >= Fc(|X|,S)（すべての S）．

使い方: python3 lip_sat.py '<括弧表記の木>' [--sym] [--solver kissat|cadical] [--dump 写像の出力先]
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile


def parse(s: str):
    children: list[list[int]] = []
    stack: list[int] = []
    for ch in s:
        if ch == "(":
            v = len(children)
            children.append([])
            if stack:
                children[stack[-1]].append(v)
            stack.append(v)
        elif ch == ")":
            stack.pop()
    return children


class CNF:
    def __init__(self):
        self.nv = 0
        self.cl: list[list[int]] = []

    def new(self) -> int:
        self.nv += 1
        return self.nv

    def add(self, c):
        self.cl.append(list(c))

    def amo(self, xs):
        """高々 1 つ（逐次符号化）."""
        if len(xs) <= 4:
            for i in range(len(xs)):
                for j in range(i + 1, len(xs)):
                    self.add([-xs[i], -xs[j]])
            return
        s = [self.new() for _ in range(len(xs) - 1)]
        self.add([-xs[0], s[0]])
        for i in range(1, len(xs) - 1):
            self.add([-xs[i], s[i]])
            self.add([-s[i - 1], s[i]])
            self.add([-xs[i], -s[i - 1]])
        self.add([-xs[-1], -s[-1]])

    def atmost_k(self, xs, k):
        """Σ xs <= k（逐次カウンタ，Sinz 2005）."""
        n = len(xs)
        if k >= n:
            return
        if k == 0:
            for x in xs:
                self.add([-x])
            return
        s = [[self.new() for _ in range(k)] for _ in range(n)]
        self.add([-xs[0], s[0][0]])
        for j in range(1, k):
            self.add([-s[0][j]])
        for i in range(1, n):
            self.add([-xs[i], s[i][0]])
            self.add([-s[i - 1][0], s[i][0]])
            for j in range(1, k):
                self.add([-xs[i], -s[i - 1][j - 1], s[i][j]])
                self.add([-s[i - 1][j], s[i][j]])
            self.add([-xs[i], -s[i - 1][k - 1]])


def canon_fn(children):
    """配置 A（ビット集合）の Aut 不変な正準形を返す関数."""

    def canon(v, A):
        return ((A >> v) & 1, tuple(sorted(canon(c, A) for c in children[v])))

    return lambda A: canon(0, A)


def build(children, sym: bool, weak4: bool = False, space: int | None = None):
    """space を与えると，定義域を「ペブル数 <= space の配置」に，(2) を |ψ(A)| <= space に替え，
    (4) は ψ({根}) = {先端} とする（木全体の M(X,space) >= Fc(|X|,space) の証明に足りる形）."""
    n = len(children)
    NS = 1 << n
    need = [sum(1 << c for c in children[v]) for v in range(n)]
    inside = [space is None or bin(A).count("1") <= space for A in range(NS)]
    if sym:
        cf = canon_fn(children)
        key: dict = {}
        rep = []
        orb = [-1] * NS
        for A in range(NS):
            if not inside[A]:
                continue
            k = cf(A)
            if k not in key:
                key[k] = len(rep)
                rep.append(A)
            orb[A] = key[k]
    else:
        rep = [A for A in range(NS) if inside[A]]
        orb = [-1] * NS
        for i, A in enumerate(rep):
            orb[A] = i
    m = len(rep)
    cnf = CNF()
    Z = [[cnf.new() for _ in range(n)] for _ in range(m)]  # Z[o][i]: 鎖のセル i+1
    for o, A in enumerate(rep):
        w = bin(A).count("1")
        if A == 0:
            for i in range(n):
                cnf.add([-Z[o][i]])
            continue
        if space is None:
            cnf.atmost_k(Z[o], w)
            if (A & 1) and (not weak4 or A == 1):  # 根（頂点 0）．weak4 では {根} だけ
                cnf.add([Z[o][n - 1]])
        else:
            cnf.atmost_k(Z[o], space)
            if A == 1:  # ψ({根}) = {先端}
                for i in range(n - 1):
                    cnf.add([-Z[o][i]])
                cnf.add([Z[o][n - 1]])
    seen = set()
    for o, A in enumerate(rep):
        for v in range(n):
            if (A & need[v]) != need[v]:
                continue
            o2 = orb[A ^ (1 << v)]
            if o2 < 0 or o2 == o:
                continue
            e = (min(o, o2), max(o, o2))
            if e in seen:
                continue
            seen.add(e)
            p, q = Z[o], Z[o2]
            d = [cnf.new() for _ in range(n)]
            for i in range(n):  # d_i <-> p_i xor q_i
                cnf.add([-d[i], p[i], q[i]])
                cnf.add([-d[i], -p[i], -q[i]])
                cnf.add([d[i], -p[i], q[i]])
                cnf.add([d[i], p[i], -q[i]])
                if i > 0:  # セル i+1 を動かすにはセル i が要る（p, q で共通）
                    cnf.add([-d[i], p[i - 1]])
            cnf.amo(d)
    return cnf, Z, rep, orb


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tree")
    ap.add_argument("--sym", action="store_true")
    ap.add_argument("--solver", default="kissat")
    ap.add_argument("--dump")
    ap.add_argument("--space", type=int, default=None)
    ap.add_argument("--weak4", action="store_true",
                    help="(4) を ψ({根}) ∋ 先端 だけに弱める（木全体の CC にはこれで足りる）")
    a = ap.parse_args()
    children = parse(a.tree)
    cnf, Z, rep, orb = build(children, a.sym, a.weak4, a.space)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {cnf.nv} {len(cnf.cl)}\n")
        for c in cnf.cl:
            f.write(" ".join(map(str, c)) + " 0\n")
        path = f.name
    try:
        args = [a.solver, "-q", path]
        r = subprocess.run(args, capture_output=True, text=True)
    finally:
        os.unlink(path)
    status = next((ln for ln in r.stdout.splitlines() if ln.startswith("s ")), "s ?")
    print(f"{a.tree}（{len(children)} 頂点，{'Aut 不変' if a.sym else '制約なし'}{'，弱い(4)' if a.weak4 else ''}{f'，S={a.space}' if a.space else ''}，状態 {len(rep)}）: {status}"
          f"（変数 {cnf.nv}，節 {len(cnf.cl)}）", flush=True)
    if a.dump and "UNSAT" not in status and "SATISFIABLE" in status:
        model = set()
        for ln in r.stdout.splitlines():
            if ln.startswith("v "):
                model.update(int(t) for t in ln[2:].split() if int(t) > 0)
        n = len(children)
        with open(a.dump, "w") as g:
            for A in range(1 << n):
                o = orb[A]
                if o < 0:
                    continue
                z = sum(1 << i for i in range(n) if Z[o][i] in model)
                g.write(f"{A} {z}\n")
        print(f"写像を {a.dump} に書いた")


if __name__ == "__main__":
    sys.exit(main())
