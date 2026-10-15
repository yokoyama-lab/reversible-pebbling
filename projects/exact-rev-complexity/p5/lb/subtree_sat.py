#!/usr/bin/env python3
"""部分木を同じ頂点数の鎖へ置き換える局所写像があるかを SAT で調べる.

木 X（根 x）の配置から長さ |X| の鎖 Z の配置への写像 ψ で
  (1) ψ(∅) = ∅,  (2) |ψ(A)| <= |A|,
  (3) X の合法な 1 手 A -> A' について ψ(A) = ψ(A') か Z の合法な 1 手で移り合う,
  (4) x ∈ A ならば Z の先端 ∈ ψ(A)
を満たすもの．あれば，X を任意の木の中でぶら下がる部分木として鎖に置き換えても M(·,S) は増えない．
（X の外の手は写像を変えない．X の親の手は (4) で合法のまま．）

使い方: python3 subtree_sat.py '<木>'   木は括弧表記: '()' が葉，'(()())' が T_2．
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile


def parse(s: str):
    """括弧表記を children リスト（頂点 0 が根）にする."""
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


def build(children):
    n = len(children)
    NS = 1 << n
    need = [sum(1 << c for c in children[v]) for v in range(n)]
    pc = [bin(x).count("1") for x in range(NS)]

    def tmoves(A):
        return [A ^ (1 << v) for v in range(n) if (A & need[v]) == need[v]]

    def cmoves(Z):
        return [Z ^ (1 << i) for i in range(n) if i == 0 or (Z >> (i - 1)) & 1]

    var = {}
    nv = 0
    for A in range(NS):
        for Z in range(NS):
            if pc[Z] <= pc[A]:
                nv += 1
                var[(A, Z)] = nv
    top = 1 << (n - 1)
    clauses = []
    nbr = {Z: set(cmoves(Z)) | {Z} for Z in range(NS)}
    for A in range(NS):
        opts = [Z for Z in range(NS) if (A, Z) in var]
        if A == 0:
            opts = [0]
        if A & 1:  # 根（頂点 0）がペブル済み
            opts = [Z for Z in opts if Z & top]
        for Z in range(NS):
            if (A, Z) in var and Z not in opts:
                clauses.append([-var[(A, Z)]])
        clauses.append([var[(A, Z)] for Z in opts])
        for i in range(len(opts)):
            for j in range(i + 1, len(opts)):
                clauses.append([-var[(A, opts[i])], -var[(A, opts[j])]])
        for A2 in tmoves(A):
            for Z in opts:
                clauses.append([-var[(A, Z)]] + [var[(A2, Z2)] for Z2 in nbr[Z] if (A2, Z2) in var])
    return nv, clauses


def main(s: str, solver: str = "cadical"):
    children = parse(s)
    nv, clauses = build(children)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
        path = f.name
    try:
        r = subprocess.run([solver, "-q", path], capture_output=True, text=True)
    finally:
        os.unlink(path)
    status = next((ln for ln in r.stdout.splitlines() if ln.startswith("s ")), "s ?")
    print(f"{s}（{len(children)} 頂点）: {status}（変数 {nv}，節 {len(clauses)}）")


if __name__ == "__main__":
    for s in sys.argv[1:]:
        main(s)
