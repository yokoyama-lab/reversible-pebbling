#!/usr/bin/env python3
"""2 本の道の併合写像があるかを SAT で調べる（手術の補題の探索）.

対象: 長さ a と b の道（鎖）P, Q の配置の直積から，長さ a+b の鎖 Z の配置への写像 ψ で
  (1) ψ(∅) = ∅
  (2) |ψ(A)| <= |A|                       （ペブル数を増やさない）
  (3) 直積の合法な 1 手 A -> A' について ψ(A) = ψ(A') か，Z の合法な 1 手で移り合う
  (4) A が P と Q の先端を両方含むなら ψ(A) は Z の先端を含む
を満たすもの．あれば，木の中で頂点 w の下に P, Q がぶら下がっているとき，それを長さ a+b の 1 本の道に
置き換えても M(·,S) は増えない（どの手順も ψ で写せる）．

使い方: python3 merge_sat.py a b [--solver cadical]
出力: SAT/UNSAT と，SAT なら写像の表（状態は下位ビットから P の 1..a, Q の 1..b）.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile


def chain_moves(x: int, n: int):
    """長さ n の鎖の配置 x（ビット i がセル i+1）から 1 手で行ける配置."""
    out = []
    for i in range(n):
        if i == 0 or (x >> (i - 1)) & 1:
            out.append(x ^ (1 << i))
    return out


def prod_moves(A: int, a: int, b: int):
    out = []
    for i in range(a):
        if i == 0 or (A >> (i - 1)) & 1:
            out.append(A ^ (1 << i))
    for j in range(b):
        if j == 0 or (A >> (a + j - 1)) & 1:
            out.append(A ^ (1 << (a + j)))
    return out


def build(a: int, b: int):
    n = a + b
    NS = 1 << n
    pc = [bin(x).count("1") for x in range(NS)]
    var = {}
    nv = 0
    for A in range(NS):
        for Z in range(NS):
            if pc[Z] <= pc[A]:
                nv += 1
                var[(A, Z)] = nv
    clauses = []
    top_p = 1 << (a - 1)
    top_q = 1 << (a + b - 1)
    top_z = 1 << (n - 1)
    nbrZ = {Z: set(chain_moves(Z, n)) | {Z} for Z in range(NS)}
    for A in range(NS):
        opts = [Z for Z in range(NS) if (A, Z) in var]
        if A == 0:
            opts = [0]
            for Z in range(1, NS):
                if (A, Z) in var:
                    clauses.append([-var[(A, Z)]])
        if (A & top_p) and (A & top_q):
            for Z in list(opts):
                if not Z & top_z:
                    clauses.append([-var[(A, Z)]])
            opts = [Z for Z in opts if Z & top_z]
        clauses.append([var[(A, Z)] for Z in opts])  # 少なくとも 1 つ
        for i in range(len(opts)):  # 高々 1 つ
            for j in range(i + 1, len(opts)):
                clauses.append([-var[(A, opts[i])], -var[(A, opts[j])]])
    for A in range(NS):
        for A2 in prod_moves(A, a, b):
            if A2 < A:
                continue  # 対称なので片向きだけでよいが，含意は両向きに書く
            for (X, Y) in ((A, A2), (A2, A)):
                for Z in range(NS):
                    if (X, Z) not in var:
                        continue
                    lits = [-var[(X, Z)]] + [var[(Y, Z2)] for Z2 in nbrZ[Z] if (Y, Z2) in var]
                    clauses.append(lits)
    return nv, clauses, var


def solve(a: int, b: int, solver: str):
    nv, clauses, var = build(a, b)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
        path = f.name
    try:
        r = subprocess.run([solver, "-q", path] if solver == "cadical" else [solver, path],
                           capture_output=True, text=True)
    finally:
        os.unlink(path)
    lines = r.stdout.splitlines()
    status = next((ln for ln in lines if ln.startswith("s ")), "s ?")
    model = set()
    for ln in lines:
        if ln.startswith("v "):
            model.update(int(t) for t in ln[2:].split() if int(t) > 0)
    psi = None
    if "SATISFIABLE" in status and "UNSAT" not in status:
        inv = {v: k for k, v in var.items()}
        psi = {}
        for v in model:
            if v in inv:
                A, Z = inv[v]
                psi[A] = Z
    return status, nv, len(clauses), psi


def show(x: int, n: int) -> str:
    return "".join("1" if (x >> i) & 1 else "0" for i in range(n))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("a", type=int)
    ap.add_argument("b", type=int)
    ap.add_argument("--solver", default="cadical")
    ap.add_argument("--print", action="store_true")
    args = ap.parse_args()
    st, nv, nc, psi = solve(args.a, args.b, args.solver)
    print(f"a={args.a} b={args.b}: {st}（変数 {nv}，節 {nc}）")
    if psi and args.print:
        n = args.a + args.b
        for A in sorted(psi):
            print(f"  P={show(A & ((1 << args.a) - 1), args.a)} Q={show(A >> args.a, args.b)} -> Z={show(psi[A], n)}")
    sys.exit(0)
