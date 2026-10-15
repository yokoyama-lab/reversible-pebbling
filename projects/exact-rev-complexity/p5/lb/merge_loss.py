#!/usr/bin/env python3
"""根 + 長さ a の道 2 本（または長さ a, b）から鎖への pluggable 写像がある最長の鎖の長さを SAT で求める.

pluggable 写像の条件は lip_sat.py と同じ（(1) ψ(∅)=∅ (2) |ψ(A)|<=|A| (3) 1-Lipschitz (4) 根 ⇒ 先端）．
ただし鎖の長さ nt を木の頂点数より短くしてよい．存在すれば，その部分木を長さ nt の鎖に置き換えても
M(·,S) は増えない（頂点は減るので F_c の下界は弱くなる）．損失 λ = 頂点数 - nt.

使い方: python3 merge_loss.py a [b]   出力: 最長の nt と，その 1 つ上が UNSAT であること
"""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import lip_sat as L  # noqa: E402


def exists(children, nt: int, sym: bool = True) -> bool:
    n = len(children)
    NS = 1 << n
    need = [sum(1 << c for c in children[v]) for v in range(n)]
    cf = L.canon_fn(children)
    key: dict = {}
    rep = []
    orb = [0] * NS
    for A in range(NS):
        k = cf(A) if sym else A
        if k not in key:
            key[k] = len(rep)
            rep.append(A)
        orb[A] = key[k]
    cnf = L.CNF()
    Z = [[cnf.new() for _ in range(nt)] for _ in rep]
    for o, A in enumerate(rep):
        w = bin(A).count("1")
        if A == 0:
            for i in range(nt):
                cnf.add([-Z[o][i]])
            continue
        cnf.atmost_k(Z[o], w)
        if A & 1:
            cnf.add([Z[o][nt - 1]])
    seen = set()
    for o, A in enumerate(rep):
        for v in range(n):
            if (A & need[v]) != need[v]:
                continue
            o2 = orb[A ^ (1 << v)]
            if o2 == o:
                continue
            e = (min(o, o2), max(o, o2))
            if e in seen:
                continue
            seen.add(e)
            p, q = Z[o], Z[o2]
            d = [cnf.new() for _ in range(nt)]
            for i in range(nt):
                cnf.add([-d[i], p[i], q[i]])
                cnf.add([-d[i], -p[i], -q[i]])
                cnf.add([d[i], -p[i], q[i]])
                cnf.add([d[i], p[i], -q[i]])
                if i > 0:
                    cnf.add([-d[i], p[i - 1]])
            cnf.amo(d)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        f.write(f"p cnf {cnf.nv} {len(cnf.cl)}\n")
        for c in cnf.cl:
            f.write(" ".join(map(str, c)) + " 0\n")
        path = f.name
    try:
        r = subprocess.run(["kissat", "-q", path], capture_output=True, text=True)
    finally:
        os.unlink(path)
    st = next((ln for ln in r.stdout.splitlines() if ln.startswith("s ")), "s ?")
    if "UNSAT" in st:
        return False
    if "SATISFIABLE" in st:
        return True
    raise RuntimeError(st)


def path(a: int) -> str:
    return "(" * a + ")" * a


if __name__ == "__main__":
    a = int(sys.argv[1])
    b = int(sys.argv[2]) if len(sys.argv) > 2 else a
    t = "(" + path(a) + path(b) + ")"
    ch = L.parse(t)
    n = len(ch)
    nt = n
    while nt >= 1 and not exists(ch, nt, sym=(a == b)):
        print(f"  a={a} b={b} nt={nt}: UNSAT", flush=True)
        nt -= 1
    print(f"根+P{a}+P{b}（{n} 頂点）: 最長 {nt}，損失 {n - nt}", flush=True)
