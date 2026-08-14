#!/usr/bin/env python3
"""拡大性つき下界に **DRAT 証明書**を付ける（2026-08-14）。

`q2_pyr_lower.py` の抽象（層ごとの個数 `a_k(t)` と変化数 `c_k(t)` だけ）を
**順序符号化**で CNF に落とし、「ピーク <= B-1 が実行不能」を cadical に証明させる。
抽象は緩和なので、その実行不能性は `p_min >= B` を意味する。

順序符号化: `A[k][t][j]` = 「`a_k(t) >= j`」（`j = 1..n_k`）。
`Σ_k a_k(t) = Σ_{k,j} A[k][t][j]` なので、**ピーク制約はそのまま基数制約**になる。

⚠ この環境の SCIP 10.0 は VIPR 証明書を出せない（`~/dev/TOOLS.md` の 2026-08-10 の訂正）。
そのため MIP ではなく SAT + DRAT を使う。
"""
import argparse
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from q2_cnf import Cnf  # noqa: E402


def build(h: int, B: int) -> Cnf:
    """「拡大性つき抽象でピーク <= B が実行可能」を表す CNF。"""
    D = h - 1
    T = 2 * D + 1
    n = [h - k for k in range(h)]
    c = Cnf()
    # A[k][t][j] = a_k(t) >= j   （j = 1..n[k]）
    A = [[[c.new() for _ in range(n[k] + 1)] for _ in range(T + 1)] for k in range(D + 1)]
    # C[k][t][j] = c_k(t) >= j   （j = 1..n[k]）
    Cv = [[[c.new() for _ in range(n[k] + 1)] for _ in range(T)] for k in range(D + 1)]

    def ge(k, t, j):                       # a_k(t) >= j
        return A[k][t][j] if 1 <= j <= n[k] else None

    for k in range(D + 1):
        for t in range(T + 1):
            for j in range(2, n[k] + 1):   # 単調性
                c.add(-A[k][t][j], A[k][t][j - 1])
        for t in range(T):
            for j in range(2, n[k] + 1):
                c.add(-Cv[k][t][j], Cv[k][t][j - 1])

    for k in range(D + 1):
        for t in range(T + 1):
            if k == D:                     # sink: t < D+1 で 0、以降 1
                if t < D + 1:
                    c.add(-A[k][t][1])
                else:
                    c.add(A[k][t][1])
            else:
                if t < k + 1 or t > 2 * D - k:      # 窓（time_window_dep）
                    c.add(-A[k][t][1])
                if t in (k + 1, k + 2, 2 * D - k - 1, 2 * D - k):   # 両端強制
                    c.add(A[k][t][n[k]])

    for k in range(D + 1):
        for t in range(T):
            # c_k(t) >= a_k(t) - a_k(t+1)  と  >= a_k(t+1) - a_k(t)
            for x in range(1, n[k] + 1):
                for y in range(0, x):
                    d = x - y
                    if d > n[k]:
                        continue
                    hi = ge(k, t + 1, y + 1)
                    c.add(*( [-A[k][t][x]] + ([hi] if hi else []) + [Cv[k][t][d]] ))
                    hi2 = ge(k, t, y + 1)
                    c.add(*( [-A[k][t + 1][x]] + ([hi2] if hi2 else []) + [Cv[k][t][d]] ))
            # 拡大性: c_k(t) >= j → a_{k-1}(t), a_{k-1}(t+1) >= j+1
            if k >= 1:
                for j in range(1, n[k] + 1):
                    if j + 1 <= n[k - 1]:
                        c.add(-Cv[k][t][j], A[k - 1][t][j + 1])
                        c.add(-Cv[k][t][j], A[k - 1][t + 1][j + 1])
                    else:
                        c.add(-Cv[k][t][j])      # 親側が足りない = 不可能

    for t in range(T + 1):                        # ピーク <= B
        lits = [A[k][t][j] for k in range(D + 1) for j in range(1, n[k] + 1)]
        c.atmost(lits, B)
    return c


def run(h: int, B: int, drat: bool, timeout: int = 36000):
    c = build(h, B)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        cnf = f.name
    c.dump(cnf)
    dr = cnf + ".drat"
    try:
        cmd = ["cadical", cnf, dr, "--binary=false"] if drat else ["cadical", cnf, "-q"]
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        st = next((ln for ln in r.stdout.splitlines() if ln.startswith("s ")), "打ち切り")
        ver = "-"
        size = "-"
        if drat and st == "s UNSATISFIABLE":
            size = subprocess.run(["du", "-h", dr], capture_output=True, text=True).stdout.split()[0]
            v = subprocess.run(["drat-trim", cnf, dr], capture_output=True, text=True,
                               timeout=timeout)
            ver = next((ln for ln in v.stdout.replace("\r", "").splitlines()
                        if ln in ("s VERIFIED", "s NOT VERIFIED")), "検証打ち切り")
        return st, size, ver, len(c.cls), c.n
    finally:
        os.unlink(cnf)
        if os.path.exists(dr):
            os.unlink(dr)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--B", type=int, required=True, help="この値でピーク<=B を試す")
    ap.add_argument("--drat", action="store_true")
    a = ap.parse_args()
    st, size, ver, ncl, nv = run(a.h, a.B, a.drat)
    print(f"h={a.h} peak<={a.B}: {st} / 節 {ncl} / 変数 {nv} / DRAT {size} / {ver}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
