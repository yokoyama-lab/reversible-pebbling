#!/usr/bin/env python3
"""**帯状 DAG** で「レベル一様性」がどこで破れるかを測る（2026-08-14）。

層 `0..D` の各層に `w` 個の頂点を置き、層 `k` の頂点 `i` の親を
**層 `k-1` の連続する `b` 個**（境界で切り詰め）とする。

* `b = w`  → 全結合（`full_layered_reduction` が適用でき、レベル一様が最適）
* `b = 2`  → ピラミッドと同じ局所結合（レベル一様は $h=9$ で破れる）

**帯幅 `b` を動かして、レベル一様の最適値（＝機械証明つき上界）が
真の `p_min` から離れ始める点を探す。**

⚠ 最深層は 1 頂点にして sink を一意にする。
"""
import argparse
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import q2_cnf  # noqa: E402
from q2_level_weighted import solve as lvl  # noqa: E402


def build_band(D: int, w: int, b: int):
    """層 0..D。層 D は 1 頂点。層 k の頂点 i の親は層 k-1 の [i-b+1, i] ∩ 範囲。"""
    sizes = [w] * D + [1]
    idx, par, dep = [], [], []
    for k, n in enumerate(sizes):
        cur = []
        for i in range(n):
            cur.append(len(par))
            if k == 0:
                par.append([])
            else:
                prev = idx[k - 1]
                lo = max(0, i - b + 1) if len(prev) > 1 else 0
                hi = min(len(prev) - 1, i + b - 1) if len(prev) > 1 else 0
                # 連続する b 個（境界で切り詰め）。層 D は前層の全部を親にする
                if k == D:
                    sel = list(range(len(prev)))
                else:
                    sel = list(range(max(0, i - b + 1), min(len(prev), i + 1)))
                    if not sel:
                        sel = [min(i, len(prev) - 1)]
                par.append([prev[j] for j in sel])
            dep.append(k)
        idx.append(cur)
    return par, idx[-1][0], dep, sizes


def solve_sat(par, sink, p, T):
    c = q2_cnf.build(par, sink, p, T, window=True)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        path = f.name
    c.dump(path)
    try:
        r = subprocess.run(["cadical", path, "-q"], capture_output=True,
                           text=True, timeout=1800)
        out = [ln for ln in r.stdout.splitlines() if ln.startswith("s ")]
        return None if not out else ("SATISFIABLE" in out[0] and "UNSAT" not in out[0])
    finally:
        os.unlink(path)


def pmin_sat(par, sink, D, ub):
    T = 2 * D + 1
    for p in range(2, ub + 1):
        r = solve_sat(par, sink, p, T)
        if r is None:
            return None
        if r:
            return p
    return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--D", type=int, default=5)
    ap.add_argument("--w", type=int, default=5)
    a = ap.parse_args()
    print(f"  D={a.D} w={a.w}  （b=w が全結合・b=2 がピラミッド並みの局所結合）")
    print(f"  {'帯幅 b':>6} {'|V|':>5} {'レベル一様(上界)':>16} {'p_min(SAT)':>11} {'差':>4}")
    for b in range(2, a.w + 1):
        par, sink, dep, sizes = build_band(a.D, a.w, b)
        u, _ = lvl(sizes, 300.0)
        v = pmin_sat(par, sink, a.D, u)
        d = "—" if (v is None or u is None) else f"{u - v:+d}"
        print(f"  {b:>6} {len(par):>5} {str(u):>16} {str(v):>11} {d:>4}"
              + ("  ✔一致" if v == u else "  ✖離れた" if v else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
