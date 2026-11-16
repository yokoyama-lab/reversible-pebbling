#!/usr/bin/env python3
"""完全二分木の edge rank coloring 数 χ'_e を SAT+DRAT で求める。

なぜ要るか: KSS（Komarath–Sarma–Sawlani, JCSS 2019）の主定理
「根つき木の可逆ペブリング数 = 台の無向木の edge rank coloring 数 + 1」により、
**χ'_e が分かれば最適ペブル数が分かる**。$h\\ge4$ は総当たり（`calib_kss.py`）では届かない。

edge rank coloring: 辺に色 1..k を付け、**同色の 2 辺の間の路に必ずより大きい色の辺がある**。

符号化:
  - `c[e][i]` = 辺 e の色が i（ちょうど 1 つ）
  - `y[e][i]` = 辺 e の色が i より大きい（順序符号化。`y[e][i] ↔ ∨_{j>i} c[e][j]`）
  - 各辺対 (e,f) と各色 i について `c[e][i] ∧ c[f][i] → ∨_{g∈path(e,f)} y[g][i]`
    （path は e,f 自身を除く間の辺。空なら禁止＝同色にできない）

UNSAT は CaDiCaL の表示だけでは信じず、**drat-trim が `s VERIFIED` を返したときだけ**
下界として扱う（`exact-rev-complexity/scripts/sat_pebble.py` の配管をそのまま使う）。

    python3 sat_edgerank.py --h 4 --min
"""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

SCRIPTS = Path("<local>/dev/github.com/tetsuo-jp/exact-rev-complexity/scripts")
sys.path.insert(0, str(SCRIPTS))

import sat_pebble  # noqa: E402


def cbt_edges(h: int) -> list[tuple[int, int]]:
    """高さ h の完全二分木の辺。頂点 0 が根、子は 2v+1, 2v+2。辺は (子, 親)。"""
    n = 2 ** (h + 1) - 1
    return [(v, (v - 1) // 2) for v in range(1, n)]


def between(e1: tuple[int, int], e2: tuple[int, int]) -> set[tuple[int, int]]:
    """2 辺の**間**の辺（両端の 2 辺は含まない）。辺は子の側で代表する。"""
    def anc(v: int) -> list[int]:
        out = [v]
        while v != 0:
            v = (v - 1) // 2
            out.append(v)
        return out

    a, b = e1[0], e2[0]
    pa, pb = anc(a), anc(b)
    common = next(x for x in pa if x in pb)

    def up(v: int) -> list[tuple[int, int]]:
        out = []
        while v != common:
            out.append((v, (v - 1) // 2))
            v = (v - 1) // 2
        return out

    return (set(up(a)) | set(up(b))) - {e1, e2}


def encode(h: int, k: int) -> sat_pebble.Cnf:
    edges = cbt_edges(h)
    cnf = sat_pebble.Cnf()
    c = {(e, i): cnf.var() for e in edges for i in range(1, k + 1)}
    y = {(e, i): cnf.var() for e in edges for i in range(1, k + 1)}

    for e in edges:
        cnf.exactly_one([c[e, i] for i in range(1, k + 1)])
        for i in range(1, k + 1):
            higher = [c[e, j] for j in range(i + 1, k + 1)]
            # y[e,i] ↔ ∨_{j>i} c[e,j]
            for lit in higher:
                cnf.add(-lit, y[e, i])
            cnf.add_list([-y[e, i]] + higher)

    for e1, e2 in itertools.combinations(edges, 2):
        mid = between(e1, e2)
        for i in range(1, k + 1):
            cnf.add_list([-c[e1, i], -c[e2, i]] + [y[g, i] for g in mid])
    return cnf


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--k", type=int, help="この色数で塗れるかを 1 点だけ判定")
    ap.add_argument("--min", action="store_true", help="最小色数を求める")
    ap.add_argument("--timeout", type=float, default=1800.0)
    ap.add_argument("--workdir", default="sat_work")
    args = ap.parse_args()

    wd = Path(args.workdir)
    edges = cbt_edges(args.h)
    print(f"# 高さ {args.h} の完全二分木: 辺 {len(edges)} 本", flush=True)

    if args.k is not None:
        r = sat_pebble.run(encode(args.h, args.k), wd, f"er{args.h}_k{args.k}",
                           solver_timeout=args.timeout, checker_timeout=4 * args.timeout)
        print(f"k={args.k}: {r.verdict} ({r.solver_seconds:.1f}s, proof={r.proof_status})")
        return 0

    if not args.min:
        ap.error("--k か --min のどちらかが要る")

    k = 1
    while True:
        r = sat_pebble.run(encode(args.h, k), wd, f"er{args.h}_k{k}",
                           solver_timeout=args.timeout, checker_timeout=4 * args.timeout)
        print(f"  k={k}: {r.verdict} ({r.solver_seconds:.1f}s, proof={r.proof_status})",
              flush=True)
        if r.verdict == "SATISFIABLE":
            print(f"# χ'_e(h={args.h}) = {k}  ⇒ KSS より可逆ペブリング数 = {k + 1}")
            return 0
        if r.verdict != "UNSATISFIABLE":
            print("  打ち切り（値が無いのではなく未測定）")
            return 2
        k += 1


if __name__ == "__main__":
    sys.exit(main())
