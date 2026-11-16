#!/usr/bin/env python3
"""CNF の**構文的な自己同型群の位数を実際に測る**（2026-09-05）。

「ピラミッドの UNSAT は対称性が巨大なので DPR なら短くなる」という見込みを、
言葉ではなく数で確かめるための道具。標準の CNF→彩色グラフ還元を作り、**nauty
（`dreadnaut`）を実際に呼ぶ**。

⚠ この研究室には「nauty で同型を割った」と書いて nauty を一度も呼んでいなかった前例がある。
そこで **`--selftest` で位数が既知のグラフ（三角形 6・P3 2・K4 24・C5 10・K3,3 72）を
先に通す**。ここが合わなければ以降の数字は使わない。

還元（Crawford 1992 / Aloul 2003 と同じ）:
  * 変数 i に節点 2 つ（x_i と ¬x_i）。両者を辺で結ぶ（極性反転の対称性を許す）
  * 節 c に節点 1 つ。その節に現れるリテラル節点と結ぶ
  * 色: リテラル節点と節節点を分ける（2 項節と変数辺の混同を防ぐ）
位数には**極性反転**も含まれる（純粋な変数置換だけの部分群ではない）。
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

GRPSIZE = re.compile(r"grpsize=([0-9.e+]+)")


def run_dreadnaut(nodes: int, adj: dict[int, set[int]], colors: list[list[int]],
                  timeout: int = 1800) -> tuple[float, str]:
    lines = [f"n={nodes} g"]
    for v in range(nodes):
        nb = sorted(x for x in adj.get(v, ()) if x > v)
        lines.append(f"{v}: {' '.join(map(str, nb))};")
    lines.append(".")
    lines.append("f=[" + "|".join(",".join(map(str, c)) for c in colors) + "]")
    lines.append("c x")
    lines.append("q")
    inp = "\n".join(lines) + "\n"
    r = subprocess.run(["dreadnaut"], input=inp, capture_output=True, text=True,
                       timeout=timeout)
    m = GRPSIZE.search(r.stdout)
    if not m:
        return -1.0, (r.stdout + r.stderr)[-300:]
    return float(m.group(1)), ""


def selftest() -> int:
    """位数が既知のグラフで dreadnaut の呼び出しと読み取りを校正する。"""
    cases = [
        ("三角形 K3", 3, [(0, 1), (1, 2), (0, 2)], 6.0),
        ("道 P3", 3, [(0, 1), (1, 2)], 2.0),
        ("K4", 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 24.0),
        ("閉路 C5", 5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], 10.0),
        ("K3,3", 6, [(i, 3 + j) for i in range(3) for j in range(3)], 72.0),
    ]
    bad = 0
    for name, n, edges, want in cases:
        adj: dict[int, set[int]] = {i: set() for i in range(n)}
        for a, b in edges:
            adj[a].add(b)
            adj[b].add(a)
        got, err = run_dreadnaut(n, adj, [list(range(n))])
        ok = abs(got - want) < 1e-6
        bad += 0 if ok else 1
        print(f"  [{'OK ' if ok else '**NG**'}] {name}: 位数 {got}（既知 {want}）{err}")
    print("校正 OK（dreadnaut を実際に呼び、位数を読めている）" if bad == 0
          else f"**校正 NG: {bad} 件。以降の位数を使ってはいけない**")
    return bad


def cnf_group(nvars: int, clauses: list[list[int]], timeout: int = 1800):
    """(位数, 節点数)。リテラル節点 2n ＋ 節節点 m。"""
    def lit(l: int) -> int:                    # x_i -> 2(i-1), ~x_i -> 2(i-1)+1
        return 2 * (abs(l) - 1) + (0 if l > 0 else 1)

    n_nodes = 2 * nvars + len(clauses)
    adj: dict[int, set[int]] = {}

    def link(a, b):
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)

    for i in range(nvars):
        link(2 * i, 2 * i + 1)
    for ci, c in enumerate(clauses):
        cn = 2 * nvars + ci
        for l in c:
            link(cn, lit(l))
    colors = [list(range(2 * nvars)), list(range(2 * nvars, n_nodes))]
    g, err = run_dreadnaut(n_nodes, adj, colors, timeout)
    return g, n_nodes, err


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--hs", default="3,4,5")
    ap.add_argument("--timeout", type=int, default=1800)
    a = ap.parse_args()
    if a.selftest:
        return 1 if selftest() else 0

    import q2_cnf
    import pbcert_pyr_opb as enc
    from pbcert_measure import L_ABSTRACT

    P_MIN = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16}   # 実測 p_min（q2_pyr_lower.MEASURED）
    print(f"  {'系':<34} {'変数':>7} {'節':>8} {'節点':>8} {'自己同型群の位数':>16}")
    for h in [int(x) for x in a.hs.split(",")]:
        # (a) 抽象 CNF（DRAT 基準線が使っているもの）
        nv, cls = enc.build(h, L_ABSTRACT[h] - 1).to_cnf()
        g, nn, err = cnf_group(nv, cls, a.timeout)
        print(f"  {f'抽象 CNF h={h} B={L_ABSTRACT[h]-1}':<34} {nv:>7} {len(cls):>8} {nn:>8} "
              f"{g:>16} {err}")

        # (b) 本物のペブリング CNF（x[v][t]。ピラミッドの鏡映が効きうる側）
        if h in P_MIN:
            par, sk = q2_cnf.pyramid(h)
            T = 2 * (h - 1) + 1
            c = q2_cnf.build(par, sk, P_MIN[h] - 1, T, window=True)
            g2, nn2, err2 = cnf_group(c.n, c.cls, a.timeout)
            print(f"  {f'ペブリング CNF h={h} p={P_MIN[h]-1}':<34} {c.n:>7} {len(c.cls):>8} "
                  f"{nn2:>8} {g2:>16} {err2}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
