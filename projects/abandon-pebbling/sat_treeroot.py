#!/usr/bin/env python3
"""完全二分木の根を**最適ペブル数**でペブルする最小手数を SAT+DRAT で求める。

なぜ SAT か: 素の Dijkstra は $h=4$（$n=31$）で 2000 万状態・24GB に達して届かない。
SAT なら変数は $O(nk)$ で済み、**UNSAT 側に drat-trim の証明ログが付く**
（下界を主張するには証明ログが要る。`machine-checkable-work-ladder`）。

符号化は `exact-rev-complexity/scripts/sat_pebble.py` をそのまま使う（再実装しない）。
約束: 空盤から始め、最後は**目標だけ**がペブル済み（KSS の約束＝`abandon.py --final keep`）。
**根も葉もペブルを消費する**（`free=∅`）。この約束で KSS の定理
「可逆ペブリング数 = edge rank coloring 数 + 1」と 3 点一致することを確認済み（README §5-5）。

    python3 sat_treeroot.py --h 3 --p 6 --minmoves
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

SCRIPTS = Path("<local>/dev/github.com/tetsuo-jp/exact-rev-complexity/scripts")
sys.path.insert(0, str(SCRIPTS))

import sat_pebble  # noqa: E402
from revpebble import Dag  # noqa: E402


def cbt_in_tree(h: int) -> tuple[Dag, int]:
    """高さ h の完全二分木（葉が source、根が sink）。**free は空**。

    頂点番号は葉から根へ。返り値は (dag, 根の番号)。
    """
    levels: list[list[int]] = []
    counter = 0
    for lv in range(h, -1, -1):
        levels.append([])
        for _ in range(2**lv):
            levels[-1].append(counter)
            counter += 1
    preds: list[frozenset[int]] = [frozenset() for _ in range(counter)]
    for depth in range(1, len(levels)):
        children = levels[depth - 1]
        parents = levels[depth]
        for j, v in enumerate(parents):
            preds[v] = frozenset({children[2 * j], children[2 * j + 1]})
    root = levels[-1][0]
    return Dag(n=counter, preds=tuple(preds), free=frozenset(), name=f"cbt{h}"), root


def decide(h: int, p: int, k: int, workdir: Path, *, timeout: float,
           verify: bool = True) -> sat_pebble.SatResult:
    dag, root = cbt_in_tree(h)
    enc = sat_pebble.encode(dag, root, p, 0, k)
    return sat_pebble.run(enc, workdir, f"cbt{h}_p{p}_k{k}",
                          solver_timeout=timeout, checker_timeout=4 * timeout,
                          verify_proof=verify)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--k", type=int, help="この手数で可能かを 1 点だけ判定")
    ap.add_argument("--minmoves", action="store_true",
                    help="最小手数を求める（上へ伸ばして SAT を見つけ、直下の UNSAT を証明）")
    ap.add_argument("--lo", type=int, default=1, help="minmoves の探索開始")
    ap.add_argument("--hi", type=int, default=4000)
    ap.add_argument("--timeout", type=float, default=3600.0)
    ap.add_argument("--workdir", default="sat_work")
    args = ap.parse_args()

    wd = Path(args.workdir)
    dag, root = cbt_in_tree(args.h)
    print(f"# 完全二分木 h={args.h}: 頂点 {dag.n} 個・根 {root}・free なし, p={args.p}",
          flush=True)

    if args.k is not None:
        r = decide(args.h, args.p, args.k, wd, timeout=args.timeout)
        print(f"k={args.k}: {r.verdict} "
              f"(solver {r.solver_seconds:.1f}s, proof={r.proof_status})", flush=True)
        return 0

    if not args.minmoves:
        ap.error("--k か --minmoves のどちらかが要る")

    # 1) SAT になる k を見つける（下から倍々で伸ばす）
    lo, hi = args.lo, None
    k = max(args.lo, 2 * dag.n - 1)
    while k <= args.hi:
        r = decide(args.h, args.p, k, wd, timeout=args.timeout, verify=False)
        print(f"  探索 k={k}: {r.verdict} ({r.solver_seconds:.1f}s)", flush=True)
        if r.verdict == "SATISFIABLE":
            hi = k
            break
        if r.verdict == "UNKNOWN":
            print("  打ち切り（値が無いのではなく未測定）", flush=True)
            return 2
        lo = k + 1
        k = k * 2 if k > 0 else 1
    if hi is None:
        print("  上限まで SAT が見つからなかった（未測定）", flush=True)
        return 2

    # 2) 二分探索で最小 k を決める
    while lo < hi:
        mid = (lo + hi) // 2
        r = decide(args.h, args.p, mid, wd, timeout=args.timeout, verify=False)
        print(f"  二分 k={mid}: {r.verdict} ({r.solver_seconds:.1f}s)", flush=True)
        if r.verdict == "SATISFIABLE":
            hi = mid
        elif r.verdict == "UNSATISFIABLE":
            lo = mid + 1
        else:
            print("  打ち切り（未測定）", flush=True)
            return 2

    # 3) 下界に証明ログを付ける（k-1 が UNSAT であることを drat-trim で検査）
    print(f"# 最小手数 = {lo}", flush=True)
    if lo >= 1:
        r = decide(args.h, args.p, lo - 1, wd, timeout=args.timeout, verify=True)
        print(f"# 下界の証明: k={lo - 1} は {r.verdict} / drat-trim: {r.proof_status}",
              flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
