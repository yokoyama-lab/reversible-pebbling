#!/usr/bin/env python3
"""完全二分木の根を最適ペブル数でペブルする最小手数を CP-SAT で求める。

素の SAT（`sat_treeroot.py`）は $h=4$・$k=155$ で歯が立たなかったので、
リポジトリにある CP-SAT の定式化（`exact-rev-complexity/scripts/cpsat_pebble.py`）を使う。

**役割分担**（`machine-checkable-work-ladder` の非対称性）:
  - **上界（手順を見つける）は CP-SAT でよい** — 出てきた手順は再生して検証できる
  - **下界（それ未満は不可能）は CP-SAT の OPTIMAL では足りない**。
    境界の 1 点だけ `sat_treeroot.py`（CaDiCaL + drat-trim）で UNSAT の証明ログを取る

必ず**既知の 4 点（h=1..4 で 5, 17, 53, 155）で校正してから** h=5 を信じること。

    .venv/bin/python cpsat_treeroot.py --h 4 --p 7
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

SCRIPTS = Path("<local>/dev/github.com/tetsuo-jp/exact-rev-complexity/scripts")
sys.path.insert(0, str(SCRIPTS))

import cpsat_pebble  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
from sat_treeroot import cbt_in_tree  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--horizon", type=int, default=None)
    ap.add_argument("--seconds", type=float, default=600.0)
    ap.add_argument("--workers", type=int, default=8)
    args = ap.parse_args()

    dag, root = cbt_in_tree(args.h)
    horizon = args.horizon
    if horizon is None:
        # ⚠ 地平線が足りないと INFEASIBLE が返る。これは「不可能」ではなく「未測定」。
        # 実測（h=1..4 で 5,17,53,155）は 4n では足りない（h=4 で 124 < 155）ので 8n を既定にする。
        horizon = 8 * dag.n
    t0 = time.monotonic()
    r = cpsat_pebble.solve(dag, root, args.p, 0, horizon=horizon,
                           max_seconds=args.seconds, workers=args.workers,
                           want_schedule=False)
    tight = "⚠ 地平線に張り付き（伸ばして再確認が要る）" if r.horizon_tight else "余裕あり"
    if r.status == "INFEASIBLE":
        tight = "⚠ INFEASIBLE は『不可能』ではなく**地平線不足の疑い**。伸ばして再確認すること"
    print(f"h={args.h} n={dag.n} p={args.p} 地平線={horizon}: "
          f"status={r.status} 手数={r.moves} ({time.monotonic() - t0:.1f}s) {tight}")
    return 0 if r.status == "OPTIMAL" else 2


if __name__ == "__main__":
    sys.exit(main())
