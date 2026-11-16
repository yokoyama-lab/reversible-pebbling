"""data/exp03_reach.csv の厳密値 reach(p,e) を再計算して照合する（CSV は書き換えない）。

出口台帳 X-erasure-pebbling-01 の証拠用。表 reach.tex（gen_tables.py）が読む列を、
同じ BFS（landauer.reach_e）で作り直し、全行一致を確かめる。打ち切り長に当たれば失敗。

    python3 scripts/recheck_reach_csv.py [--nmax 200]
"""

from __future__ import annotations

import argparse
import csv
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
sys.path.insert(0, str(REPO / "src"))
import landauer as ld  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=200)
    a = ap.parse_args()
    t0 = time.time()
    bad = 0
    with (REPO / "data/exp03_reach.csv").open() as fh:
        data = list(csv.DictReader(fh))
    for r in data:
        p, e = int(r["p"]), int(r["e"])
        got = ld.reach_e(p, e, nmax=a.nmax)
        if got >= a.nmax:
            print(f"TRUNCATED p={p} e={e} (nmax={a.nmax})")
            return 2
        ok = got == int(r["reach"])
        bad += not ok
        print(f"{'ok ' if ok else 'BAD'} p={p} e={e} csv={r['reach']} recomputed={got}")
    print(f"{len(data) - bad}/{len(data)} rows agree; {time.time() - t0:.1f}s")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
