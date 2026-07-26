"""候補1: 木・DAG 族のトレードオフ曲線 $p \\mapsto M^*(G,p)$ の厳密表。

`data/exp01_findings.md` の教訓（$M^*(p_{\\min})$ だけを見ると当てはめが崩れる）を踏まえ、
**$p_{\\min}$ の1点ではなく曲線全体**を出す。$p_{\\min}$ 自体が不規則に跳ぶので、
$p_{\\min}$ 基準の系列と絶対 $p$ 基準の系列の両方を見られるようにする。

出力: `data/exp01b_tradeoff.csv`（自動生成・手編集禁止）

実行: python3 scripts/exp01b_tradeoff.py [--extra 3] [--cap 40000000]
"""

from __future__ import annotations

import argparse
import csv
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import revpebble as rp  # noqa: E402
from exp01b_engine import (  # noqa: E402
    all_pebbled,
    butterfly,
    mstar_mask,
    pmin_mask,
    spinal_tree,
)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "exp01b_tradeoff.csv"


def cases() -> list[tuple[str, object, int]]:
    """(族名, Dag, 終端マスク) の列。"""
    out: list[tuple[str, object, int]] = []
    for n in range(1, 17):
        g = rp.chain(n)
        out.append(("chain", g, 1 << n))
    for h in range(1, 5):
        g = all_pebbled(rp.complete_binary_tree(h))
        out.append(("cbt*", g, 1 << (g.n - 1)))
    for h in range(1, 7):
        g = all_pebbled(rp.pyramid(h))
        out.append(("pyr*", g, 1 << (g.n - 1)))
    for h in range(1, 8):
        g = rp.pyramid(h)
        out.append(("pyr free-base", g, 1 << (g.n - 1)))
    for k in range(1, 9):
        g = spinal_tree(k)
        out.append(("spinal free-leaves", g, 1 << (g.n - 1)))
    for k in range(1, 9):
        g = all_pebbled(spinal_tree(k))
        out.append(("spinal*", g, 1 << (g.n - 1)))
    for k in range(1, 4):
        g = butterfly(k)
        w = 2**k
        goal = 0
        for j in range(w):
            goal |= 1 << (k * w + j)
        out.append(("butterfly all-outputs", g, goal))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--extra", type=int, default=3, help="p_min からいくつ上まで測るか")
    ap.add_argument("--cap", type=int, default=40_000_000, help="訪問状態数の上限")
    ap.add_argument("--budget", type=float, default=600.0, help="1ケースの秒数上限（超えたら打ち切り）")
    args = ap.parse_args()

    rows: list[dict] = []
    for fam, g, goal in cases():
        t0 = time.time()
        try:
            p0 = pmin_mask(g, goal)
        except RuntimeError as exc:
            print(f"{g.name}: p_min 到達できず（{exc}）", flush=True)
            rows.append({"family": fam, "name": g.name, "vertices": g.n, "p_min": "NR"})
            continue
        row: dict[str, object] = {
            "family": fam,
            "name": g.name,
            "vertices": g.n,
            "pebbleable": len(g.pebbleable()),
            "goal_size": bin(goal).count("1"),
            "p_min": p0,
        }
        if p0 is not None:
            for k in range(args.extra + 1):
                if time.time() - t0 > args.budget:
                    row[f"M*_p{k}"] = "TO"
                    break
                try:
                    row[f"M*_p{k}"] = mstar_mask(g, goal, p0 + k, cap=args.cap)
                except RuntimeError:
                    row[f"M*_p{k}"] = "NR"
                    break
        row["sec"] = round(time.time() - t0, 1)
        rows.append(row)
        print(
            f"{g.name:<26} V={g.n:<3} p_min={p0} "
            + " ".join(f"{row.get(f'M*_p{k}')}" for k in range(args.extra + 1))
            + f"  ({row['sec']}s)",
            flush=True,
        )

    fields = ["family", "name", "vertices", "pebbleable", "goal_size", "p_min"] + [
        f"M*_p{k}" for k in range(args.extra + 1)
    ] + ["sec"]
    with OUT.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        for r in rows:
            w.writerow(r)
    print(f"\n→ {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
