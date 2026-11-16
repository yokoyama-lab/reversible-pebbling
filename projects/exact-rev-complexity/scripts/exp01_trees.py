"""候補1 の初日実験: 木・ピラミッド族の厳密 p_min と M*、トレードオフ曲線。

出力: data/exp01_trees.csv（自動生成・手編集禁止）

正規化を2通り出す（docs/idea01_trees_dags.md の未決事項）:
  free_leaves=True  … 葉を常時可用な入力源としてペブル数に数えない
  free_leaves=False … 葉もペブル対象（Královič の流儀の可能性）

使い方:
    python3 scripts/exp01_trees.py            # 既定（軽い範囲）
    python3 scripts/exp01_trees.py --budget 20  # 探索する頂点数の上限を上げる
"""

from __future__ import annotations

import argparse
import csv
import sys
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag, bfs, chain, complete_binary_tree, pmin, pyramid

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "exp01_trees.csv"


def measure(dag: Dag, target: int, extra: int = 2) -> dict:
    """p_min と p_min..p_min+extra の M* を測る。"""
    p0 = pmin(dag, target)
    row: dict[str, object] = {
        "name": dag.name,
        "vertices": dag.n,
        "pebbleable": len(dag.pebbleable()),
        "p_min": p0,
    }
    if p0 is None:
        return row
    for k in range(extra + 1):
        moves, _ = bfs(dag, target, p0 + k)
        row[f"M*_p_min+{k}"] = moves
    return row


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--budget",
        type=int,
        default=17,
        help="ペブル対象頂点数の上限（2^budget が状態数。既定 17 で数秒〜数十秒）",
    )
    args = ap.parse_args()

    rows: list[dict] = []

    # (a) 鎖 — 先行プロジェクトの既知値。実装の妥当性確認を兼ねる。
    for n in range(1, 15):
        g = chain(n)
        rows.append(measure(g, n))

    # (b) 完全二分木 — 葉 free / 葉もペブル対象 の両流儀。
    for h in range(1, 8):
        g = complete_binary_tree(h)
        root = g.n - 1
        if len(g.pebbleable()) <= args.budget:
            rows.append(measure(g, root) | {"name": f"cbt({h}) free-leaves"})
        g2 = replace(g, free=frozenset(), name=f"cbt({h}) all-pebbled")
        if len(g2.pebbleable()) <= args.budget:
            rows.append(measure(g2, root))

    # (c) ピラミッド — 標準ペブリングの定番例との比較用。
    for h in range(1, 8):
        g = pyramid(h)
        apex = g.n - 1
        if len(g.pebbleable()) <= args.budget:
            rows.append(measure(g, apex) | {"name": f"pyr({h}) free-base"})
        g2 = replace(g, free=frozenset(), name=f"pyr({h}) all-pebbled")
        if len(g2.pebbleable()) <= args.budget:
            rows.append(measure(g2, apex))

    fields = ["name", "vertices", "pebbleable", "p_min", "M*_p_min+0", "M*_p_min+1", "M*_p_min+2"]
    OUT.parent.mkdir(exist_ok=True)
    with OUT.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        for r in rows:
            w.writerow(r)

    width = max(len(str(r["name"])) for r in rows)
    print(f"{'name':<{width}}  {'V':>3} {'p_min':>5} {'M*':>6} {'+1':>6} {'+2':>6}")
    for r in rows:
        print(
            f"{r['name']:<{width}}  {r['vertices']:>3} {str(r['p_min']):>5} "
            f"{str(r.get('M*_p_min+0')):>6} {str(r.get('M*_p_min+1')):>6} "
            f"{str(r.get('M*_p_min+2')):>6}"
        )
    print(f"\n→ {OUT.relative_to(ROOT)}")
    print("\n次の一手: p_min - h の段差が出る h を特定し、Královič の h+Theta(lg* h) と突き合わせる。")
    print("          M* の数列を OEIS 照合（docs/10_method_toolkit.md §3）。")


if __name__ == "__main__":
    main()
