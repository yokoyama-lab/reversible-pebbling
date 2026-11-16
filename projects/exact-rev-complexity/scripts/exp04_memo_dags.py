"""候補4 の実験: メモ化 DP 依存 DAG（Fibonacci型・グリッド型・パスカル型）の厳密 p_min・M*。

出力: data/exp04_fib.csv, data/exp04_grid.csv, data/exp04_pascal.csv（自動生成・手編集禁止）

使い方:
    python3 scripts/exp04_memo_dags.py                  # 既定（軽い範囲）
    python3 scripts/exp04_memo_dags.py --fib-nmax 24     # fib 型の n 上限を上げる
    python3 scripts/exp04_memo_dags.py --grid-max 5      # グリッド型の辺長上限（正方形 k x k）

注意: 素朴 BFS は状態空間 2^(pebbleable数) を全探索する。fib(n) は帯幅2なので
pebbleable = n-1 個で済み、n=29 程度まで数分で届く（data/exp04_results.md 参照）。
grid(k,k) は pebbleable が O(k^2) で伸びるため k=5 (pebbleable=16) が素朴 BFS の実用上限。
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from memo_dags import fib_dag, grid_dag, grid_target, pascal_dag, pascal_target  # noqa: E402
from revpebble import bfs, pmin  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]


def measure(g, target: int, extra: int = 2) -> dict:
    p0 = pmin(g, target)
    row: dict[str, object] = {
        "name": g.name,
        "vertices": g.n,
        "pebbleable": len(g.pebbleable()),
        "p_min": p0,
    }
    if p0 is None:
        return row
    for k in range(extra + 1):
        moves, _ = bfs(g, target, p0 + k)
        row[f"M*_p_min+{k}"] = moves
    return row


def write_csv(path: Path, rows: list[dict]) -> None:
    fields = ["name", "vertices", "pebbleable", "p_min", "M*_p_min+0", "M*_p_min+1", "M*_p_min+2"]
    path.parent.mkdir(exist_ok=True)
    with path.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        for r in rows:
            w.writerow(r)


def print_table(rows: list[dict]) -> None:
    width = max(len(str(r["name"])) for r in rows)
    print(f"{'name':<{width}}  {'V':>4} {'pbl':>4} {'p_min':>5} {'M*':>6} {'+1':>6} {'+2':>6}")
    for r in rows:
        print(
            f"{r['name']:<{width}}  {r['vertices']:>4} {r['pebbleable']:>4} "
            f"{str(r['p_min']):>5} {str(r.get('M*_p_min+0')):>6} "
            f"{str(r.get('M*_p_min+1')):>6} {str(r.get('M*_p_min+2')):>6}"
        )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--fib-nmax", type=int, default=24, help="fib 型の n 上限")
    ap.add_argument("--grid-max", type=int, default=4, help="grid(k,k) の k 上限")
    ap.add_argument("--pascal-nmax", type=int, default=8, help="pascal 型の n 上限")
    ap.add_argument("--budget", type=int, default=20, help="pebbleable 頂点数の上限（安全弁）")
    args = ap.parse_args()

    print("=== fib 型 ===")
    fib_rows = []
    for n in range(1, args.fib_nmax + 1):
        g = fib_dag(n)
        if len(g.pebbleable()) > args.budget:
            print(f"  fib({n}): pebbleable={len(g.pebbleable())} > budget, skip")
            continue
        fib_rows.append(measure(g, n))
    print_table(fib_rows)
    write_csv(ROOT / "data" / "exp04_fib.csv", fib_rows)

    print("\n=== grid 型（正方 k x k） ===")
    grid_rows = []
    for k in range(1, args.grid_max + 1):
        g = grid_dag(k, k)
        t = grid_target(k, k)
        if len(g.pebbleable()) > args.budget:
            print(f"  grid({k},{k}): pebbleable={len(g.pebbleable())} > budget, skip")
            continue
        grid_rows.append(measure(g, t))
    print_table(grid_rows)
    write_csv(ROOT / "data" / "exp04_grid.csv", grid_rows)

    print("\n=== pascal 型（中央二項係数 C(n,n//2)） ===")
    pascal_rows = []
    for n in range(1, args.pascal_nmax + 1):
        g = pascal_dag(n)
        t = pascal_target(n)
        if len(g.pebbleable()) > args.budget:
            print(f"  pascal({n}): pebbleable={len(g.pebbleable())} > budget, skip")
            continue
        pascal_rows.append(measure(g, t))
    print_table(pascal_rows)
    write_csv(ROOT / "data" / "exp04_pascal.csv", pascal_rows)

    print(f"\n→ data/exp04_fib.csv, data/exp04_grid.csv, data/exp04_pascal.csv")
    print("次の一手: data/exp04_results.md を参照（OEIS 照合・フロンティア DP は未着手）。")


if __name__ == "__main__":
    main()
