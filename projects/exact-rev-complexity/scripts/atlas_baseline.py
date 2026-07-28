"""資源アトラス Phase 3 — DP 系 5 族への厳密最適の基準線（docs/81 §3 Phase 3）。

Phase 2 の各点（実装の実測）に、依存 DAG 上の clean 可逆ペブリングの厳密値
（$p_{\\min}$・$M^*$・床 $2N-1$）を添える。**アトラス全体には基準線を付けられない**
（DAG 抽出が定義できない族があるため）。付けられる 5 族に限る。

族 → DAG の対応（docs/81 §2.1 の注釈つき部分集合に相当）:

| family | DAG | 実装側メモ配列 | 単位の注意 |
|---|---|---|---|
| fib_pairs_2017 | `chain(pairs)`, pairs=(n+1)/2 | `M` | **セル 2 個 = 1 対 = 1 節点**（÷2） |
| cutrod_linear | 完全履歴 DAG（節点 k の先行点 = 0..k−1 全部） | `r` | そのまま |
| edit_distance | `grid_dag(n+1,n+1)`（内部 $n^2$ 節点、基底は自由源） | `D` | 実装 moves は基底書き込み $2n$ を含む |
| lcs | `grid_dag(n+1,n+1)` | `L` | 同上 |
| knapsack | `knapsack_dag(wt, cap)`（wt=(i mod 3)+1, cap=n+2） | `K` | そのまま |

厳密値のエンジンは既存資産（`frontierdp_memo.bidir_bfs` / `pmin_bidir`。
素朴 BFS と全域一致済み＝候補 4 の検証）。**届かないサイズは空欄にする**（推定しない）。

    python3 scripts/atlas_baseline.py
"""

from __future__ import annotations

import csv
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

from atlas_measure import measure  # noqa: E402
from atlas_scale import FAMILIES, OUTDIR  # noqa: E402
from frontierdp_memo import bidir_bfs, pmin_bidir  # noqa: E402
from memo_dags import grid_dag, grid_target  # noqa: E402
from real_program_dags import knapsack_dag, knapsack_target  # noqa: E402
from revpebble import Dag, chain  # noqa: E402

MAX_PEBBLEABLE = 25  # これを超える DAG は基準線を計算しない（正直に空欄）。grid 7x7=36 は候補4で p_min>11 未確定の領域で時間切れになるため 25 に設定（2026-07-28 実測）


def cutrod_dag(n: int) -> Dag:
    """cut rod の完全履歴 DAG。節点 k (1..n) の先行点は 0..k-1 の全部、節点 0 は自由源。"""
    preds = [frozenset()] + [frozenset(range(k)) for k in range(1, n + 1)]
    return Dag(n=n + 1, preds=tuple(preds), free=frozenset({0}), name=f"cutrod({n})")


def dag_for(family: str, n: int):
    """(dag, target, 実装側メモ配列名, 実装→DAG 単位の除数)。"""
    if family == "fib_pairs_2017":
        pairs = (n + 1) // 2
        return chain(pairs), pairs, "M", 2
    if family == "cutrod_linear":
        return cutrod_dag(n), n, "r", 1
    if family == "edit_distance":
        # 実装の表は (n+1)×(n+1) で境界行・列（自明な基底）も書く。
        # DAG は基底を自由源とする内部 n×n = grid_dag(n+1,n+1)。
        # 実装側 moves には基底書き込み 2n 個が含まれる（findings で分けて報告）。
        return grid_dag(n + 1, n + 1), grid_target(n + 1, n + 1), "D", 1
    if family == "lcs":
        return grid_dag(n + 1, n + 1), grid_target(n + 1, n + 1), "L", 1
    if family == "knapsack":
        wt = [(i % 3) + 1 for i in range(1, n + 1)]
        return knapsack_dag(wt, n + 2), knapsack_target(wt, n + 2), "K", 1
    raise KeyError(family)


def baseline_row(family: str, n: int) -> dict:
    dag, target, arr, unit = dag_for(family, n)
    npeb = len(dag.pebbleable())
    row = {"family": family, "n": n, "dag_N": npeb,
           "p_min": "", "mstar": "", "floor": 2 * npeb - 1,
           "impl_moves": "", "impl_peak": "", "error": ""}
    fx = OUTDIR / f"{family}_{n}.janus"
    if fx.exists():
        m = measure(fx)
        a = m["arrays"].get(arr)
        if a:
            row["impl_moves"] = (a["puts"] + a["takes"]) // unit
            row["impl_peak"] = a["peak_nonzero"] // unit
        else:
            row["error"] = f"array {arr} not traced"
    else:
        row["error"] = "fixture missing"
    if npeb > MAX_PEBBLEABLE:
        row["error"] = (row["error"] + "; " if row["error"] else "") + \
            f"baseline skipped (N={npeb}>{MAX_PEBBLEABLE})"
        return row
    p = pmin_bidir(dag, target)
    row["p_min"] = p
    if p is not None:
        row["mstar"] = bidir_bfs(dag, target, p)
    return row


def main() -> None:
    fams = ["fib_pairs_2017", "cutrod_linear", "edit_distance", "lcs", "knapsack"]
    rows = []
    t0 = time.monotonic()
    for fam in fams:
        for n in FAMILIES[fam][1]:
            r = baseline_row(fam, n)
            rows.append(r)
            print(f"{fam} n={n}: N={r['dag_N']} p_min={r['p_min']} M*={r['mstar']} "
                  f"floor={r['floor']} impl={r['impl_moves']}@peak{r['impl_peak']} "
                  f"{r['error']}", flush=True)
    out = REPO / "data/atlas/baselines.csv"
    with out.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader(); w.writerows(rows)
    print(f"\n完了 ({time.monotonic()-t0:.0f} 秒) → {out}", flush=True)


if __name__ == "__main__":
    main()
