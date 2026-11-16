"""候補2: 標準 vs 可逆ペブル数の分離 onset — 小 DAG 全数探索の実験ドライバ。

docs/idea02_separation_onset.md 準拠。本命の問いは差の大きさではなく
「R(G)=P(G) となる DAG の構造的特徴付け」（§4）。

## 使い方

```bash
python3 scripts/exp02_separation.py                  # n<=6 を全数・厳密に（既定, 数十秒）
python3 scripts/exp02_separation.py --nmax 5          # 上限を下げる
python3 scripts/exp02_separation.py --raw7 --budget 480  # n=7 の時間制限つき部分スキャン（重複除去なし）
```

n<=6 は `exp02_dags.enumerate_nonisomorphic` で非同型類まで厳密に還元する
（数十秒で終わる）。n=7 は同型除去の順列探索が (n-1)!=720 通り×約61万候補で
単体では10分を超えるため、既定では実行しない。`--raw7` は同型除去を行わない
「生ラベル付きスキャン」（時間制限つき）で、存在性の探索
（分離の実例・R-P最大化・R=P反例）だけを行う。件数の主張（非同型類の個数）は
n<=6 のみで行う。
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp02_dags import edges_to_dag, enumerate_nonisomorphic, generate_labeled  # noqa: E402
from revpebble import pmin as pmin_rev  # noqa: E402
from stdpebble import pmin_std  # noqa: E402


def max_outdeg_nonsink(edges: frozenset[tuple[int, int]], n: int) -> int:
    """非シンク頂点(0..n-2)の出次数の最大値。木（各非シンク頂点の出次数=1）なら 1。"""
    outdeg = [0] * (n - 1) if n > 1 else []
    for i, j in edges:
        if i < n - 1:
            outdeg[i] += 1
    return max(outdeg) if outdeg else 0


def is_intree(edges: frozenset[tuple[int, int]], n: int) -> bool:
    """全ての非シンク頂点の出次数が1（=シンクへの in-tree／各値が1回だけ使われる）。"""
    return n <= 1 or max_outdeg_nonsink(edges, n) <= 1


def run_exact(nmax: int) -> dict[int, list[tuple[frozenset, int, int]]]:
    """n=1..nmax の非同型 DAG 全数について (edges, P, R) を厳密計算する。"""
    results: dict[int, list[tuple[frozenset, int, int]]] = {}
    for n in range(1, nmax + 1):
        rows = []
        for edges in enumerate_nonisomorphic(n):
            g = edges_to_dag(edges, n)
            target = n - 1
            p = pmin_std(g, target)
            r = pmin_rev(g, target)
            assert p is not None and r is not None
            rows.append((edges, p, r))
        results[n] = rows
    return results


def summarize_exact(results: dict[int, list[tuple[frozenset, int, int]]]) -> None:
    print("=== n<=nmax 厳密全数（非同型類）===")
    first_separation: tuple[int, frozenset] | None = None
    max_gap = -1
    max_gap_graph: tuple[int, frozenset] | None = None
    tree_iff_rp_holds = True
    counterexamples: list[tuple[int, frozenset, int, int, int]] = []

    for n, rows in results.items():
        dist: dict[tuple[int, int], int] = {}
        for edges, p, r in rows:
            dist[(p, r)] = dist.get((p, r), 0) + 1
            if r > p and first_separation is None:
                first_separation = (n, edges)
            if r - p > max_gap:
                max_gap = r - p
                max_gap_graph = (n, edges)
            tree = is_intree(edges, n)
            eq = p == r
            if tree != eq:
                tree_iff_rp_holds = False
                counterexamples.append((n, edges, p, r, max_outdeg_nonsink(edges, n)))
        print(f"n={n}: classes={len(rows)} dist(P,R)={sorted(dist.items())}")

    print()
    print(f"最初の分離 (R>P) が起きる最小 n: {first_separation}")
    print(f"R-P 最大: {max_gap}  グラフ: {max_gap_graph}")
    print(f"「R=P <=> 各非シンク頂点の出次数<=1(in-tree)」が全データで成立: {tree_iff_rp_holds}")
    if counterexamples:
        print(f"反例 {len(counterexamples)} 件（先頭5件）: {counterexamples[:5]}")


def run_raw7(budget_sec: float) -> None:
    """n=7 の時間制限つき生ラベル付きスキャン（同型除去なし）。存在性の探索専用。"""
    print(f"=== n=7 raw scan (budget={budget_sec:.0f}s, 同型除去なし・存在性探索のみ) ===")
    t0 = time.time()
    n = 7
    target = n - 1
    labeled = generate_labeled(n)
    print(f"labeled candidates: {len(labeled)} (生成時間 {time.time() - t0:.1f}s)")

    processed = 0
    max_gap = -1
    max_gap_edges: frozenset | None = None
    separation_found = False
    tree_counterexamples: list[tuple[frozenset, int, int]] = []
    nontree_equal_examples: list[tuple[frozenset, int, int]] = []
    timed_out = False

    t1 = time.time()
    for edges in labeled:
        if time.time() - t1 > budget_sec:
            timed_out = True
            break
        g = edges_to_dag(edges, n)
        p = pmin_std(g, target)
        r = pmin_rev(g, target)
        assert p is not None and r is not None
        processed += 1
        if r > p:
            separation_found = True
        if r - p > max_gap:
            max_gap = r - p
            max_gap_edges = edges
        tree = is_intree(edges, n)
        eq = p == r
        if tree and not eq:
            tree_counterexamples.append((edges, p, r))
        if (not tree) and eq and len(nontree_equal_examples) < 20:
            nontree_equal_examples.append((edges, p, r))

    dt = time.time() - t1
    print(f"processed={processed}/{len(labeled)} ({100 * processed / len(labeled):.1f}%) in {dt:.1f}s"
          + (" [TIMED OUT]" if timed_out else " [完了]"))
    print(f"分離 (R>P) の存在: {separation_found}")
    print(f"R-P 最大 (処理済み範囲): {max_gap}  グラフ: {max_gap_edges}")
    print(f"tree(outdeg<=1) だが R!=P の反例数: {len(tree_counterexamples)} (先頭3件: {tree_counterexamples[:3]})")
    print(
        f"非 tree (分岐あり) だが R=P の例: {len(nontree_equal_examples)} 件見つかった"
        f"（先頭5件: {nontree_equal_examples[:5]})"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--nmax", type=int, default=6)
    parser.add_argument("--raw7", action="store_true")
    parser.add_argument("--budget", type=float, default=480.0, help="raw7 の時間予算(秒)")
    args = parser.parse_args()

    results = run_exact(args.nmax)
    summarize_exact(results)

    if args.raw7:
        print()
        run_raw7(args.budget)
