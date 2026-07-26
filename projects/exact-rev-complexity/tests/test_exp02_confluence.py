"""候補2: 合流コスト定量化ヘルパーの回帰テスト（テストファースト）。"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from exp02_confluence import (  # noqa: E402
    chain_r,
    depth_edges,
    max_antichain,
    num_branch,
    num_confluent,
    residual,
)
from exp02_dags import edges_to_dag  # noqa: E402
from revpebble import pmin as pmin_rev  # noqa: E402
from stdpebble import pmin_std  # noqa: E402


def test_depth_of_chain_equals_edge_count() -> None:
    for m in range(0, 6):
        edges = frozenset((i, i + 1) for i in range(m))
        assert depth_edges(edges, m + 1) == m


def test_confluence_and_branch_on_minimal_branching_separator() -> None:
    """n=4 の最小の「分岐を持つ分離」例 {0->2,1->2,2->3}（data/exp02_results.md ③）。

    頂点2が入次数2（合流）、出次数はどの頂点も1（再利用なし）。
    """
    edges = frozenset({(0, 2), (1, 2), (2, 3)})
    n = 4
    assert num_confluent(edges, n) == 1
    assert num_branch(edges, n) == 0
    assert max_antichain(edges, n) == 2  # {0,1} は互いに到達不能


def test_confluence_zero_for_pure_chain() -> None:
    edges = frozenset({(0, 1), (1, 2), (2, 3)})
    n = 4
    assert num_confluent(edges, n) == 0
    assert num_branch(edges, n) == 0
    assert max_antichain(edges, n) == 1


def test_chain_r_matches_pmin_rev_directly() -> None:
    for m in range(0, 6):
        edges = frozenset((i, i + 1) for i in range(m))
        g = edges_to_dag(edges, m + 1)
        expected = pmin_rev(g, m) if m > 0 else 1
        assert chain_r(m) == expected


def test_residual_zero_for_pure_chain() -> None:
    """鎖自身は depth=辺数なので chainR(depth) が丁度 R に等しく残差0になる。"""
    for m in range(1, 6):
        edges = frozenset((i, i + 1) for i in range(m))
        n = m + 1
        g = edges_to_dag(edges, n)
        p = pmin_std(g, n - 1)
        r = pmin_rev(g, n - 1)
        assert residual(edges, n, p, r) == 0


def test_residual_positive_on_known_counterexample() -> None:
    """data/exp02_results.md ④ の仮説3反例: n=4 {0->2,1->2,2->3} で残差が正になる。"""
    edges = frozenset({(0, 2), (1, 2), (2, 3)})
    n = 4
    g = edges_to_dag(edges, n)
    p = pmin_std(g, n - 1)
    r = pmin_rev(g, n - 1)
    assert (p, r) == (3, 4)
    assert residual(edges, n, p, r) == 1


if __name__ == "__main__":
    import traceback

    tests = [v for k, v in list(globals().items()) if k.startswith("test_")]
    failed = 0
    for t in tests:
        try:
            t()
            print(f"OK   {t.__name__}")
        except AssertionError:
            failed += 1
            print(f"FAIL {t.__name__}")
            traceback.print_exc()
    print(f"\n{len(tests) - failed}/{len(tests)} passed")
    sys.exit(1 if failed else 0)
