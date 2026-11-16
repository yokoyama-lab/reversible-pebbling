"""Phase 3（基準線）の回帰テスト。族→DAG 対応が既知値を再現することを固定する。

    python3 tests/test_atlas_baseline.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from atlas_baseline import cutrod_dag, dag_for  # noqa: E402
from frontierdp_memo import bidir_bfs, pmin_bidir  # noqa: E402


def test_fib_pairs_mapping_reproduces_known_chain_values() -> None:
    """n=9 → 対 5 → 鎖 5: p_min=4・M*=11（exp51 §7.2 の確定値）。"""
    dag, target, arr, unit = dag_for("fib_pairs_2017", 9)
    assert (target, arr, unit) == (5, "M", 2)
    p = pmin_bidir(dag, target)
    assert p == 4, p
    assert bidir_bfs(dag, target, p) == 11


def test_cutrod_dag_is_complete_history() -> None:
    """完全履歴 DAG: p_min = n（全先行点を同時に要する）・M* = 2n-1。"""
    for n in (3, 5, 7):
        d = cutrod_dag(n)
        p = pmin_bidir(d, n)
        assert p == n, (n, p)
        assert bidir_bfs(d, n, p) == 2 * n - 1, n


def test_knapsack_mapping_runs() -> None:
    dag, target, arr, unit = dag_for("knapsack", 3)
    p = pmin_bidir(dag, target)
    assert p is not None and bidir_bfs(dag, target, p) is not None


def test_dag_is_restricted_to_ancestors_of_target() -> None:
    """目標に寄与しない頂点は DAG に残さない。

    knapsack は表全体を頂点にするが、目標セル dp[n][cap] の祖先は一部でしかない。
    非祖先を N に数えると床 2N-1 が過大になり、M* を上回って矛盾する。
    """
    dag, target, _, _ = dag_for("knapsack", 3)
    assert len(dag.pebbleable()) == 7, len(dag.pebbleable())
    # 格子と鎖は全頂点が目標の祖先なので、制限しても頂点数は変わらない。
    assert len(dag_for("edit_distance", 3)[0].pebbleable()) == 9
    assert len(dag_for("fib_pairs_2017", 13)[0].pebbleable()) == 7


def test_restriction_preserves_pmin_and_mstar() -> None:
    """祖先への制限は p_min と M* を変えない（非祖先は最適戦略で一度も置かれない）。"""
    dag, target, _, _ = dag_for("knapsack", 3)
    p = pmin_bidir(dag, target)
    assert p == 5, p
    assert bidir_bfs(dag, target, p) == 17


def test_floor_never_exceeds_mstar() -> None:
    """床 2N-1 はクリーンな計画の下限なので、厳密最適 M* を上回ってはならない。"""
    for family, n in (("knapsack", 2), ("knapsack", 3),
                      ("fib_pairs_2017", 9), ("fib_pairs_2017", 13),
                      ("edit_distance", 3), ("lcs", 3)):
        dag, target, _, _ = dag_for(family, n)
        floor = 2 * len(dag.pebbleable()) - 1
        p = pmin_bidir(dag, target)
        mstar = bidir_bfs(dag, target, p)
        assert floor <= mstar, (family, n, floor, mstar)


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn(); print(f"ok   {name}")
            except AssertionError as exc:
                failures += 1; print(f"FAIL {name}: {exc}")
            except Exception as exc:
                failures += 1; print(f"ERROR {name}: {type(exc).__name__}: {exc}")
    sys.exit(1 if failures else 0)
