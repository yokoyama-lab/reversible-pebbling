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
