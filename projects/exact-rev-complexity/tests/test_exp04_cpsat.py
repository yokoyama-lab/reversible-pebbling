"""候補4: CP-SAT retention interval 定式化（`scripts/cpsat_interval.py`, team-lead 管理・
編集禁止）を、自分のメモ DAG（fib/grid/pascal）に適用したときのクロスバリデーション。

⚠️ ortools が必要。実行は `.venv/bin/python tests/test_exp04_cpsat.py`
（plain `python3` では ImportError になる。プロジェクト規約どおり冒頭に明記）。

方針（`docs/10_method_toolkit.md` (2) 二重実装で照合）:
- $e=0$: 既に BFS で確定済みの値（`tests/test_exp04_memo_dags.py`,
  `data/exp04_results.md`）と全点一致することを確認する。
- $e>0$: 候補3 の `scripts/landauer.py`（読むだけ・編集しない）の素朴 BFS
  `landauer_bfs` と、小さい $n$ で全点一致することを確認する。
一致しない領域の値は使わない・公表しない。
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from cpsat_interval import solve_intervals_auto  # noqa: E402
from landauer import landauer_bfs  # noqa: E402  (候補3, 読むだけ)
from memo_dags import fib_dag, grid_dag, grid_target, pascal_dag, pascal_target  # noqa: E402
from revpebble import pmin  # noqa: E402

# fib/grid/pascal の e=0（通常の可逆ペブリング）での既知の厳密値
# （data/exp04_results.md, tests/test_exp04_memo_dags.py と同じ数値）。
FIB_KNOWN = {3: 3, 5: 7, 8: 17}
GRID_KNOWN = {2: 1, 3: 7, 4: 25}
PASCAL_KNOWN = {2: 1, 3: 3, 4: 7, 5: 13}


def test_cpsat_matches_known_fib_e0() -> None:
    for n, want in FIB_KNOWN.items():
        g = fib_dag(n)
        p = pmin(g, n)
        r = solve_intervals_auto(g, n, p, e=0, max_seconds=30)
        assert r.moves == want, (n, r.moves, want, r.status)


def test_cpsat_matches_known_grid_e0() -> None:
    for k, want in GRID_KNOWN.items():
        g = grid_dag(k, k)
        t = grid_target(k, k)
        p = pmin(g, t)
        r = solve_intervals_auto(g, t, p, e=0, max_seconds=60)
        assert r.moves == want, (k, r.moves, want, r.status)


def test_cpsat_matches_known_pascal_e0() -> None:
    for n, want in PASCAL_KNOWN.items():
        g = pascal_dag(n)
        t = pascal_target(n)
        p = pmin(g, t)
        r = solve_intervals_auto(g, t, p, e=0, max_seconds=30)
        assert r.moves == want, (n, r.moves, want, r.status)


def test_cpsat_matches_landauer_bfs_fib_with_erasure() -> None:
    """e>0（消去予算あり）で、候補3 の素朴 BFS と一致するか（小さい n のみ）。"""
    g = fib_dag(8)
    p = pmin(g, 8)  # p_min（e=0 のときの最小ピーク）で固定し、e だけ動かす
    for e in (0, 1, 2, 4):
        want = landauer_bfs(g, 8, p, e)
        r = solve_intervals_auto(g, 8, p, e=e, max_seconds=30)
        assert r.moves == want, (e, r.moves, want, r.status)


def test_cpsat_matches_landauer_bfs_grid_with_erasure() -> None:
    g = grid_dag(3, 3)
    t = grid_target(3, 3)
    p = pmin(g, t)
    for e in (0, 1, 2, 4):
        want = landauer_bfs(g, t, p, e)
        r = solve_intervals_auto(g, t, p, e=e, max_seconds=30)
        assert r.moves == want, (e, r.moves, want, r.status)


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"ok   {name}")
            except AssertionError as exc:
                failures += 1
                print(f"FAIL {name}: {exc}")
    sys.exit(1 if failures else 0)
