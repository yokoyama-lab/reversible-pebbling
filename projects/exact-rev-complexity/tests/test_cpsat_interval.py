"""retention interval 型定式化の検証: BFS の厳密値と一致するか。

**この一致確認が通らない限り外挿値は使わない**（`docs/30_cross_field.md` §1.6）。
素朴な時間展開版（`cpsat_pebble`）とも突き合わせる三層照合。

    .venv/bin/python -m pytest tests/test_cpsat_interval.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import pytest  # noqa: E402

pytest.importorskip("ortools.sat.python.cp_model", reason="ortools が必要（.venv）")

from cpsat_interval import solve_intervals, solve_intervals_auto  # noqa: E402
from landauer import landauer_bfs  # noqa: E402
from revpebble import bfs, chain, complete_binary_tree, pmin, pyramid  # noqa: E402

SECONDS = 90.0


def _pmin_chain(n: int) -> int:
    return 1 + (n - 1).bit_length()


def test_moves_are_odd_by_construction() -> None:
    """$M^* = 2A-1$ なので**常に奇数**。既知の全厳密値がこれを満たす。

    これは定式化の核となる観察であり、実装の健全性チェックになる。
    """
    known = [1, 3, 5, 9, 11, 15, 19, 25, 25, 29, 33, 39, 45, 53, 61, 71]  # 鎖
    known += [1, 5, 17, 53, 155, 429]  # 完全二分木
    known += [5, 13, 27, 47, 105, 99]  # ピラミッド
    assert all(v % 2 == 1 for v in known)


@pytest.mark.parametrize("n", [2, 3, 4, 5, 6, 8])
def test_chain_e0_matches_bfs(n: int) -> None:
    p = _pmin_chain(n)
    want, _ = bfs(chain(n), n, p)
    got = solve_intervals_auto(chain(n), n, p=p, e=0, max_seconds=SECONDS)
    assert got.moves == want, (n, got.moves, want, got.status)


@pytest.mark.parametrize("n", [4, 6, 8])
@pytest.mark.parametrize("e", [0, 1, 2])
def test_chain_with_erasures_matches_bfs(n: int, e: int) -> None:
    p = _pmin_chain(n)
    want = landauer_bfs(chain(n), n, p, e)
    got = solve_intervals_auto(chain(n), n, p=p, e=e, max_seconds=SECONDS)
    assert got.moves == want, (n, e, got.moves, want, got.status)


def test_tree_and_pyramid_match_bfs() -> None:
    for gen, h in ((complete_binary_tree, 2), (complete_binary_tree, 3), (pyramid, 2)):
        g = gen(h)
        tgt = g.n - 1
        p = pmin(g, tgt)
        assert p is not None
        want, _ = bfs(g, tgt, p)
        got = solve_intervals_auto(g, tgt, p=p, e=0, max_seconds=SECONDS)
        assert got.moves == want, (gen.__name__, h, got.moves, want, got.status)


def test_linear_regime_needs_only_one_interval() -> None:
    """$e \\ge e^*$ では各頂点1回で足りる（$A=n$, $M^*=2n-1$）。

    定理 A（`data/exp03_results.md` §A）の構成側。$C=1$ で解けるので軽い。
    """
    from math import ceil

    for n, p in ((12, 5), (20, 6)):
        est = ceil((n - 1) / (p - 1)) - 1
        r = solve_intervals(chain(n), n, p=p, e=est, cap=1, max_seconds=SECONDS)
        assert r.status == "OPTIMAL", (n, r.status)
        assert r.moves == 2 * n - 1, (n, r.moves)
        assert r.intervals == n, (n, r.intervals)


def test_agrees_with_time_expanded_formulation() -> None:
    """三層照合: interval 版 ⟷ 素朴な時間展開版 ⟷ BFS。"""
    from cpsat_pebble import solve_auto

    for n, e in ((6, 0), (6, 1), (8, 1)):
        p = _pmin_chain(n)
        a = solve_intervals_auto(chain(n), n, p=p, e=e, max_seconds=SECONDS)
        b = solve_auto(chain(n), n, p=p, e=e, max_seconds=SECONDS)
        c = landauer_bfs(chain(n), n, p, e)
        assert a.moves == b.moves == c, (n, e, a.moves, b.moves, c)


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
