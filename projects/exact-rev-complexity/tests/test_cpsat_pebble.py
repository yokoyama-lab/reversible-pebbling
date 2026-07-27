"""CP-SAT 定式化の検証: BFS の厳密値と全点一致するか。

**この一致確認が通らない限り、CP-SAT の外挿値は使ってはいけない**
（`docs/30_cross_field.md` §1.6、`scripts/cpsat_pebble.py` の docstring）。

`.venv` が必要（ortools）:
    .venv/bin/python -m pytest tests/test_cpsat_pebble.py -q
    .venv/bin/python tests/test_cpsat_pebble.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import pytest  # noqa: E402

cp = pytest.importorskip(
    "ortools.sat.python.cp_model",
    reason="ortools が無い環境ではスキップ（.venv を使うこと）",
)

from cpsat_pebble import solve_auto  # noqa: E402
from landauer import landauer_bfs  # noqa: E402
from revpebble import (  # noqa: E402
    bfs,
    chain,
    complete_binary_tree,
    pmin,
    pyramid,
)

SECONDS = 60.0


def _pmin_chain(n: int) -> int:
    return 1 + (n - 1).bit_length()


@pytest.mark.parametrize("n", [2, 3, 4, 5, 6, 7, 8])
def test_chain_matches_bfs_e0(n: int) -> None:
    """$e=0$ の鎖で BFS と一致（p_min とその +1）。"""
    p0 = _pmin_chain(n)
    for p in (p0, p0 + 1):
        want, _ = bfs(chain(n), n, p)
        got = solve_auto(chain(n), n, p=p, e=0, max_seconds=SECONDS)
        assert got.status == "OPTIMAL", (n, p, got.status)
        assert got.moves == want, (n, p, got.moves, want)


@pytest.mark.parametrize("n", [4, 6, 8])
@pytest.mark.parametrize("e", [0, 1, 2, 3])
def test_chain_matches_bfs_with_erasures(n: int, e: int) -> None:
    """消去予算つきで landauer_bfs と一致。"""
    p = _pmin_chain(n)
    want = landauer_bfs(chain(n), n, p, e)
    got = solve_auto(chain(n), n, p=p, e=e, max_seconds=SECONDS)
    assert got.status == "OPTIMAL", (n, e, got.status)
    assert got.moves == want, (n, e, got.moves, want)


def test_tree_matches_bfs() -> None:
    """完全二分木（free-leaves 流儀）で BFS と一致。"""
    for h in (2, 3):
        g = complete_binary_tree(h)
        root = g.n - 1
        p = pmin(g, root)
        assert p is not None
        want, _ = bfs(g, root, p)
        got = solve_auto(g, root, p=p, e=0, max_seconds=SECONDS)
        assert got.status == "OPTIMAL", (h, got.status)
        assert got.moves == want, (h, got.moves, want)


def test_pyramid_matches_bfs() -> None:
    """ピラミッドで BFS と一致。"""
    for h in (2, 3):
        g = pyramid(h)
        apex = g.n - 1
        p = pmin(g, apex)
        assert p is not None
        want, _ = bfs(g, apex, p)
        got = solve_auto(g, apex, p=p, e=0, max_seconds=SECONDS)
        assert got.status == "OPTIMAL", (h, got.status)
        assert got.moves == want, (h, got.moves, want)


def test_schedule_is_valid() -> None:
    """CP-SAT が返すスケジュールが規則を守り、長さが最適値に一致する。"""
    n = 6
    p = _pmin_chain(n)
    g = chain(n)
    r = solve_auto(g, n, p=p, e=0, max_seconds=SECONDS, want_schedule=True)
    assert r.schedule is not None and r.moves is not None
    state: set[int] = set()
    for kind, v in r.schedule:
        assert all((u in g.free) or (u in state) for u in g.preds[v]), (kind, v)
        if kind == "put":
            assert v not in state
            state.add(v)
        else:
            state.discard(v)
        assert len(state) <= p
    assert state == {n}
    assert len(r.schedule) == r.moves


def test_unreachable_is_reported() -> None:
    """到達不能（$p$ 不足）を INFEASIBLE として報告する（地平線不足と区別できる）。

    $\\mathrm{reach}(p)=2^{p-1}$ なので $p=2$ では $n=3$ に到達できない。
    """
    r = solve_auto(chain(3), 3, p=2, e=0, max_seconds=SECONDS, max_doublings=2)
    assert r.moves is None
    assert r.status == "INFEASIBLE"


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
