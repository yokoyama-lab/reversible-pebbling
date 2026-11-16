"""treedp_erase（消去つき商木 BFS）の回帰テスト。

真値の出所:
- landauer_bfs（検証済み・商なし）との一致（m ≤ 3 の全点照合は
  scripts/treedp_erase.py --verify。ここではその抜粋を固定）
- e=0 の S̄min(2..6) = [3,5,6,7,8]（docs/25 §1・§7）

    .venv/bin/python -m pytest tests/test_treedp_erase.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from landauer import landauer_bfs  # noqa: E402
from revpebble import complete_binary_tree  # noqa: E402
from treedp_erase import QuotientTreeErase, reach_clean  # noqa: E402


def test_matches_landauer_bfs_small() -> None:
    """m <= 2 の全点で landauer_bfs の到達可能性と一致。"""
    for m in (1, 2):
        g = complete_binary_tree(m + 1)
        root = g.n - 1
        qt = QuotientTreeErase(m)
        for p in range(1, 7):
            for e in range(0, 3):
                want = landauer_bfs(g, root, p, e) is not None
                assert reach_clean(qt, p, e) == want, (m, p, e)


def test_matches_landauer_bfs_m3_boundary() -> None:
    """m=3 は境界近傍のみ固定（全点は --verify で実施済み）。"""
    g = complete_binary_tree(4)
    root = g.n - 1
    qt = QuotientTreeErase(3)
    for p, e in ((5, 0), (5, 1), (6, 0), (6, 1), (4, 2)):
        want = landauer_bfs(g, root, p, e) is not None
        assert reach_clean(qt, p, e) == want, (p, e)


def test_e0_reproduces_sbar_min() -> None:
    """e=0 は S̄min(2..6) = [3,5,6,7,8] を再現（docs/25）。"""
    for m, want in ((1, 3), (2, 5), (3, 6), (4, 7)):
        qt = QuotientTreeErase(m)
        assert not reach_clean(qt, want - 1, 0), m
        assert reach_clean(qt, want, 0), m


def test_erasure_strictly_helps_at_boundary() -> None:
    """m=2 (Bt(3)): e=0 は p=5 が必要だが e=1 なら p=4 で届く（既検証域の性質）。"""
    qt = QuotientTreeErase(2)
    assert not reach_clean(qt, 4, 0)
    assert reach_clean(qt, 4, 1)


if __name__ == "__main__":
    import pytest

    raise SystemExit(pytest.main([__file__, "-q"]))
