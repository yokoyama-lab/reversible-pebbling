"""3 相合成（autoresearch/tools/compose_upper.py）の回帰テスト。

- h=3,4,5 で合成が既知 M*=17,53,155 を厳密再現し、再生検証を通ること。
- 相2 の制限 BFS が h=3,4 の既知値（7, 21）を返すこと。
- relabel_under が heap 番号の部分木写像として正しいこと。
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "autoresearch" / "tools"))
from compose_upper import bfs_masked, compose, relabel_under, replay, subtree  # noqa: E402


def test_relabel_under():
    assert relabel_under([1, 2, 3, 4, 7], 2) == [2, 4, 5, 8, 11]
    assert relabel_under([1, 2, 3], 3) == [3, 6, 7]


def test_subtree():
    assert subtree(3, 15) == [3, 6, 7, 12, 13, 14, 15]


@pytest.mark.parametrize("h,p,mstar", [(3, 5, 17), (4, 6, 53), (5, 7, 155)])
def test_compose_reproduces_known_mstar(h, p, mstar):
    mv = compose(h, p, log=lambda *_: None)
    r = replay(h, p, mv)
    assert r["moves"] == mstar
    assert r["peak"] <= p


@pytest.mark.parametrize("h,b,expect", [(3, 4, 7), (4, 5, 21), (5, 6, 57)])
def test_phase2_restricted_bfs(h, b, expect):
    n = (1 << h) - 1
    d, mv = bfs_masked(n, [1] + subtree(3, n), {2}, b, 1)
    assert d == expect and len(mv) == expect
