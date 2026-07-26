"""回帰テスト: 2026_exact_reversible_pebbling で確定した厳密値をエンジンが再現するか。

これらの数値は先行プロジェクト（overleaf/2026_exact_reversible_pebbling）で
独立に BFS 実装され、Knill 1995 の数表・Královič 2001 の特徴付けと整合が取れている。
エンジンを改造したら必ずここが通ることを確認する（実装はテストファースト）。

実行: python3 -m pytest tests/ -q   （pytest 不在なら python3 tests/test_revpebble.py）
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from revpebble import (  # noqa: E402
    bfs,
    chain,
    complete_binary_tree,
    mstar_chain,
    pmin,
    pyramid,
    reach,
    schedule,
)

# 先行プロジェクトで確定した鎖の最小手数（p = p_min で評価）。n = 1..14。
MSTAR_CHAIN = [1, 3, 5, 9, 11, 15, 19, 25, 25, 29, 33, 39, 45, 53]


def test_reach_is_two_to_the_p_minus_one() -> None:
    """reach(p) = 2^{p-1}（Královič Thm 3.1 の系）。"""
    for p in range(1, 6):
        assert reach(p) == 2 ** (p - 1), f"p={p}"


def test_mstar_chain_table() -> None:
    """鎖の M* 表の再現。"""
    got = [mstar_chain(n) for n in range(1, len(MSTAR_CHAIN) + 1)]
    assert got == MSTAR_CHAIN, got


def test_pmin_chain_matches_reach() -> None:
    """p_min(chain n) = ceil(log2 n) + 1。"""
    for n in range(1, 17):
        p = pmin(chain(n), n)
        expected = 1 + (n - 1).bit_length()
        assert p == expected, (n, p, expected)


def test_bennett_family_is_not_optimal() -> None:
    """Pesu-Phillips 2015 の Bennett 族 B(2,3)=27 は n=8 の厳密最適 25 に劣る。"""
    assert mstar_chain(8) == 25 < 27


def test_extra_pebble_reduces_moves() -> None:
    """トレードオフ: ペブルを 1 本足すと手数は真に減る（n=16）。"""
    g = chain(16)
    p0 = pmin(g, 16)
    m0, _ = bfs(g, 16, p0)
    m1, _ = bfs(g, 16, p0 + 1)
    assert m0 == 71
    assert m1 is not None and m1 < m0


def test_schedule_is_valid_and_optimal_length() -> None:
    """抽出したスケジュールが規則を守り、長さが M* に一致する。"""
    n = 6
    g = chain(n)
    p = pmin(g, n)
    seq = schedule(g, n, p)
    assert seq is not None
    state: set[int] = set()
    for kind, v in seq:
        assert all((u in g.free) or (u in state) for u in g.preds[v]), (kind, v)
        if kind == "put":
            assert v not in state
            state.add(v)
        else:
            assert v in state
            state.discard(v)
        assert len(state) <= p
    assert state == {n}
    assert len(seq) == mstar_chain(n)


def test_complete_binary_tree_small() -> None:
    """完全二分木の小さい厳密値（本プロジェクトの新規測定・回帰用に固定）。"""
    expected = {2: (3, 5), 3: (5, 17)}
    for h, (want_p, want_m) in expected.items():
        g = complete_binary_tree(h)
        root = g.n - 1
        p = pmin(g, root)
        assert p == want_p, (h, p)
        assert bfs(g, root, p)[0] == want_m, (h, bfs(g, root, p)[0])


def test_pyramid_small() -> None:
    """ピラミッド DAG が構成でき、clean 到達できる。"""
    g = pyramid(3)
    apex = g.n - 1
    p = pmin(g, apex)
    assert p is not None and p >= 1
    assert bfs(g, apex, p)[0] is not None


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
