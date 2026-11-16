"""候補2: 標準ペブリング BFS の回帰テスト（テストファースト）。

期待値の根拠:
  - 鎖の標準ペブル数 P=2（n>=2）: 取る操作が自由なので、隣接2頂点だけを
    順に置き換えていけば任意長の鎖を渡れる（可逆版は p_min=ceil(log2 n)+1 で
    無限に分離する — docs/20_prior_art.md §2）。n=1 は直接置くだけなので P=1。
  - 完全二分木の標準ペブル空間は h+1（docs/20_prior_art.md §3, Královič の言明。
    可逆は h+Theta(lg* h) で真に大きい）。
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from revpebble import chain, complete_binary_tree, pmin, pyramid  # noqa: E402
from stdpebble import bfs_std, mstar_std_chain, pmin_std  # noqa: E402


def test_pmin_std_chain_is_constant_two() -> None:
    """鎖の標準ペブル数は n に依らず 2（n=1 のみ 1）。"""
    assert pmin_std(chain(1), 1) == 1
    for n in range(2, 20):
        assert pmin_std(chain(n), n) == 2, n


def test_pmin_std_chain_strictly_less_than_reversible() -> None:
    """鎖は標準 P=2 に対し可逆 R=ceil(log2 n)+1 なので、n>=3 で真に分離する。"""
    for n in [3, 4, 5, 8, 16]:
        p_std = pmin_std(chain(n), n)
        p_rev = pmin(chain(n), n)
        assert p_std == 2
        assert p_rev > p_std, (n, p_std, p_rev)


def test_pmin_std_complete_binary_tree_is_h_plus_1() -> None:
    """完全二分木の標準ペブル空間は h+1（Královič, docs/20_prior_art.md §3）。

    ただし `complete_binary_tree()` は葉を free（常時可用な入力、コスト無し）と
    定義しているため（revpebble.py の設計。読むだけ・編集禁止）、h=0,1 は
    葉のみで根を直接置けてしまい退化する（P=1）。h>=2 で古典的な h+1 が
    ちょうど現れる（実測: h=2..5 で P=3,4,5,6）。
    """
    assert pmin_std(complete_binary_tree(0), 0) == 1
    assert pmin_std(complete_binary_tree(1), complete_binary_tree(1).n - 1) == 1
    for h in range(2, 6):
        g = complete_binary_tree(h)
        root = g.n - 1
        assert pmin_std(g, root) == h + 1, h


def test_pmin_std_le_pmin_reversible_general() -> None:
    """標準ペブル数は可逆ペブル数を超えない（取る操作の制約が緩いので探索が広い）。

    完全二分木・ピラミッドの両方で確認する。
    """
    for h in range(0, 4):
        g = complete_binary_tree(h)
        root = g.n - 1
        assert pmin_std(g, root) <= pmin(g, root)
    for h in range(0, 4):
        g = pyramid(h)
        root = g.n - 1
        assert pmin_std(g, root) <= pmin(g, root)


def test_mstar_std_chain_helper_matches_bfs_std() -> None:
    """mstar_std_chain がヘルパー無しの直接呼び出しと一致する。"""
    for n in [2, 3, 5, 8]:
        p = pmin_std(chain(n), n)
        moves, _ = bfs_std(chain(n), n, p)
        assert moves == mstar_std_chain(n)


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
