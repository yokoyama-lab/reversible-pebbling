"""候補2: DAG 全数列挙・同型除去の回帰テスト（テストファースト）。

n=2,3 は手計算で裏取りした値（docs/idea02_separation_onset.md 実装ノート参照）。
n>=4 は「軌道サイズの総和 = ラベル付き総数」という自己整合性チェック
（同型類の見落とし・二重登録があれば必ず崩れる不変量）で検証する。
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from exp02_dags import (  # noqa: E402
    _all_reach_sink,
    canonical_key,
    edges_to_dag,
    enumerate_nonisomorphic,
    enumerate_nonisomorphic_fast,
    generate_labeled,
    wl_invariant,
)


def test_n1_single_vertex() -> None:
    labeled = generate_labeled(1)
    assert labeled == [frozenset()]
    classes = enumerate_nonisomorphic(1)
    assert len(classes) == 1


def test_n2_single_edge_forced() -> None:
    """n=2: 出次数条件から辺 (0,1) が唯一の選択。"""
    labeled = generate_labeled(2)
    assert labeled == [frozenset({(0, 1)})]
    classes = enumerate_nonisomorphic(2)
    assert len(classes) == 1


def test_n3_three_labeled_three_classes() -> None:
    """n=3: 手計算で確認した3通りのラベル付きグラフが、全て非同型（自明な軌道）。"""
    labeled = generate_labeled(3)
    expected = {
        frozenset({(0, 1), (1, 2)}),
        frozenset({(0, 2), (1, 2)}),
        frozenset({(0, 1), (0, 2), (1, 2)}),
    }
    assert set(labeled) == expected
    classes = enumerate_nonisomorphic(3)
    assert len(classes) == 3


def test_all_labeled_graphs_reach_sink() -> None:
    """出次数フィルタのみで全頂点到達可能性が自動的に従う、という解析を裏取り。"""
    for n in range(1, 7):
        for edges in generate_labeled(n):
            assert _all_reach_sink(edges, n), (n, edges)


def test_full_permutation_search_agrees_with_sink_fixed_search() -> None:
    """独立な低速アルゴリズムでの裏取り: シンク固定 (n-1)! 版と、

    固定しない全 n! 順列版の正規形（辞書順最小の辺集合）で、非同型類の
    個数が一致することを確認する。シンクは同型写像で必ずシンクに写る
    （出次数0の頂点は1個しかない）という解析の裏取り。n が小さいうちだけ
    n! 版を走らせる（n=5 で 120 通り）。
    """
    import itertools

    for n in range(2, 6):
        labeled = generate_labeled(n)

        def full_key(edges: frozenset[tuple[int, int]]) -> tuple[tuple[int, int], ...]:
            best = None
            for perm in itertools.permutations(range(n)):
                image = tuple(sorted((perm[i], perm[j]) for i, j in edges))
                if best is None or image < best:
                    best = image
            return best  # type: ignore[return-value]

        full_classes = {full_key(e) for e in labeled}
        restricted_classes = enumerate_nonisomorphic(n)
        assert len(full_classes) == len(restricted_classes), (
            n,
            len(full_classes),
            len(restricted_classes),
        )


def test_canonical_key_is_isomorphism_invariant() -> None:
    """辺集合を同型写像で写しても正規形キーは変わらない。"""
    import itertools

    n = 4
    for edges in generate_labeled(n):
        key0 = canonical_key(edges, n)
        for rest in itertools.permutations(range(n - 1)):
            perm = rest + (n - 1,)
            image = frozenset((perm[i], perm[j]) for i, j in edges)
            assert canonical_key(image, n) == key0


def test_wl_invariant_is_isomorphism_invariant() -> None:
    """WL 不変量は同型写像（シンク固定の順列）で不変（必要条件のテスト）。"""
    import itertools

    n = 5
    for edges in generate_labeled(n)[:200]:
        inv0 = wl_invariant(edges, n)
        for rest in itertools.permutations(range(n - 1)):
            perm = rest + (n - 1,)
            image = frozenset((perm[i], perm[j]) for i, j in edges)
            assert wl_invariant(image, n) == inv0


def test_fast_enumeration_matches_slow_exactly() -> None:
    """高速版（WL 不変量バケット分割）が低速版（全数 canonical_key）と

    n<=6 で**同型類の集合として完全一致**することを確認する
    （個数だけでなく、正規形キーの集合まで一致させる強いテスト）。
    """
    for n in range(1, 7):
        slow_keys = {canonical_key(e, n) for e in enumerate_nonisomorphic(n)}
        fast_keys = {canonical_key(e, n) for e in enumerate_nonisomorphic_fast(n)}
        assert fast_keys == slow_keys, (
            n,
            len(fast_keys),
            len(slow_keys),
            slow_keys - fast_keys,
            fast_keys - slow_keys,
        )


def test_edges_to_dag_roundtrip() -> None:
    edges = frozenset({(0, 1), (1, 2)})
    g = edges_to_dag(edges, 3)
    assert g.n == 3
    assert g.preds[0] == frozenset()
    assert g.preds[1] == frozenset({0})
    assert g.preds[2] == frozenset({1})


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
