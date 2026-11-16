"""JSSST レターの図 1・図 2 の系列の回帰テスト（テストファースト）。

図そのもの（見た目）は検査しない。**描く前の系列**が findings と一致することを固定する。
描画は `scripts/gen_atlas_figures.py` の render 側にあり、ここでは呼ばない。

    python3 tests/test_gen_atlas_figures.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from gen_atlas_figures import ratio_series, scatter_points  # noqa: E402


# --- 図 1: steps × stack_peak の散布 ------------------------------------------


def test_scatter_covers_all_111_programs() -> None:
    assert len(scatter_points()) == 111


def test_scatter_stack_users_are_36() -> None:
    """findings_phase1 §3: スタックを使うのは 36 本。"""
    assert sum(1 for p in scatter_points() if p.stack > 0) == 36


def test_scatter_extremes_match_findings() -> None:
    pts = {p.name: p for p in scatter_points()}
    assert pts["topDownCutRod"].stack == 310
    assert pts["avl_delete"].stack == 79
    assert max(p.steps for p in scatter_points()) == 27_157


def test_scatter_categories_are_the_five_known_ones() -> None:
    cats = {p.category for p in scatter_points()}
    assert cats == {"algorithm", "memoization", "injective", "structs", "jana"}


# --- 図 2: 隣接比の推移 -------------------------------------------------------


def test_ratio_series_has_nine_families_of_five_ratios() -> None:
    s = ratio_series()
    assert len(s) == 9
    for family, ratios in s.items():
        assert len(ratios) == 5, (family, ratios)  # 6 点なら比は 5 つ


def test_ratio_series_endpoints_match_findings() -> None:
    """findings_phase2 §1 の「隣接比（初 $\\to$ 末）」と一致する。"""
    s = ratio_series()
    def ends(f: str) -> tuple[float, float]:
        return round(s[f][0], 2), round(s[f][-1], 2)
    assert ends("fib_iter") == (1.80, 1.19)
    assert ends("factorial") == (4.48, 4.00)
    assert ends("bubble_sort") == (2.18, 1.36)
    assert ends("cutrod_linear") == (2.71, 2.27)


def test_growth_groups_are_separable_by_final_ratio() -> None:
    """図 2 の主張（3 群が視覚的に分かれる）が数として成り立つか。

    末端の比が 1.2 未満なら線形群、2 以上なら急成長群、その間は多項式群。
    群の境界に落ちる族が無いことを確かめる（境界に乗るなら図の主張は弱い）。
    """
    last = {f: r[-1] for f, r in ratio_series().items()}
    linear = {f for f, v in last.items() if v < 1.2}
    fast = {f for f, v in last.items() if v >= 2.0}
    poly = set(last) - linear - fast
    assert linear == {"fib_iter", "gcd_fib", "fib_pairs_2017"}, linear
    assert fast == {"factorial", "cutrod_linear"}, fast
    assert poly == {"bubble_sort", "edit_distance", "lcs", "knapsack"}, poly


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
