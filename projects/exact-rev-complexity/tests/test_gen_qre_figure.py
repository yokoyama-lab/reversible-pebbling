"""QRE 向けの図（時間最適 vs 空間最適）の系列の回帰テスト（テストファースト）。

図そのもの（見た目）は検査しない。**描く前の系列**が
`data/q2_parallel_findings.md` と `registry/results.tsv` R-Q2-08 に一致することを固定する。

    python3 tests/test_gen_qre_figure.py

⚠ この図は科研費調書と arXiv の両方で使うので、**数値の取り違えが最も高くつく場所**。
特に高さ h と深さ D = h-1 の混同を検査する。
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from gen_qre_figure import (  # noqa: E402
    QUBIT_MINIMAL_MEASURED,
    depth_optimal_peak,
    qubit_minimal_trend,
    series,
)


# --- 時間最適側（定理。R-Q2-08 / tree_pmin_exact） ----------------------------


def test_theorem_matches_findings_table() -> None:
    """findings の表: h=3,4,5,9 で 7, 13, 25, 385。"""
    assert [depth_optimal_peak(h) for h in (3, 4, 5, 9)] == [7, 13, 25, 385]


def test_theorem_is_stated_in_depth_not_height() -> None:
    """p_min = 3*2^(D-1)+1 で D = h-1。高さと深さの取り違えを固定する。"""
    for h in range(3, 14):
        D = h - 1
        assert depth_optimal_peak(h) == 3 * 2 ** (D - 1) + 1


def test_theorem_excludes_h2() -> None:
    """D>=2 (h>=3) がちょうど境界。変異注入が hD: 3<=D を 2<=D へ改良し、
    1<=D では落ちることを確かめている。h=2 の実測は 3 で式の 4 と合わない。"""
    try:
        depth_optimal_peak(2)
    except ValueError:
        pass
    else:
        raise AssertionError("h=2 は定理の範囲外なので拒否しなければならない")


def test_h4_h5_are_the_two_sided_lean_theorems() -> None:
    """tree4_pmin_eq_13 / tree5_pmin_eq_25（両側とも層1）。"""
    assert depth_optimal_peak(4) == 13
    assert depth_optimal_peak(5) == 25


# --- 空間最適側（実測。素の CNF で T を伸ばして最小ピークを探したもの） --------


def test_measured_exact_points_match_findings() -> None:
    """findings の表: h=2..5 で 3, 5, 6, 7（並列モデルで自前に測定）。"""
    exact = {h: v for h, (v, is_exact) in QUBIT_MINIMAL_MEASURED.items() if is_exact}
    assert exact == {2: 3, 3: 5, 4: 6, 5: 7}


def test_h9_is_marked_approximate() -> None:
    """findings は h=9 を「約 12」と書いている。厳密値として扱わない。"""
    value, is_exact = QUBIT_MINIMAL_MEASURED[9]
    assert value == 12
    assert is_exact is False


def test_trend_is_h_plus_2_on_the_measured_range() -> None:
    """Královič の h + Θ(lg* h) の形と整合（h=3,4,5 で h+2）。傾向線であって定理ではない。"""
    assert [qubit_minimal_trend(h) for h in (3, 4, 5)] == [5, 6, 7]


# --- 対比そのもの（この図の主張） --------------------------------------------


def test_ratio_at_h9_is_about_32() -> None:
    """findings の表の最終行: 385 / 12 ≈ 32。"""
    ratio = depth_optimal_peak(9) / QUBIT_MINIMAL_MEASURED[9][0]
    assert 31.0 < ratio < 33.0


def test_series_is_monotone_and_separates() -> None:
    """図に描く範囲で、時間最適が空間最適の傾向線を常に上回る（h>=3）。"""
    s = series()
    assert s.heights[0] == 3
    assert all(a > b for a, b in zip(s.depth_optimal, s.trend))
    assert s.depth_optimal == sorted(s.depth_optimal)


def test_series_reaches_h12() -> None:
    """調書の図は h=12（|V|=4095）まで描く。3*2^10+1 = 3073。"""
    s = series()
    assert s.heights[-1] == 12
    assert s.depth_optimal[-1] == 3073


if __name__ == "__main__":
    import traceback

    failed = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"ok   {name}")
            except Exception:
                failed += 1
                print(f"FAIL {name}")
                traceback.print_exc()
    print(f"\n{'FAILED' if failed else 'PASSED'}: {failed} failure(s)")
    sys.exit(1 if failed else 0)
