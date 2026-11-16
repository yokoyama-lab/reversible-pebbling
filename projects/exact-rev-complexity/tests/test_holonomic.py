"""holonomic guessing の回帰テスト（テストファースト）。

既知の P-recursive 数列で「正しい漸化式を、正しい必要項数で見つける」ことを固定する。
ここが通らない実装で我々の数列を判定してはいけない
（`docs/00_overview.md` §2.1 の当てはめ崩壊4件は、まさにこの検証を欠いた当てはめだった）。

実行: python3 -m pytest tests/test_holonomic.py -q
      python3 tests/test_holonomic.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from holonomic import (  # noqa: E402
    Recurrence,
    guess,
    min_terms_needed,
    verify,
)

FIB = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597]
CATALAN = [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900]
FACTORIAL = [1, 1, 2, 6, 24, 120, 720, 5040, 40320, 362880, 3628800, 39916800]
CENTRAL_BINOM = [1, 2, 6, 20, 70, 252, 924, 3432, 12870, 48620, 184756, 705432]
POWERS_OF_2 = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096]
# 多項式列 3h^2-h+3（h=1..）— ピラミッドの崩壊した当てはめ。多項式は holonomic。
POLY = [3 * h * h - h + 3 for h in range(1, 15)]


def test_fibonacci_order2_degree0() -> None:
    """Fibonacci は order 2 / degree 0 で見つかる（定数係数）。"""
    rec = guess(FIB)
    assert rec is not None
    assert rec.order == 2 and rec.degree == 0, (rec.order, rec.degree)
    assert verify(rec, FIB)


def test_catalan_order1_degree1() -> None:
    """Catalan は order 1 / degree 1: (n+2)a(n+1) - (4n+2)a(n) = 0。"""
    rec = guess(CATALAN)
    assert rec is not None
    assert rec.order == 1 and rec.degree == 1, (rec.order, rec.degree)
    assert verify(rec, CATALAN)


def test_factorial_order1_degree1() -> None:
    """階乗は a(n+1) - (n+1)a(n) = 0。"""
    rec = guess(FACTORIAL)
    assert rec is not None
    assert rec.order == 1 and rec.degree == 1
    assert verify(rec, FACTORIAL)


def test_central_binomial_order1_degree1() -> None:
    """中央二項係数 C(2n,n): (n+1)a(n+1) - (4n+2)a(n) = 0。"""
    rec = guess(CENTRAL_BINOM)
    assert rec is not None
    assert rec.order == 1 and rec.degree == 1
    assert verify(rec, CENTRAL_BINOM)


def test_geometric_order1_degree0() -> None:
    """2^n は a(n+1) - 2a(n) = 0（最小の非自明ケース）。"""
    rec = guess(POWERS_OF_2)
    assert rec is not None
    assert rec.order == 1 and rec.degree == 0
    assert verify(rec, POWERS_OF_2)


def test_polynomial_is_holonomic() -> None:
    """多項式列も holonomic（order 1 / degree = 次数）。崩壊した当てはめの対照。"""
    rec = guess(POLY)
    assert rec is not None
    assert rec.order == 1
    assert verify(rec, POLY)


def test_random_like_sequence_is_rejected() -> None:
    """holonomic でない（と期待される）列に対して、偽の漸化式を返さない。

    素数列は P-recursive でないことが知られている。探索範囲内で見つからないか、
    見つかっても held-out 検証で落ちること。
    """
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]
    rec = guess(primes, max_order=2, max_degree=2)
    assert rec is None, f"素数列に漸化式を誤検出した: {rec}"


def test_short_sequence_refuses_to_guess() -> None:
    """項数が足りないときは None を返す（当てはめて自信を持たない）。

    4 点で 2 次多項式（未知数3個）は「解ける」が、確証に必要な余剰式が無い。
    これを弾けることが本実装の存在理由（当てはめ崩壊4件の再発防止）。
    """
    assert guess(POLY[:4], min_slack=3) is None


def test_min_terms_needed_is_reported() -> None:
    """(order, degree) から必要項数を計算できる。"""
    # 未知数 = (order+1)*(degree+1)、確証には余剰式が要る
    assert min_terms_needed(2, 0, slack=3) == (2 + 1) * (0 + 1) + 3 + 2
    assert min_terms_needed(1, 1, slack=3) == (1 + 1) * (1 + 1) + 3 + 1


def test_verify_detects_wrong_recurrence() -> None:
    """明らかに誤った漸化式を verify が弾く。"""
    bad = Recurrence(order=1, degree=0, coeffs={(0, 0): 1, (1, 0): -3})  # a(n+1)=3a(n)
    assert not verify(bad, POWERS_OF_2)


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
