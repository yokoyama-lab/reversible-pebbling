"""`scripts/atlas_coverage.py` / `scripts/atlas_extend.py` の回帰テスト（Phase 4）。

規約（`docs/81_resource_atlas_plan.md` §4）どおり、**先に固定する数値**を置く:

- L2 の対応（reftest の登録 → `.j` ファイル）が既知の 39 ファイル・40 アルゴリズムであること。
- 既測の 1 本（`fib_c.ja`）で、自作トレーサと PyJanus 純正プロファイラが
  `steps` / `call_depth` で一致すること（＝独立 2 実装照合の最小単位）。
- 3 層の判定が既知の代表例で変わらないこと。

PyJanus / reversible-algorithms が手元に無い環境では skip する。
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))

import atlas_coverage as cov  # noqa: E402
import atlas_extend as ext  # noqa: E402

pytestmark = pytest.mark.skipif(
    not (cov.CORPUS.is_dir() and cov.PYJANUS.is_dir()),
    reason="reversible-algorithms / PyJanus が手元に無い",
)


def test_l2_map_covers_the_registered_algorithms() -> None:
    """reftest の 40 登録が 39 本の `.j` に対応する（avl_insert.j が 2 つに使われる）。"""
    m = cov.l2_map()
    assert len(m) == 39, sorted(m)
    names = {n for v in m.values() for n in v}
    assert len(names) == 40, sorted(names)
    # 代表例: パスと名前の対応が壊れていないこと
    assert m["numeric/gcd.j"] == ["gcd"]
    assert "kmp_count" in m["string_search/kmp2.j"]


def test_l1_known_verdicts() -> None:
    assert cov.check_l1(cov.CORPUS / "numeric/gcd.j")[0] == "reversible"


def test_l3_vjanus_and_codegen_agree_on_gcd() -> None:
    """処理系横断: 検証済みインタプリタと C++ 生成が、どちらも PyJanus と一致する。"""
    if not cov.DRIVERAR.exists():
        pytest.skip("driverar が未ビルド")
    assert cov.check_vjanus(cov.CORPUS / "numeric/gcd.j")[0] == "PASS"
    assert cov.check_codegen(cov.CORPUS / "numeric/gcd.j")[0] == "PASS"


def test_two_implementations_agree_on_fib() -> None:
    """独立 2 実装照合の最小単位（exp51 の既測 1 本）。"""
    fib = cov.PYJANUS / "tests/jana2014/fixtures/examples/fib_c.ja"
    if not fib.exists():
        pytest.skip("fixtures が改名されている")
    a = ext.impl_a(fib, 120.0)
    b = ext.impl_b(fib, 120.0)
    assert a["steps"] == b["b_steps"] == 60
    assert a["call_depth_peak"] == b["b_call_depth_peak"] == 6
