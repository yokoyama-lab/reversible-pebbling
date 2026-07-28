"""Phase 0（実行センサス）の回帰テスト。

センサス本体を走らせる前に、分類と単体実行の器が正しいことを固定する。

    python3 tests/test_atlas_census.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from atlas_census import CORPORA, categorize, discover, run_single  # noqa: E402


def test_categorize() -> None:
    """区分列（先生の決定 2026-07-28: injective 系は含めて区分で分ける）。"""
    assert categorize("pyjanus", "injective_gcd") == "injective"
    assert categorize("pyjanus", "structs_nested") == "structs"
    assert categorize("pyjanus", "edit_distance") == "algorithm"
    assert categorize("memoization", "fib") == "memoization"
    assert categorize("jana", "sqrt") == "jana"
    assert categorize("oracle", "feistel8") == "oracle"


def test_discover_finds_main_corpus() -> None:
    """主コーパス（PyJanus 97 本）が見えること。他は環境依存なので本数を固定しない。"""
    files = discover()
    pyjanus = [f for f in files if f[0] == "pyjanus"]
    assert len(pyjanus) == 97, len(pyjanus)
    # 総数はコーパスの増減がありうるので下限のみ
    assert len(files) >= 100, len(files)


def test_run_single_on_known_fast_program() -> None:
    """既に exp51 で実行実績のあるプログラムが run_ok になること。"""
    fib = Path.home() / "dev/overleaf/2017_rev_memoization/program/fib.janus"
    r = run_single(fib, timeout=60)
    assert r["parse_ok"] and r["run_ok"], r


def test_run_single_reports_failure_honestly() -> None:
    """存在しないファイルは例外でなく失敗として返る（センサスが途中で死なない）。"""
    r = run_single(Path("/nonexistent/x.ja"), timeout=5)
    assert not r["parse_ok"] and not r["run_ok"]
    assert r["error"], r


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
