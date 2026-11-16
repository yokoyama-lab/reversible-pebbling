"""Phase 2（スケーリング）の回帰テスト。

生成フィクスチャが (1) 実行できること (2) 既知の点で既測値を再現することを固定する。

    python3 tests/test_atlas_scale.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from atlas_measure import measure  # noqa: E402
from atlas_scale import FAMILIES, OUTDIR  # noqa: E402


def _measure(fam: str, n: int):
    gen, _grid = FAMILIES[fam]
    _src, text = gen(n)
    OUTDIR.mkdir(parents=True, exist_ok=True)
    fx = OUTDIR / f"_test_{fam}_{n}.janus"
    fx.write_text(text)
    return measure(fx)


def test_all_families_run_at_smallest_size() -> None:
    """全 9 族が最小サイズで実行できる（Janus の fi/delocal 表明が通る＝内部整合の検査）。"""
    for fam, (gen, grid) in FAMILIES.items():
        r = _measure(fam, grid[0])
        assert r["steps"] > 0, (fam, r)


def test_fib_pairs_reproduces_exp51_at_n9() -> None:
    """fib_pairs_2017 の n=9 は exp51 の 1 回呼び実測（M: put のみ 10・ピーク 10）を再現。"""
    r = _measure("fib_pairs_2017", 9)
    m = r["arrays"]["M"]
    assert m["puts"] == 10 and m["takes"] == 0, m
    assert m["peak_nonzero"] == 10, m


def test_gcd_fib_stack_grows_with_k() -> None:
    """gcd の最悪ケースはステップ数が k とともに増える（スタック族の生成が機能している）。"""
    a = _measure("gcd_fib", 4)
    b = _measure("gcd_fib", 8)
    assert b["steps"] > a["steps"], (a["steps"], b["steps"])


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
            except Exception as exc:
                failures += 1
                print(f"ERROR {name}: {type(exc).__name__}: {exc}")
    sys.exit(1 if failures else 0)
