"""treedp_complete（Královič の complete computation 最小空間）の回帰テスト。

真値の出所（docs/25 §7）:
- Smin(1..5) = [1,3,4,5,6] は Lemma 4.3（S̄min(h+1) = Smin(h)+2）と
  実測 S̄min(2..6) = pmin_tree(1..5) = [3,5,6,7,8] から導出
- Smin(6) = 8 は 2026-08-10 の決定計算（第 3 ジャンプ i*=6 の確定。
  独立実装照合・全探索完了・runcap 上限内）

    .venv/bin/python -m pytest tests/test_treedp_complete.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from treedp_complete import smin_brute, smin_tree  # noqa: E402


def test_smin_matches_lemma43_derivation() -> None:
    """Smin(m+1) for m=0..4 が Lemma 4.3 由来の導出値と一致。"""
    assert [smin_tree(m) for m in range(5)] == [1, 3, 4, 5, 6]


def test_quotient_agrees_with_brute_force() -> None:
    """商 BFS と（商なし・被覆集合明示の）独立実装が一致（m <= 2）。"""
    for m in range(3):
        assert smin_brute(m) == smin_tree(m), m


def test_third_jump_smin6() -> None:
    """決定結果の固定: Smin(6) = 8（= S̄min(6)、ジャンプ i*=6）。

    ここが 7 に変わったら定義か実装が壊れている（docs/25 §7 が崩れる）。
    数秒で走る（2026-08-10 実測 13 秒・376MB）。
    """
    assert smin_tree(5) == 8


if __name__ == "__main__":
    import pytest

    raise SystemExit(pytest.main([__file__, "-q"]))
