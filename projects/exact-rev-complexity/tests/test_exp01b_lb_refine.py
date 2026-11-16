r"""駒数の結合制約で締めた下界 `scripts/exp01b_lb_refine.py` の回帰テスト。

**下界の検定は 2 つを対で測る。片方だけでは意味がない。**

1. **健全性**: 既知の $M^*$ を**超えない**。超えたら論法が誤りで、
   台帳に嘘の下界が載る（`solver-abort-is-not-unsat` と同じ害）
2. **単調性**: 従来（駒数を無視した版）を**下回らない**。下回ったら実装が誤り

安い $T_4$・$T_5$ だけを固定する（$T_6$ 以上は分単位なので夜の仕事）。

実行: python3 tests/test_exp01b_lb_refine.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from exp01b_lb_refine import (  # noqa: E402
    KNOWN_MSTAR,
    g_by_count,
    old_bound,
    refined_bound,
)
from treedp import QuotientTree  # noqa: E402

CHEAP = [(4, 6), (5, 7)]


def test_sound_never_exceeds_known_mstar():
    """⚠ 下界が既知の厳密値を超えたら論法が誤り。"""
    for h, P in CHEAP:
        new, _ = refined_bound(h, P)
        assert new is not None, (h, P)
        assert new <= KNOWN_MSTAR[(h, P)], (h, P, new, KNOWN_MSTAR[(h, P)])


def test_never_weaker_than_previous():
    """⚠ 従来の下界を下回ったら実装が誤り（min の取り方を間違えている）。"""
    for h, P in CHEAP:
        new, _ = refined_bound(h, P)
        old = old_bound(h, P)
        assert old is not None and new is not None
        assert new >= old, (h, P, new, old)


def test_actually_improves():
    """**改善していることも測る。** 等号のままなら結合制約が効いていない。"""
    gains = []
    for h, P in CHEAP:
        new, _ = refined_bound(h, P)
        gains.append(new - old_bound(h, P))
    assert all(g > 0 for g in gains), gains


def test_joint_constraint_is_respected():
    """最小を与える (x, y) が $x+y\\le P-1$ を満たす（制約を書き忘れていない）。"""
    for h, P in CHEAP:
        _, info = refined_bound(h, P)
        x, y = info["arg"]
        assert x >= 1 and y >= 1 and x + y <= P - 1, (h, P, x, y)


def test_g_by_count_matches_first_root_pebbled_depth():
    """⚠ **添字の流儀の校正。** `QuotientTree(m)` は $T_{m+1}$ を指す。

    駒数を無視した最小値は `first_root_pebbled_depth(m, p)` に一致するはず。
    ここがずれていたら、見ている木が 1 段違う。
    """
    from treedp import first_root_pebbled_depth
    for m, p in ((2, 5), (2, 6), (3, 5), (3, 6)):
        got = g_by_count(QuotientTree(m), p)
        assert got, (m, p)
        assert min(got.values()) == first_root_pebbled_depth(m, p), (m, p, got)


def test_g_by_count_is_monotone_in_peak():
    """ピークを緩めれば手数は増えない（単調性。BFS が壊れていれば破れる）。"""
    for m in (2, 3):
        lo = g_by_count(QuotientTree(m), 5)
        hi = g_by_count(QuotientTree(m), 6)
        for x in set(lo) & set(hi):
            assert hi[x] <= lo[x], (m, x, lo[x], hi[x])


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
