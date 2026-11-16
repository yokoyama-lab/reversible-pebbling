"""Phase 1（全数計測）の回帰テスト。

**一般化トレーサが、既測 5 本（exp51/exp52）と同じ数値を出すことを最初に固定する。**
これが通らない限り全数計測の値は採用しない（docs/81 §4）。

    python3 tests/test_atlas_measure.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from atlas_measure import measure  # noqa: E402

MEMO2017 = Path.home() / "dev/overleaf/2017_rev_memoization/program"
MEMO2021 = Path.home() / "dev/overleaf/2021_rev_memoization2/programs"


def test_fib_matches_exp51() -> None:
    """exp51 の確定値: メモ表 M は手数 70・ピーク 10・終端 10 セル非ゼロ。"""
    r = measure(MEMO2017 / "fib.janus")
    m = r["arrays"]["M"]
    assert m["puts"] + m["takes"] == 70, m
    assert m["peak_nonzero"] == 10, m
    assert m["final_nonzero"] == 10, m


def test_fac_matches_exp51() -> None:
    """exp51 の確定値: メモ表 t は手数 8・ピーク 6・終端 6 セル非ゼロ。"""
    r = measure(MEMO2017 / "fac.janus")
    t = r["arrays"]["t"]
    assert t["puts"] + t["takes"] == 8, t
    assert t["peak_nonzero"] == 6, t
    assert t["final_nonzero"] == 6, t


def test_topdown_cutrod_matches_corrected() -> None:
    """総歩数 8497・メモ r 手数 646・ピーク 7 は exp52 と同じ。
    **stack peak は 310 が正**（exp52 の 75802 は共有スタックセルを参照フレーム数だけ
    多重計上した測定バグ。剪定方式とデデュープ方式の独立2実装が 310 で一致、2026-07-28）。"""
    r = measure(MEMO2021 / "topDownCutRod.janus")
    assert r["steps"] == 8497, r["steps"]
    assert r["stack_peak"] == 310, r["stack_peak"]
    a = r["arrays"]["r"]
    assert a["puts"] + a["takes"] == 646, a
    assert a["peak_nonzero"] == 7, a
    assert a["final_nonzero"] == 0, a


def test_symmetric_cutrod_matches_corrected() -> None:
    """総歩数 959・メモ手数 100・ピーク 10 は exp52 と同じ。stack peak は 14 が正（同上の訂正）。"""
    r = measure(MEMO2021 / "topDownCutRod_symmetric.janus")
    assert r["steps"] == 959, r["steps"]
    assert r["stack_peak"] == 14, r["stack_peak"]
    a = r["arrays"]["r"]
    assert a["puts"] + a["takes"] == 100, a
    assert a["peak_nonzero"] == 10, a


def test_no_double_count_across_frames() -> None:
    """参照渡しで複数フレームに見える配列を二重計上しない。

    fib.janus の M は再帰呼び出し中、root と呼び出し先フレームの両方に見えるが、
    ピークは 10（表のサイズ）を超えてはならない。
    """
    r = measure(MEMO2017 / "fib.janus")
    assert r["arrays"]["M"]["peak_nonzero"] <= 10


def test_steps_cross_check_with_pyjanus_profiler() -> None:
    """二重実装照合: 総歩数を PyJanus 純正 profile_space と突き合わせる。

    どちらも同じ `_exec_stmt_impl` フックで文を数えるので、一致しなければ
    こちらの配管が壊れている。
    """
    sys.path.insert(0, str(Path.home() / "dev/github.com/yokoyama-lab/PyJanus"))
    from jana_py.cli import parse_for_std
    from jana_py.pebble import profile_space

    p = MEMO2017 / "fac.janus"
    prog = parse_for_std("jana2014", str(p), p.read_text(), None)
    theirs = profile_space(prog).total_steps
    ours = measure(p)["steps"]
    assert ours == theirs, (ours, theirs)


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
