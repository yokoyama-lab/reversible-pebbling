"""候補2: nauty ストリーミング集計スクリプトの回帰テスト（テストファースト）。

n=6（既に厳密確定済み: 非同型類3341、分布は `data/exp02_results.md` §②）で
ストリーミング集計版が同じ分布・同じ eq/gt 件数を再現することを確認する
（team-lead 指示の「n<=6 で完全一致を確認してから n>=7,8 を採用する」の実践）。
チェックポイントは一時ディレクトリに退避し、実データを汚さない。
nauty が PATH に無い環境ではスキップする。
"""

from __future__ import annotations

import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

NAUTY_AVAILABLE = shutil.which("geng") is not None and shutil.which("directg") is not None

if NAUTY_AVAILABLE:
    import exp02_n8_stream as stream  # noqa: E402

# n<=6 の厳密分布（data/exp02_results.md §②、自作全数探索で確定済み）。
KNOWN_DIST_N6 = {
    "2,4": 1,
    "3,4": 126,
    "3,5": 136,
    "4,4": 92,
    "4,5": 1319,
    "4,6": 102,
    "5,5": 650,
    "5,6": 613,
    "6,6": 302,
}
KNOWN_TOTAL_N6 = 3341
KNOWN_EQ_N6 = 1044
KNOWN_MAX_GAP_N6 = 2


def test_stream_matches_known_n6_distribution() -> None:
    if not NAUTY_AVAILABLE:
        print("SKIP (nauty not on PATH)")
        return
    with tempfile.TemporaryDirectory() as tmpdir:
        stream.DATA_DIR = Path(tmpdir)
        state = stream.run_chunk(6, budget_sec=120.0, quiet=True)
        assert state["done"]
        assert state["kept_processed"] == KNOWN_TOTAL_N6
        assert state["eq_count"] == KNOWN_EQ_N6
        assert state["gt_count"] == KNOWN_TOTAL_N6 - KNOWN_EQ_N6
        assert state["max_gap"] == KNOWN_MAX_GAP_N6
        assert state["dist"] == KNOWN_DIST_N6, state["dist"]


def test_stream_resume_matches_single_run() -> None:
    """小さい予算で何度も中断・再開しても、n=6 で一括処理と同じ最終集計になる。"""
    if not NAUTY_AVAILABLE:
        print("SKIP (nauty not on PATH)")
        return
    with tempfile.TemporaryDirectory() as tmpdir:
        stream.DATA_DIR = Path(tmpdir)
        state = {"done": False}
        for _ in range(200):
            state = stream.run_chunk(6, budget_sec=0.2, quiet=True)
            if state["done"]:
                break
        assert state["done"]
        assert state["kept_processed"] == KNOWN_TOTAL_N6
        assert state["dist"] == KNOWN_DIST_N6


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
