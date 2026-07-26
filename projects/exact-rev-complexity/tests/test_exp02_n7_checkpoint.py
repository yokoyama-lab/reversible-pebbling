"""候補2: n=7 の同型除去チェックポイント機構の回帰テスト（テストファースト）。

計算アルゴリズム自体（`canonical_key`）は既に信用済み（test_exp02_dags.py）。
ここで検証するのは**分割・再開の仕組みが結果を変えないこと**——
小さい n（テストでは n=5）で「一括処理」と「小さな予算で何度も中断→再開」が
最終的に同じ非同型類集合に収束することを確認する。
一時ディレクトリに退避してから実データ (`data/`) を汚さないようにする。
"""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import exp02_n7_checkpoint as ckpt  # noqa: E402
from exp02_dags import canonical_key, enumerate_nonisomorphic, generate_labeled  # noqa: E402


def test_single_unbounded_chunk_matches_direct_enumeration(tmp_path: Path = None) -> None:
    """予算を十分大きく取れば1回のチャンクで直接列挙と同じ結果になる。"""
    n = 4
    with tempfile.TemporaryDirectory() as tmpdir:
        ckpt.DATA_DIR = Path(tmpdir)
        state = ckpt.run_chunk(n, budget_sec=60.0, quiet=True)
        assert state["next_index"] == len(generate_labeled(n))
        got_keys = {tuple(tuple(p) for p in k) for k in state["keys"]}
        expected_keys = {canonical_key(e, n) for e in enumerate_nonisomorphic(n)}
        assert got_keys == expected_keys


def test_many_small_chunks_resume_to_same_result() -> None:
    """小さい予算(0秒=1件ずつ)で何度も中断・再開しても最終結果は一括処理と一致する。"""
    n = 5
    with tempfile.TemporaryDirectory() as tmpdir:
        ckpt.DATA_DIR = Path(tmpdir)
        labeled = generate_labeled(n)
        state = {"next_index": 0, "keys": [], "reps": []}
        # budget_sec=0 だと必ず1件処理してから予算切れになる（while ループの構造上）。
        for _ in range(len(labeled) + 5):  # 十分な回数呼べば完走する
            state = ckpt.run_chunk(n, budget_sec=0.0, quiet=True)
            if state["next_index"] >= len(labeled):
                break
        assert state["next_index"] == len(labeled)
        got_keys = {tuple(tuple(p) for p in k) for k in state["keys"]}
        expected_keys = {canonical_key(e, n) for e in enumerate_nonisomorphic(n)}
        assert got_keys == expected_keys


def test_classes_file_written_on_completion() -> None:
    n = 3
    with tempfile.TemporaryDirectory() as tmpdir:
        ckpt.DATA_DIR = Path(tmpdir)
        ckpt.run_chunk(n, budget_sec=60.0, quiet=True)
        assert ckpt.classes_path(n).exists()


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
