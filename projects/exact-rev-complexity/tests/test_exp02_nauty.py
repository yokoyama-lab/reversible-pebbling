"""候補2: nauty 経路の DAG 列挙が自作の全数探索と完全一致することの回帰テスト。

team-lead 指示: 「nauty で数えた類数が n<=6 の既知値と完全一致すること」を
まず確認してから n>=7 の値を採用する。ここでは類数だけでなく、
`canonical_key` による同型類の**集合としての一致**まで検証する（より強いテスト）。

nauty (`geng`, `directg`) が PATH に無い環境ではスキップする。
"""

from __future__ import annotations

import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from exp02_dags import canonical_key, enumerate_nonisomorphic  # noqa: E402

NAUTY_AVAILABLE = shutil.which("geng") is not None and shutil.which("directg") is not None

if NAUTY_AVAILABLE:
    from exp02_nauty import enumerate_nonisomorphic_nauty  # noqa: E402


def _skip_if_no_nauty() -> bool:
    if not NAUTY_AVAILABLE:
        print("SKIP (nauty not on PATH)")
        return True
    return False


def test_nauty_matches_slow_enumeration_n1_to_6() -> None:
    if _skip_if_no_nauty():
        return
    for n in range(1, 7):
        slow_keys = {canonical_key(e, n) for e in enumerate_nonisomorphic(n)}
        nauty_keys = {canonical_key(e, n) for e in enumerate_nonisomorphic_nauty(n)}
        assert nauty_keys == slow_keys, (
            n,
            len(nauty_keys),
            len(slow_keys),
            slow_keys - nauty_keys,
            nauty_keys - slow_keys,
        )


def test_nauty_output_is_valid_dag_each_case() -> None:
    """各グラフが `edges_to_dag` に通せる（トポロジカル順で再ラベル済み）ことを確認。"""
    if _skip_if_no_nauty():
        return
    from exp02_dags import edges_to_dag

    for n in range(1, 6):
        for edges in enumerate_nonisomorphic_nauty(n):
            g = edges_to_dag(edges, n)
            assert g.n == n
            # シンクは n-1、出次数0であること。
            outdeg = [0] * n
            for i, _ in edges:
                outdeg[i] += 1
            assert outdeg[n - 1] == 0
            assert all(outdeg[v] >= 1 for v in range(n - 1))


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
