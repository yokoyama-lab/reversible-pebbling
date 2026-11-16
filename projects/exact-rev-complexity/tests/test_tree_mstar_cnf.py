"""tree_mstar_cnf.py の校正テスト（2026-08-10 初夜作成、翌夜に初実行のこと）。

jq 実装（autoresearch/tools/pebble.jq）と同じ検査:
  1. BFS 校正: h=1..4 で p_min=1,3,5,6 / M*=1,5,17,53
  2. K=M* の CNF は実スケジュール由来の割当で全節充足（過剰制約なし）
  3. 変異スケジュールは検出される（検査の検出力）
  4. symbreak 付き CNF も、正規化（noop 末尾・最初の手が最左最下段）を満たす
     スケジュールでは充足可能なまま
  5. cadical があれば K=M*−1 が UNSAT（h≤3）
"""

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
from tree_mstar_cnf import Enc, bfs, pminm, schedule  # noqa: E402

EXPECT = {1: (1, 1), 2: (3, 5), 3: (5, 17), 4: (6, 53)}


@pytest.mark.parametrize("h", [1, 2, 3, 4])
def test_calibration(h):
    assert pminm(h) == EXPECT[h]


@pytest.mark.parametrize("h", [1, 2, 3, 4])
def test_schedule_replays(h):
    p, m = EXPECT[h]
    mv = schedule(h, p)
    assert len(mv) == m
    n = (1 << h) - 1
    mask, peak = 0, 0
    for v in mv:
        assert 1 <= v <= n
        for c in (2 * v, 2 * v + 1):
            assert c > n or (mask >> (c - 1)) & 1, "子が未ペブル"
        mask ^= 1 << (v - 1)
        peak = max(peak, mask.bit_count())
    assert mask == 1 and peak <= p


@pytest.mark.parametrize("h", [1, 2, 3, 4])
def test_satcheck_at_mstar(h):
    p, m = EXPECT[h]
    assert Enc(h, p, m).satcheck(schedule(h, p)) == []


@pytest.mark.parametrize("h", [2, 3])
def test_mutation_detected(h):
    p, m = EXPECT[h]
    mv = schedule(h, p)
    mv2 = mv[:-1] + [2 if mv[-1] == 1 else 1]
    assert Enc(h, p, m).satcheck(mv2) != []


def test_bfs_reach_h3():
    d, _ = bfs(3, 5)
    assert len(d) == 120 and d[1] == 17


@pytest.mark.skipif(shutil.which("cadical") is None, reason="cadical なし")
@pytest.mark.parametrize("h", [1, 2, 3])
def test_lower_bound_unsat(h, tmp_path):
    p, m = EXPECT[h]
    cnf = tmp_path / f"t{h}.cnf"
    cnf.write_text(Enc(h, p, m - 1).dimacs())
    r = subprocess.run(["cadical", str(cnf)], capture_output=True, text=True, timeout=600)
    assert "s UNSATISFIABLE" in r.stdout


@pytest.mark.skipif(shutil.which("cadical") is None, reason="cadical なし")
def test_symbreak_still_sat(tmp_path):
    h, (p, m) = 3, EXPECT[3]
    cnf = tmp_path / "t3_sb.cnf"
    cnf.write_text(Enc(h, p, m).dimacs(symbreak=True))
    r = subprocess.run(["cadical", str(cnf)], capture_output=True, text=True, timeout=600)
    assert "s SATISFIABLE" in r.stdout
