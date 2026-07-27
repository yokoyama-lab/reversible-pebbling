"""SAT による下界証明の回帰テスト（小さい $n$ のみ。CaDiCaL が必要）。

    python3 tests/test_sat_lower_bound.py
    python3 -m pytest tests/test_sat_lower_bound.py -q
"""

from __future__ import annotations

import shutil
import subprocess
import sys
from math import ceil
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import pytest  # noqa: E402

from revpebble import bfs, chain  # noqa: E402
from sat_lower_bound import DRAT_TRIM, encode, run  # noqa: E402

pytestmark = pytest.mark.skipif(
    shutil.which("cadical") is None, reason="cadical が無い（brew install cadical）"
)

WORK = Path("/tmp/claude-1000/-work-a-dev/sat_lb_test")


def test_cardinality_encoding_is_sound() -> None:
    """濃度制約の符号化が正しい（$\\sum \\le k$ を破る割り当てが UNSAT）。"""
    from sat_lower_bound import Cnf

    c = Cnf()
    lits = [c.var() for _ in range(5)]
    c.at_most_k(lits, 2)
    for lit in lits[:3]:  # 3 個を真に固定 → 矛盾すべき
        c.add(lit)
    r = run(c, WORK, "card_bad", timeout=60)
    assert r["verdict"] == "UNSATISFIABLE", r

    c2 = Cnf()
    lits2 = [c2.var() for _ in range(5)]
    c2.at_most_k(lits2, 2)
    for lit in lits2[:2]:  # 2 個なら充足
        c2.add(lit)
    r2 = run(c2, WORK, "card_ok", timeout=60)
    assert r2["verdict"] == "SATISFIABLE", r2


def test_encoding_agrees_with_bfs_on_feasibility() -> None:
    """「$M^*$ 手で可能」が SAT、「$M^*-2$ 手」が UNSAT（手数は奇数なので 2 刻み）。"""
    n, p = 6, 4
    want, _ = bfs(chain(n), n, p)
    assert want is not None
    ok = run(encode(chain(n), n, p, 0, want), WORK, f"feas{n}", timeout=120)
    assert ok["verdict"] == "SATISFIABLE", ok
    ng = run(encode(chain(n), n, p, 0, want - 2), WORK, f"infeas{n}", timeout=120)
    assert ng["verdict"] == "UNSATISFIABLE", ng


@pytest.mark.parametrize("n,p", [(8, 4), (12, 5)])
def test_theorem_a_lower_bound_certified(n: int, p: int) -> None:
    """定理 A の下界: $e=e^*-1$ で $2n-1$ 手は UNSAT。**DRAT を独立検証**する。"""
    estar = ceil((n - 1) / (p - 1)) - 1
    r = run(encode(chain(n), n, p, estar - 1, 2 * n - 1), WORK, f"lb{n}", timeout=240)
    assert r["verdict"] == "UNSATISFIABLE", r
    if DRAT_TRIM.exists():
        assert r["checked"] == "VERIFIED", r
    # 対照: e=e* なら充足する
    r2 = run(encode(chain(n), n, p, estar, 2 * n - 1), WORK, f"ub{n}", timeout=240)
    assert r2["verdict"] == "SATISFIABLE", r2


def test_drat_trim_is_available() -> None:
    """drat-trim が使える（無い場合は認証なしになるので警告として明示）。"""
    if not DRAT_TRIM.exists():
        pytest.skip(f"drat-trim が無い: {DRAT_TRIM}（gnu99 でビルドが必要）")
    out = subprocess.run([str(DRAT_TRIM)], capture_output=True, text=True)
    assert "usage" in out.stdout.lower()


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
