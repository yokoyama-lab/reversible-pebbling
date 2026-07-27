"""IC3 符号化の回帰テスト（既知値で符号化の妥当性を固定）。

**この検証を通さずに UNREACHABLE を信用してはいけない**
（符号化が過剰に制約されているだけの可能性がある）。

    python3 tests/test_ic3_reach.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import pytest  # noqa: E402

from ic3_reach import NUXMV, run_nuxmv, smv_model  # noqa: E402

pytestmark = pytest.mark.skipif(
    not NUXMV.exists(), reason="nuXmv が無い（docs/33_install_notes.md §1）"
)

WORK = Path("/tmp/claude-1000/-work-a-dev/ic3_test")


def _check(p: int, e: int, n: int) -> str:
    WORK.mkdir(parents=True, exist_ok=True)
    f = WORK / f"c_p{p}_e{e}_n{n}.smv"
    f.write_text(smv_model(n, p, e))
    return run_nuxmv(f, timeout=300.0)[0]


def test_model_generates() -> None:
    txt = smv_model(5, 3, 1)
    assert "INVARSPEC" in txt and "cnt : 0..1" in txt and "npeb" in txt


@pytest.mark.parametrize("p,e,reach", [(3, 0, 4), (4, 0, 8), (4, 1, 12)])
def test_boundary_matches_conjecture_b2(p: int, e: int, reach: int) -> None:
    """予想値には到達し、+1 には到達しない（両側の一致）。"""
    assert _check(p, e, reach) == "REACHABLE", (p, e, reach)
    assert _check(p, e, reach + 1) == "UNREACHABLE", (p, e, reach + 1)


def test_e_zero_matches_known_reach() -> None:
    """$e=0$ では既知の $\\mathrm{reach}(p)=2^{p-1}$（Královič Thm 3.1 の系）に一致。"""
    for p in (3, 4, 5):
        assert _check(p, 0, 2 ** (p - 1)) == "REACHABLE", p
        assert _check(p, 0, 2 ** (p - 1) + 1) == "UNREACHABLE", p


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
