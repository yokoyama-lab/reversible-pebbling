"""ブロック標準形（put 添字ステージ）定式化の検証: BFS の厳密値と一致するか。

**この一致確認が通らない限り外挿値は使わない**（`docs/30_cross_field.md` §1.6）。
検証対象は `scripts/mip_stage.py`（Gurobi / SCIP）と `scripts/cpsat_stage.py`
（同一定式化の CP-SAT 版。ソルバ比較の統制用）。

既知真値（指揮者提供・`data/mip_findings.md` §2 と同一）:
    chain(4)  p=3: e=0 → 9,  e=1 → 7
    chain(6)  p=4: e=0 → 15, e=1 → 11
    chain(8)  p=4: e=0 → 25, e=1 → 17
    chain(12) p=5: e=0 → 39, e=1 → 29
$M^*$ は必ず奇数（$2A-1$）。値を合わせるために期待値をいじってはいけない。

    .venv/bin/python -m pytest tests/test_mip_stage.py -q
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import pytest  # noqa: E402

from landauer import landauer_bfs  # noqa: E402
from revpebble import bfs, chain, complete_binary_tree, pmin, pyramid  # noqa: E402

SECONDS = 90.0


def _pmin_chain(n: int) -> int:
    return 1 + (n - 1).bit_length()


def _solvers():
    """利用可能なソルバ関数を (名前, callable) で列挙する。"""
    out = []
    try:
        from mip_stage import solve_stage_auto as mip_solve

        def gurobi(dag, target, p, e=0, **kw):
            return mip_solve(dag, target, p, e, backend="gurobi", **kw)

        def scip(dag, target, p, e=0, **kw):
            return mip_solve(dag, target, p, e, backend="scip", **kw)

        out.append(("gurobi", gurobi))
        out.append(("scip", scip))
    except ImportError:
        pass
    try:
        from cpsat_stage import solve_stage_auto as cp_solve

        out.append(("cpsat", cp_solve))
    except ImportError:
        pass
    return out


SOLVERS = _solvers()
if not SOLVERS:  # pragma: no cover
    pytest.skip("mip_stage/cpsat_stage が import できない", allow_module_level=True)

GUROBI = dict(SOLVERS).get("gurobi")
KNOWN = {
    (4, 0): 9,
    (4, 1): 7,
    (6, 0): 15,
    (6, 1): 11,
}


@pytest.mark.parametrize("name,solve", SOLVERS)
@pytest.mark.parametrize("n,e", sorted(KNOWN))
def test_known_chain_values(name, solve, n, e) -> None:
    """既知真値との一致と奇数性（全バックエンド）。"""
    r = solve(chain(n), n, _pmin_chain(n), e, max_seconds=SECONDS)
    assert r.status == "OPTIMAL", (name, n, e, r.status)
    assert r.moves == KNOWN[n, e], (name, n, e, r.moves)
    assert r.moves % 2 == 1
    assert r.intervals == (r.moves + 1) // 2


@pytest.mark.parametrize("n", [2, 3, 5])
def test_chain_e0_matches_bfs(n) -> None:
    """既知表にない鎖長でも BFS と一致（Gurobi）。"""
    assert GUROBI is not None
    p = _pmin_chain(n)
    r = GUROBI(chain(n), n, p, 0, max_seconds=SECONDS)
    assert r.status == "OPTIMAL"
    assert r.moves == bfs(chain(n), n, p)[0]


@pytest.mark.parametrize("n,e", [(4, 2), (6, 2), (6, 3)])
def test_chain_erasures_match_landauer_bfs(n, e) -> None:
    """消去予算 e >= 2 でも landauer_bfs と一致（Gurobi）。"""
    assert GUROBI is not None
    p = _pmin_chain(n)
    r = GUROBI(chain(n), n, p, e, max_seconds=SECONDS)
    assert r.status == "OPTIMAL"
    assert r.moves == landauer_bfs(chain(n), n, p, e)


def test_p_larger_than_pmin_matches_bfs() -> None:
    """p を pmin より増やすと手数が減る側も BFS と一致（Gurobi）。"""
    assert GUROBI is not None
    n = 6
    for p in (_pmin_chain(n), _pmin_chain(n) + 1):
        r = GUROBI(chain(n), n, p, 0, max_seconds=SECONDS)
        assert r.status == "OPTIMAL"
        assert r.moves == bfs(chain(n), n, p)[0], p


def test_tree_and_pyramid_match_bfs() -> None:
    """非鎖 DAG（K_max 自動昇格の経路を含む）でも BFS と一致（Gurobi）。

    cbt(2) は非 free 頂点 3 個に対し A=9 なので、初期 K_max=2n では
    INFEASIBLE になり昇格ループが必ず動く。
    """
    assert GUROBI is not None
    g = complete_binary_tree(2)
    root = g.n - 1
    p = pmin(g, root)
    r = GUROBI(g, root, p, 0, max_seconds=SECONDS)
    assert r.status == "OPTIMAL"
    assert r.moves == bfs(g, root, p)[0]

    g = pyramid(2)
    top = g.n - 1
    p = pmin(g, top)
    r = GUROBI(g, top, p, 0, max_seconds=SECONDS)
    assert r.status == "OPTIMAL"
    assert r.moves == bfs(g, top, p)[0]


def test_unreachable_is_reported() -> None:
    """reach(2)=2 なので chain(3) は p=2 で到達不能。誤って値を返さないこと。"""
    assert GUROBI is not None
    r = GUROBI(chain(3), 3, 2, 0, max_seconds=SECONDS, k_limit=24)
    assert r.moves is None
    assert r.status.startswith("INFEASIBLE")


def test_free_target_is_zero_moves() -> None:
    assert GUROBI is not None
    r = GUROBI(chain(4), 0, 3, 0, max_seconds=SECONDS)
    assert r.moves == 0


def test_hint_does_not_change_value() -> None:
    """primal hint は値を変えない（上界の注入であって答えの固定ではない）。"""
    assert GUROBI is not None
    for hint in (False, True):
        r = GUROBI(chain(6), 6, 4, 1, max_seconds=SECONDS, hint=hint)
        assert r.status == "OPTIMAL"
        assert r.moves == 11, hint


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
