"""一般の $M^*(G,p,e) <= k$ SAT 符号化と DRAT 検証の回帰テスト。"""

from __future__ import annotations

import shutil
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from landauer import landauer_bfs  # noqa: E402
from revpebble import chain, complete_binary_tree, pyramid  # noqa: E402
import sat_pebble  # noqa: E402
from sat_pebble import Cnf, encode, run, verify_schedule  # noqa: E402

WORK = Path("/tmp/sat_pebble_tests")


KNOWN = [
    (4, 3, 0, 9),
    (4, 3, 1, 7),
    (6, 4, 0, 15),
    (6, 4, 1, 11),
    (8, 4, 0, 25),
    (8, 4, 1, 17),
    (12, 5, 0, 39),
    (12, 5, 1, 29),
]


def require_tools() -> None:
    assert shutil.which("cadical") is not None, "cadical must be on PATH"
    assert shutil.which("drat-trim") is not None, "drat-trim must be on PATH"


def test_cardinality_encoding_exhaustively() -> None:
    """逐次カウンタを全 primary 割当てで SAT の真理値表と照合する。"""
    require_tools()
    for size in range(5):
        for bound in range(-1, size + 2):
            for mask in range(1 << size):
                cnf = Cnf()
                xs = [cnf.var() for _ in range(size)]
                cnf.at_most_k(xs, bound)
                for i, x in enumerate(xs):
                    cnf.add(x if mask & (1 << i) else -x)
                result = run(
                    cnf, WORK, f"card_n{size}_b{bound}_m{mask}", verify_proof=False
                )
                expected = mask.bit_count() <= bound
                assert (result.verdict == "SATISFIABLE") is expected, (
                    size,
                    bound,
                    mask,
                    result,
                )


def test_decision_is_at_most_k_not_exactly_k() -> None:
    """3 手の手順は k=4 でも SAT、k=2 では UNSAT。"""
    require_tools()
    g = chain(2)
    sat = run(encode(g, 2, p=2, e=0, k=4), WORK, "at_most_sat")
    assert sat.verdict == "SATISFIABLE", sat
    assert sat.schedule is not None and len(sat.schedule) == 3
    assert sat.schedule_valid is True

    unsat = run(encode(g, 2, p=2, e=0, k=2), WORK, "at_most_unsat")
    assert unsat.verdict == "UNSATISFIABLE", unsat
    assert unsat.proof_status == "VERIFIED", unsat


def test_small_decisions_agree_with_bfs() -> None:
    """小さい鎖について k=0..9 の決定真理値を BFS と全点照合する。"""
    require_tools()
    for n in range(1, 5):
        g = chain(n)
        for p in range(4):
            for e in range(2):
                optimum = landauer_bfs(g, n, p, e)
                for k in range(10):
                    result = run(
                        encode(g, n, p, e, k),
                        WORK,
                        f"grid_n{n}_p{p}_e{e}_k{k}",
                        verify_proof=False,
                    )
                    expected = optimum is not None and optimum <= k
                    assert (result.verdict == "SATISFIABLE") is expected, (
                        n,
                        p,
                        e,
                        k,
                        optimum,
                        result,
                    )


@pytest.mark.parametrize("dag", [complete_binary_tree(2), pyramid(2)])
def test_general_dag_with_two_predecessors_agrees_with_bfs(dag) -> None:
    """鎖以外でも availability の AND が BFS と一致する。"""
    require_tools()
    target = dag.n - 1
    p = 4
    optimum = landauer_bfs(dag, target, p, e=0)
    assert optimum is not None and optimum >= 3
    sat = run(encode(dag, target, p, 0, optimum), WORK, f"{dag.name}_sat")
    unsat = run(encode(dag, target, p, 0, optimum - 2), WORK, f"{dag.name}_unsat")
    assert sat.verdict == "SATISFIABLE" and sat.schedule_valid is True, sat
    assert unsat.verdict == "UNSATISFIABLE", unsat
    assert unsat.proof_status == "VERIFIED", unsat


def test_free_target_is_already_reached() -> None:
    """既存 BFS と同じく free target の M* は 0。"""
    require_tools()
    g = chain(2)
    result = run(encode(g, 0, p=0, e=0, k=4), WORK, "free_target")
    assert result.verdict == "SATISFIABLE", result
    assert result.schedule == ()
    assert result.schedule_valid is True


def test_unsat_is_not_certified_without_drat_checker(monkeypatch) -> None:
    """CaDiCaL の UNSAT だけでは認証済み下界にしない。"""
    require_tools()
    monkeypatch.setattr(sat_pebble, "DRAT_TRIM", "missing-drat-trim-for-test")
    result = run(encode(chain(2), 2, p=2, e=0, k=2), WORK, "no_checker")
    assert result.verdict == "UNSATISFIABLE", result
    assert result.proof_status == "UNAVAILABLE", result


@pytest.mark.parametrize("n,p,e,mstar", KNOWN)
def test_known_value_matches_bfs_and_both_decision_sides(
    n: int, p: int, e: int, mstar: int
) -> None:
    """k=M* は SAT、k=M*-2 は DRAT 検証済み UNSAT。"""
    require_tools()
    g = chain(n)
    assert landauer_bfs(g, n, p, e) == mstar

    sat = run(encode(g, n, p, e, mstar), WORK, f"n{n}_p{p}_e{e}_sat")
    assert sat.verdict == "SATISFIABLE", sat
    assert sat.schedule_valid is True, sat
    assert sat.schedule is not None and len(sat.schedule) <= mstar
    check = verify_schedule(g, n, p, e, mstar, sat.schedule)
    assert check.valid, check

    unsat = run(
        encode(g, n, p, e, mstar - 2),
        WORK,
        f"n{n}_p{p}_e{e}_unsat",
        solver_timeout=600,
        checker_timeout=1200,
    )
    assert unsat.verdict == "UNSATISFIABLE", unsat
    assert unsat.proof_status == "VERIFIED", unsat


def test_schedule_checker_rejects_illegal_put() -> None:
    """SAT 変数とは独立な手続き型検査器が不正手順を拒否する。"""
    g = chain(3)
    check = verify_schedule(g, 3, p=3, e=0, k=1, schedule=(("put", 3),))
    assert not check.valid
    assert "unavailable" in check.reason


@pytest.mark.parametrize(
    "kwargs",
    [
        {"target": -1, "p": 1, "e": 0, "k": 1},
        {"target": 4, "p": 1, "e": 0, "k": 1},
        {"target": 1, "p": -1, "e": 0, "k": 1},
        {"target": 1, "p": 1, "e": -1, "k": 1},
        {"target": 1, "p": 1, "e": 0, "k": -1},
    ],
)
def test_invalid_input_is_rejected(kwargs: dict[str, int]) -> None:
    with pytest.raises(ValueError):
        encode(chain(3), **kwargs)
