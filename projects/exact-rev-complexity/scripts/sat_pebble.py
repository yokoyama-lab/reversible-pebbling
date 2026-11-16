"""$M^*(G,p,e) <= k$ を CNF にし、CaDiCaL + DRAT で判定する。

符号化の事前仕様と正当性は ``data/sat_encoding_design.md`` を参照。
対象は 1 手 1 頂点の不可逆消去（``landauer.py`` の ``mode="ops"``）。

UNSAT は CaDiCaL の表示だけでは証明済みと扱わない。既定動作では ASCII DRAT を
保存し、PATH 上の ``drat-trim`` が ``s VERIFIED`` を返した場合だけ認証済みとする。

例::

    .venv/bin/python scripts/sat_pebble.py --n 8 --p 4 --e 0 --k 23
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag, chain  # noqa: E402

CADICAL = "cadical"
DRAT_TRIM = "drat-trim"

Move = tuple[str, int]


class Cnf:
    """小さな DIMACS CNF ビルダ。"""

    def __init__(self) -> None:
        self.nvars = 0
        self.clauses: list[list[int]] = []

    @property
    def n(self) -> int:
        """既存の ``sat_lower_bound.Cnf`` と揃えた変数数エイリアス。"""
        return self.nvars

    def var(self) -> int:
        self.nvars += 1
        return self.nvars

    def add(self, *lits: int) -> None:
        if any(lit == 0 for lit in lits):
            raise ValueError("0 is the DIMACS clause terminator, not a literal")
        self.clauses.append(list(lits))

    def add_list(self, lits: Iterable[int]) -> None:
        clause = list(lits)
        if any(lit == 0 for lit in clause):
            raise ValueError("0 is the DIMACS clause terminator, not a literal")
        self.clauses.append(clause)

    def at_most_k(self, lits: Sequence[int], bound: int) -> None:
        """Sinz 型逐次カウンタで ``sum(lits) <= bound`` を課す。"""
        xs = list(lits)
        if bound < 0:
            self.add()  # 空節 = UNSAT
            return
        if bound >= len(xs):
            return
        if bound == 0:
            for lit in xs:
                self.add(-lit)
            return

        # s[i][j]: 先頭 i+1 入力で少なくとも j+1 個が真なら真。
        s = [[self.var() for _ in range(bound)] for _ in xs]
        self.add(-xs[0], s[0][0])
        for j in range(1, bound):
            self.add(-s[0][j])
        for i in range(1, len(xs)):
            self.add(-xs[i], s[i][0])
            self.add(-s[i - 1][0], s[i][0])
            for j in range(1, bound):
                self.add(-xs[i], -s[i - 1][j - 1], s[i][j])
                self.add(-s[i - 1][j], s[i][j])
            self.add(-xs[i], -s[i - 1][bound - 1])

    def exactly_one(self, lits: Sequence[int]) -> None:
        xs = list(lits)
        self.add_list(xs)
        self.at_most_k(xs, 1)

    def dimacs(self) -> str:
        header = f"p cnf {self.nvars} {len(self.clauses)}\n"
        body = "".join(" ".join(map(str, clause)) + " 0\n" for clause in self.clauses)
        return header + body


@dataclass(frozen=True)
class PebbleEncoding:
    """CNF と SAT モデル復号に必要な変数表。"""

    cnf: Cnf
    dag: Dag
    target: int
    p: int
    e: int
    k: int
    vertices: tuple[int, ...]
    x: dict[tuple[int, int], int]
    put: dict[tuple[int, int], int]
    take: dict[tuple[int, int], int]
    idle: dict[int, int]
    available: dict[tuple[int, int], int]
    irreversible: dict[tuple[int, int], int]


@dataclass(frozen=True)
class ScheduleCheck:
    valid: bool
    reason: str
    moves: int
    peak: int
    erasures: int


@dataclass(frozen=True)
class SatResult:
    verdict: str
    proof_status: str
    vars: int
    clauses: int
    cnf_path: Path
    proof_path: Path
    proof_bytes: int
    solver_seconds: float
    checker_seconds: float | None
    solver_returncode: int | None
    checker_returncode: int | None
    schedule: tuple[Move, ...] | None = None
    schedule_valid: bool | None = None
    detail: str = ""


def _validate_input(dag: Dag, target: int, p: int, e: int, k: int) -> None:
    if not 0 <= target < dag.n:
        raise ValueError(f"target must be in 0..{dag.n - 1}: {target}")
    if p < 0:
        raise ValueError(f"p must be nonnegative: {p}")
    if e < 0:
        raise ValueError(f"e must be nonnegative: {e}")
    if k < 0:
        raise ValueError(f"k must be nonnegative: {k}")


def encode(dag: Dag, target: int, p: int, e: int, k: int) -> PebbleEncoding:
    """決定問題 ``M*(dag,target,p,e) <= k`` と同値な CNF を返す。"""
    _validate_input(dag, target, p, e, k)
    vertices = tuple(dag.pebbleable())
    cnf = Cnf()

    # free target は既存 BFS の規約で既に達成済み（M*=0）。
    if target in dag.free:
        return PebbleEncoding(
            cnf, dag, target, p, e, k, vertices, {}, {}, {}, {}, {}, {}
        )

    x = {(t, v): cnf.var() for t in range(k + 1) for v in vertices}
    put = {(t, v): cnf.var() for t in range(k) for v in vertices}
    take = {(t, v): cnf.var() for t in range(k) for v in vertices}
    idle = {t: cnf.var() for t in range(k)}
    available = {(t, v): cnf.var() for t in range(k) for v in vertices}
    irreversible = {(t, v): cnf.var() for t in range(k) for v in vertices}

    # 空の初期配置と clean 終端。
    for v in vertices:
        cnf.add(-x[0, v])
        cnf.add(x[k, v] if v == target else -x[k, v])

    # 各ステップは idle / put / take のちょうど一つ。idle は接尾辞に正規化。
    for t in range(k):
        actions = (
            [idle[t]] + [put[t, v] for v in vertices] + [take[t, v] for v in vertices]
        )
        cnf.exactly_one(actions)
        if t + 1 < k:
            cnf.add(-idle[t], idle[t + 1])

    for t in range(k):
        for v in vertices:
            need = [x[t, u] for u in dag.preds[v] if u not in dag.free]
            av = available[t, v]
            if not need:
                cnf.add(av)
            else:
                for pred_lit in need:
                    cnf.add(-av, pred_lit)
                cnf.add_list([av] + [-pred_lit for pred_lit in need])

            pv = put[t, v]
            rv = take[t, v]
            before = x[t, v]
            after = x[t + 1, v]

            # put/take の作用域と、非操作頂点の frame axiom。
            cnf.add(-pv, -before)
            cnf.add(-pv, after)
            cnf.add(-rv, before)
            cnf.add(-rv, -after)
            cnf.add(pv, rv, -before, after)
            cnf.add(pv, rv, before, -after)

            # put は可用なときだけ。take ∧ ¬available が不可逆消去。
            cnf.add(-pv, av)
            irr = irreversible[t, v]
            cnf.add(-irr, rv)
            cnf.add(-irr, -av)
            cnf.add(-rv, av, irr)

    for t in range(k + 1):
        cnf.at_most_k([x[t, v] for v in vertices], p)
    cnf.at_most_k([irreversible[t, v] for t in range(k) for v in vertices], e)

    return PebbleEncoding(
        cnf,
        dag,
        target,
        p,
        e,
        k,
        vertices,
        x,
        put,
        take,
        idle,
        available,
        irreversible,
    )


def verify_schedule(
    dag: Dag,
    target: int,
    p: int,
    e: int,
    k: int,
    schedule: Sequence[Move],
) -> ScheduleCheck:
    """CNF とは独立に、復号した put/take 列をゲーム定義で検査する。"""
    try:
        _validate_input(dag, target, p, e, k)
    except ValueError as exc:
        return ScheduleCheck(False, str(exc), 0, 0, 0)
    if len(schedule) > k:
        return ScheduleCheck(False, f"too many moves: {len(schedule)} > {k}", 0, 0, 0)

    movable = set(dag.pebbleable())
    state: set[int] = set()
    peak = 0
    erasures = 0
    for step, move in enumerate(schedule):
        if len(move) != 2:
            return ScheduleCheck(
                False, f"step {step}: malformed move {move!r}", step, peak, erasures
            )
        kind, v = move
        if v not in movable:
            return ScheduleCheck(
                False, f"step {step}: vertex {v} is not movable", step, peak, erasures
            )
        is_available = all(u in dag.free or u in state for u in dag.preds[v])
        if kind == "put":
            if v in state:
                return ScheduleCheck(
                    False,
                    f"step {step}: put on occupied vertex {v}",
                    step,
                    peak,
                    erasures,
                )
            if not is_available:
                return ScheduleCheck(
                    False, f"step {step}: unavailable put({v})", step, peak, erasures
                )
            state.add(v)
        elif kind == "take":
            if v not in state:
                return ScheduleCheck(
                    False,
                    f"step {step}: take from empty vertex {v}",
                    step,
                    peak,
                    erasures,
                )
            if not is_available:
                erasures += 1
            state.remove(v)
        else:
            return ScheduleCheck(
                False, f"step {step}: unknown action {kind!r}", step, peak, erasures
            )
        peak = max(peak, len(state))
        if peak > p:
            return ScheduleCheck(
                False,
                f"step {step}: peak {peak} exceeds p={p}",
                step + 1,
                peak,
                erasures,
            )
        if erasures > e:
            return ScheduleCheck(
                False,
                f"step {step}: erasures {erasures} exceeds e={e}",
                step + 1,
                peak,
                erasures,
            )

    goal = set() if target in dag.free else {target}
    if state != goal:
        return ScheduleCheck(
            False,
            f"unclean final state: {sorted(state)}, expected {sorted(goal)}",
            len(schedule),
            peak,
            erasures,
        )
    return ScheduleCheck(True, "VERIFIED", len(schedule), peak, erasures)


def _parse_verdict(stdout: str) -> str:
    for line in stdout.splitlines():
        if line.startswith("s "):
            answer = line[2:].strip()
            if answer in {"SATISFIABLE", "UNSATISFIABLE", "UNKNOWN"}:
                return answer
    return "UNKNOWN"


def _parse_model(stdout: str) -> dict[int, bool]:
    model: dict[int, bool] = {}
    for line in stdout.splitlines():
        if not line.startswith("v "):
            continue
        for token in line[2:].split():
            lit = int(token)
            if lit:
                model[abs(lit)] = lit > 0
    return model


def _decode_schedule(enc: PebbleEncoding, model: dict[int, bool]) -> tuple[Move, ...]:
    if enc.target in enc.dag.free:
        return ()
    out: list[Move] = []
    for t in range(enc.k):
        if model.get(enc.idle[t], False):
            continue
        selected: list[Move] = []
        for v in enc.vertices:
            if model.get(enc.put[t, v], False):
                selected.append(("put", v))
            if model.get(enc.take[t, v], False):
                selected.append(("take", v))
        if len(selected) != 1:
            raise ValueError(f"step {t}: model has {len(selected)} non-idle actions")
        out.append(selected[0])
    return tuple(out)


def run(
    problem: Cnf | PebbleEncoding,
    workdir: Path,
    tag: str,
    *,
    solver_timeout: float = 300.0,
    checker_timeout: float = 1200.0,
    verify_proof: bool = True,
) -> SatResult:
    """CaDiCaL を実行し、UNSAT なら独立に DRAT を検査する。"""
    encoding = problem if isinstance(problem, PebbleEncoding) else None
    cnf = problem.cnf if encoding is not None else problem
    cadical = shutil.which(CADICAL)
    if cadical is None:
        raise FileNotFoundError(f"{CADICAL} is not on PATH")

    workdir.mkdir(parents=True, exist_ok=True)
    cnf_path = workdir / f"{tag}.cnf"
    proof_path = workdir / f"{tag}.drat"
    cnf_path.write_text(cnf.dimacs(), encoding="ascii")
    proof_path.unlink(missing_ok=True)

    started = time.monotonic()
    try:
        solved = subprocess.run(
            [cadical, "--binary=false", "-q", str(cnf_path), str(proof_path)],
            capture_output=True,
            text=True,
            timeout=solver_timeout,
            check=False,
        )
        solver_seconds = time.monotonic() - started
        verdict = _parse_verdict(solved.stdout)
        solver_returncode: int | None = solved.returncode
        detail = solved.stderr.strip()
    except subprocess.TimeoutExpired as exc:
        solver_seconds = time.monotonic() - started
        verdict = "UNKNOWN"
        solver_returncode = None
        detail = f"CaDiCaL timed out after {solver_timeout:g}s: {exc}"
        solved = None

    # SAT 走行中の proof trace は UNSAT 証明ではなく、誤認と容量浪費を避ける。
    if verdict == "SATISFIABLE":
        proof_path.unlink(missing_ok=True)

    schedule: tuple[Move, ...] | None = None
    schedule_valid: bool | None = None
    if verdict == "SATISFIABLE" and encoding is not None and solved is not None:
        try:
            schedule = _decode_schedule(encoding, _parse_model(solved.stdout))
            checked_schedule = verify_schedule(
                encoding.dag,
                encoding.target,
                encoding.p,
                encoding.e,
                encoding.k,
                schedule,
            )
            schedule_valid = checked_schedule.valid
            if not checked_schedule.valid:
                detail = (
                    f"SAT model schedule failed verification: {checked_schedule.reason}"
                )
        except (ValueError, KeyError) as exc:
            schedule_valid = False
            detail = f"SAT model decoding failed: {exc}"

    proof_status = "NOT_APPLICABLE"
    checker_seconds: float | None = None
    checker_returncode: int | None = None
    if verdict == "UNSATISFIABLE":
        if not verify_proof:
            proof_status = "NOT_RUN"
        else:
            checker = shutil.which(DRAT_TRIM)
            if checker is None:
                proof_status = "UNAVAILABLE"
                detail = f"{DRAT_TRIM} is not on PATH"
            elif not proof_path.exists():
                proof_status = "MISSING"
                detail = f"CaDiCaL did not create {proof_path}"
            else:
                check_started = time.monotonic()
                try:
                    checked = subprocess.run(
                        [checker, str(cnf_path), str(proof_path)],
                        capture_output=True,
                        text=True,
                        timeout=checker_timeout,
                        check=False,
                    )
                    checker_seconds = time.monotonic() - check_started
                    checker_returncode = checked.returncode
                    checker_text = checked.stdout + "\n" + checked.stderr
                    if checked.returncode == 0 and "s VERIFIED" in checker_text:
                        proof_status = "VERIFIED"
                    else:
                        proof_status = "FAILED"
                        detail = checker_text.strip()[-2000:]
                except subprocess.TimeoutExpired as exc:
                    checker_seconds = time.monotonic() - check_started
                    proof_status = "TIMEOUT"
                    detail = f"drat-trim timed out after {checker_timeout:g}s: {exc}"

    return SatResult(
        verdict=verdict,
        proof_status=proof_status,
        vars=cnf.nvars,
        clauses=len(cnf.clauses),
        cnf_path=cnf_path,
        proof_path=proof_path,
        proof_bytes=proof_path.stat().st_size if proof_path.exists() else 0,
        solver_seconds=solver_seconds,
        checker_seconds=checker_seconds,
        solver_returncode=solver_returncode,
        checker_returncode=checker_returncode,
        schedule=schedule,
        schedule_valid=schedule_valid,
        detail=detail,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, required=True, help="chain(n) の長さ")
    parser.add_argument("--p", type=int, required=True, help="ピークペブル数")
    parser.add_argument("--e", type=int, default=0, help="不可逆消去予算")
    parser.add_argument("--k", type=int, required=True, help="手数上限")
    parser.add_argument("--timeout", type=float, default=300.0, help="CaDiCaL 秒数上限")
    parser.add_argument(
        "--checker-timeout", type=float, default=1200.0, help="drat-trim 秒数上限"
    )
    parser.add_argument("--workdir", type=Path, default=Path("/tmp/sat_pebble"))
    parser.add_argument("--show-schedule", action="store_true")
    args = parser.parse_args()

    dag = chain(args.n)
    encoding = encode(dag, args.n, args.p, args.e, args.k)
    tag = f"chain{args.n}_p{args.p}_e{args.e}_k{args.k}"
    result = run(
        encoding,
        args.workdir,
        tag,
        solver_timeout=args.timeout,
        checker_timeout=args.checker_timeout,
    )

    print(f"chain({args.n}) p={args.p} e={args.e}: M* <= {args.k} ? {result.verdict}")
    print(
        f"CNF: {result.vars} variables, {result.clauses} clauses, "
        f"CaDiCaL {result.solver_seconds:.3f}s"
    )
    print(f"CNF file: {result.cnf_path}")
    if result.verdict == "SATISFIABLE":
        status = "VERIFIED" if result.schedule_valid else "FAILED"
        print(f"decoded schedule: {status} ({len(result.schedule or ())} moves)")
        if args.show_schedule and result.schedule is not None:
            print("schedule:", " ".join(f"{kind}({v})" for kind, v in result.schedule))
        if result.detail:
            print(result.detail, file=sys.stderr)
        return 0 if result.schedule_valid else 1

    if result.verdict == "UNSATISFIABLE":
        checker_time = (
            "n/a"
            if result.checker_seconds is None
            else f"{result.checker_seconds:.3f}s"
        )
        print(
            f"DRAT: {result.proof_path} ({result.proof_bytes} bytes); "
            f"drat-trim {result.proof_status} in {checker_time}"
        )
        if result.proof_status == "VERIFIED":
            print(f"CERTIFIED LOWER BOUND: M* > {args.k}")
            return 0
        print(
            "CaDiCaL は UNSAT と報告したが証明は未検証: " + result.proof_status,
            file=sys.stderr,
        )
        if result.detail:
            print(result.detail, file=sys.stderr)
        return 1

    print("decision unresolved (UNKNOWN)", file=sys.stderr)
    if result.detail:
        print(result.detail, file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
