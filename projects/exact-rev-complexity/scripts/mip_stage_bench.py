"""{interval, stage} × {CP-SAT, Gurobi, SCIP} の統一ベンチマーク。

`data/mip_findings.md` §2 の 8 ケースを、同一マシン・同一時間制限 (60s/solve)・
同一計測（auto ループ込みの end-to-end 秒）で走らせる。interval × {Gurobi, SCIP}
は `scripts/mip_interval.py` の __main__（別プロセスで実行済み）と重複するので
既定ではスキップし、`--all` で含める。

    .venv/bin/python scripts/mip_stage_bench.py [--all] [--hint] [--out CSV]
"""

from __future__ import annotations

import csv
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import cpsat_interval  # noqa: E402
import cpsat_stage  # noqa: E402
import mip_interval  # noqa: E402
import mip_stage  # noqa: E402
from landauer import landauer_bfs  # noqa: E402
from revpebble import bfs, chain  # noqa: E402

CASES = [(4, 3, 0), (4, 3, 1), (6, 4, 0), (6, 4, 1),
         (8, 4, 0), (8, 4, 1), (12, 5, 0), (12, 5, 1)]
SECONDS = 60.0
WORKERS = 8


def solvers(include_interval_mip: bool, hint: bool):
    out = {
        "interval-cpsat": lambda g, t, p, e: cpsat_interval.solve_intervals_auto(
            g, t, p, e, max_seconds=SECONDS, workers=WORKERS
        ),
        "stage-cpsat": lambda g, t, p, e: cpsat_stage.solve_stage_auto(
            g, t, p, e, max_seconds=SECONDS, workers=WORKERS, hint=hint
        ),
        "stage-gurobi": lambda g, t, p, e: mip_stage.solve_stage_auto(
            g, t, p, e, backend="gurobi", max_seconds=SECONDS,
            workers=WORKERS, hint=hint
        ),
        "stage-scip": lambda g, t, p, e: mip_stage.solve_stage_auto(
            g, t, p, e, backend="scip", max_seconds=SECONDS,
            workers=WORKERS, hint=hint
        ),
    }
    if include_interval_mip:
        out["interval-gurobi"] = lambda g, t, p, e: mip_interval.solve_intervals_auto(
            g, t, p, e, backend="gurobi", max_seconds=SECONDS, workers=WORKERS
        )
        out["interval-scip"] = lambda g, t, p, e: mip_interval.solve_intervals_auto(
            g, t, p, e, backend="scip", max_seconds=SECONDS, workers=WORKERS
        )
    return out


def main() -> int:
    include_all = "--all" in sys.argv
    hint = "--hint" in sys.argv
    out_path = None
    if "--out" in sys.argv:
        out_path = Path(sys.argv[sys.argv.index("--out") + 1])
    rows = []
    table = solvers(include_all, hint)
    print(f"{'solver':<16} {'case':<16} {'moves':>6} {'BFS':>5} {'status':>9} {'秒':>8}  一致")
    for n, p, e in CASES:
        b = landauer_bfs(chain(n), n, p, e) if e else bfs(chain(n), n, p)[0]
        for name, fn in table.items():
            t0 = time.perf_counter()
            r = fn(chain(n), n, p, e)
            dt = time.perf_counter() - t0
            ok = r.moves == b
            rows.append(
                dict(solver=name, case=f"chain({n})", e=e, p=p,
                     moves=r.moves, bfs=b, status=r.status,
                     seconds=round(dt, 2), agree=int(bool(ok)))
            )
            print(
                f"{name:<16} chain({n}) e={e:<5} {str(r.moves):>6} {b:>5} "
                f"{r.status:>9} {dt:>8.2f}  {'○' if ok else '**×**'}",
                flush=True,
            )
    if out_path:
        with out_path.open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=list(rows[0]))
            w.writeheader()
            w.writerows(rows)
        print(f"→ {out_path}")
    bad = [r for r in rows if r["moves"] is not None and not r["agree"]]
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
