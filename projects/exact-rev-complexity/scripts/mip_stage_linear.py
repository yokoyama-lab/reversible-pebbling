"""線形領域（e ≥ e*、M* = 2n-1）でのステージ定式化の限界測定。

interval-CP-SAT はこの領域で n=160 まで到達している
（`data/cpsat_interval_findings.md` §3。C=1 でモデルが O(n) に潰れるため）。
ステージ定式化は K ≈ n 段 × n 頂点で O(n^2) 変数になるので、
**この領域では interval に負けるはず**という予想を検証する。

e* の値は cpsat_interval_findings §3 の表と同じ設定
（(n,p,e*) = (30,7,4), (50,8,6), (80,9,9)）。定理 A の補題 L0 が
M* ≥ 2n-1 を無条件に保証するので、OPTIMAL が 2n-1 を下回ったら
定式化のバグである（そのときは声を上げて止まる）。

    .venv/bin/python scripts/mip_stage_linear.py [--seconds S]
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import cpsat_stage  # noqa: E402
import mip_stage  # noqa: E402
from revpebble import chain  # noqa: E402

CASES = [(30, 7, 4), (50, 8, 6), (80, 9, 9)]


def main() -> int:
    seconds = 60.0
    if "--seconds" in sys.argv:
        seconds = float(sys.argv[sys.argv.index("--seconds") + 1])
    print(f"{'case':<18} {'solver':<7} {'K方針':>6} {'moves':>6} {'status':>9} {'秒':>8}")
    for n, p, e in CASES:
        for sname, fn in (
            ("cpsat", lambda g, t, pp, ee, k: cpsat_stage.solve_stage_auto(
                g, t, pp, ee, max_seconds=seconds, k_start=k, k_limit=1024)),
            ("gurobi", lambda g, t, pp, ee, k: mip_stage.solve_stage_auto(
                g, t, pp, ee, backend="gurobi", max_seconds=seconds,
                k_start=k, k_limit=1024)),
        ):
            for k_label, k_start in (("n+4", n + 4), ("2n", 2 * n)):
                t0 = time.perf_counter()
                r = fn(chain(n), n, p, e, k_start)
                dt = time.perf_counter() - t0
                if r.moves is not None and r.moves < 2 * n - 1:
                    raise SystemExit(
                        f"定式化バグ疑い: chain({n}) e={e} が M={r.moves} < 2n-1"
                    )
                print(
                    f"chain({n})p{p}e{e:<3} {sname:<7} {k_label:>6} "
                    f"{str(r.moves):>6} {r.status:>9} {dt:>8.2f}",
                    flush=True,
                )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
