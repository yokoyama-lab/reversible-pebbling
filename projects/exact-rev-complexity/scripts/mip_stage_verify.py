"""ブロック標準形定式化の全面照合: BFS ⟷ stage-Gurobi ⟷ stage-CP-SAT ⟷ stage-SCIP。

**一致確認が通った範囲でのみ外挿値を使う**（`docs/30_cross_field.md` §1.6）。
対象は
  - 鎖 n=1..8、p ∈ {pmin, pmin+1}、e ∈ {0,1,2}
  - 完全二分木 h=1..2・ピラミッド h=1..2、p ∈ {pmin, pmin+1}、e ∈ {0,1}
  - 決定的擬似乱数 DAG（seed 固定 = 再現可能）n=4..6、e ∈ {0,1}
到達不能ケース（BFS が None）は INFEASIBLE 判定の一致も確認する。

    .venv/bin/python scripts/mip_stage_verify.py [--fast]

--fast は SCIP を鎖のみに間引く（SCIP は小モデルでも他より遅いため）。
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import cpsat_stage  # noqa: E402
import mip_stage  # noqa: E402
from landauer import landauer_bfs  # noqa: E402
from revpebble import (  # noqa: E402
    Dag,
    bfs,
    chain,
    complete_binary_tree,
    pmin,
    pyramid,
    restrict_to_ancestors,
)


def random_dag(n: int, seed: int) -> Dag:
    """決定的な擬似乱数 DAG。先頭の source を free にする。"""
    rng = random.Random(seed)
    preds: list[frozenset[int]] = []
    for v in range(n):
        if v == 0:
            preds.append(frozenset())
            continue
        k = rng.randint(1, min(2, v))
        preds.append(frozenset(rng.sample(range(v), k)))
    free = frozenset(
        v for v in range(n) if not preds[v] and rng.random() < 0.7
    )
    return Dag(n=n, preds=tuple(preds), free=free, name=f"rand({n},{seed})")


def truth(dag: Dag, target: int, p: int, e: int) -> int | None:
    if e == 0:
        return bfs(dag, target, p)[0]
    return landauer_bfs(dag, target, p, e)


def cases():
    for n in range(1, 9):
        g = chain(n)
        pm = pmin(g, n)
        if pm is None:
            continue
        for p in (pm, pm + 1):
            for e in (0, 1, 2):
                yield g, n, p, e, True
        # 到達不能側: pmin - 1
        if pm >= 2:
            yield g, n, pm - 1, 0, True
    for h in (1, 2):
        for g in (complete_binary_tree(h), pyramid(h)):
            tgt = g.n - 1
            pm = pmin(g, tgt)
            if pm is None:
                continue
            for p in (pm, pm + 1):
                for e in (0, 1):
                    yield g, tgt, p, e, False
    for n in (4, 5, 6):
        for seed in range(6):
            g = random_dag(n, seed=100 * n + seed)
            tgt = n - 1
            if tgt in g.free:
                continue
            rg, rt = restrict_to_ancestors(g, tgt)
            pm = pmin(rg, rt)
            if pm is None:
                continue
            for p in (pm, pm + 1):
                for e in (0, 1):
                    yield g, tgt, p, e, False


def main() -> int:
    fast = "--fast" in sys.argv
    n_cases = 0
    wrong = []       # 値の誤り（致命的: 定式化かソルバのバグ）
    incomplete = []  # UNKNOWN で終了（誤値ではないが証明を出せなかった）
    for g, tgt, p, e, scip_ok in cases():
        b = truth(g, tgt, p, e)
        results = {
            "gurobi": mip_stage.solve_stage_auto(
                g, tgt, p, e, backend="gurobi", max_seconds=60, k_limit=128
            ),
            "cpsat": cpsat_stage.solve_stage_auto(
                g, tgt, p, e, max_seconds=60, k_limit=128
            ),
        }
        if scip_ok or not fast:
            results["scip"] = mip_stage.solve_stage_auto(
                g, tgt, p, e, backend="scip", max_seconds=60, k_limit=128
            )
        n_cases += 1
        for name, r in results.items():
            case = (g.name, tgt, p, e, name, b, r.moves, r.status)
            if b is None:
                if r.moves is not None:
                    wrong.append(case)  # 到達不能なのに値を返した
                elif not r.status.startswith("INFEASIBLE"):
                    incomplete.append(case)
            else:
                if r.moves is None:
                    incomplete.append(case)
                elif r.moves != b or r.status != "OPTIMAL":
                    wrong.append(case)
    for tag, rows in (("誤値", wrong), ("未完", incomplete)):
        for g_name, tgt, p, e, name, b, got, st in rows:
            print(f"{tag}: {g_name} target={tgt} p={p} e={e} {name}: BFS={b} got={got} ({st})")
    print(f"{n_cases} ケース × 3 ソルバ照合: 誤値 {len(wrong)} 件・未完 {len(incomplete)} 件")
    if wrong:
        print("### 誤値あり（要調査。この範囲の外挿値は使用禁止）")
        return 1
    print("値の誤りゼロ: BFS ⟷ stage-Gurobi ⟷ stage-CP-SAT" + ("" if fast else " ⟷ stage-SCIP"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
