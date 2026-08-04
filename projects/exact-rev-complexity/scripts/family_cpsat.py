"""台帳の値を **CP-SAT で独立に確認する**（`data/families/cpsat.csv`）。

## なぜ要るか

台帳の値は全数 BFS（ビットマスク双方向）1 種類の探索から出ている。
`pebbleable <= 13` の行は素朴 frozenset BFS とも照合しているが、
**どちらも同じ「状態空間を全部見る」という発想**であり、モデルの解釈を共有している。

CP-SAT の retention interval 型定式化は**まったく別の発想**（各頂点の保持区間を
整数変数にして `add_cumulative` でピークを縛る）なので、ここで一致すれば
**独立な確認**になる。`status=OPTIMAL` なら下界も CP-SAT 側で証明されている。

## 注意（`cpsat_interval.py` の docstring より）

$C$（1 頂点あたりの区間数の上限）が小さすぎると**最適解を落とす**。
`solve_intervals_auto` は $C$ を増やして値が改善しなくなるまで繰り返す。
**単発の `solve_intervals` の結果を最適値として報告してはいけない。**

## 既知の弱点

`data/cpsat_interval_findings.md` §4 が記録するとおり、**$e=0$ の超線形領域では
BFS のほうが強い**。我々の族は全て $e=0$ なので、CP-SAT が `UNKNOWN` を返す行は
珍しくない。**それは失敗ではなく、住み分けの記録である**（黙って落とさず行を残す）。
"""

from __future__ import annotations

import argparse
import csv
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from cpsat_interval import solve_intervals_auto  # noqa: E402
from families import anc, build  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "families"
ATLAS = OUT / "atlas.csv"
CSV_PATH = OUT / "cpsat.csv"

FIELDS = ["family", "params", "pebbleable", "p", "bfs_mstar",
          "cpsat_mstar", "status", "cap", "cap_tight", "seconds"]


def rows_to_check(max_pebbleable: int) -> list[dict]:
    """$p=p_{\\min}$ の行だけを、小さい順に。"""
    with ATLAS.open(encoding="utf-8", newline="") as fh:
        rows = [
            r for r in csv.DictReader(fh)
            if r["status"] == "exhaustive"
            and r["p"] == r["pmin"]
            and int(r["pebbleable"]) <= max_pebbleable
        ]
    return sorted(rows, key=lambda r: int(r["pebbleable"]))


def cmd_build(max_pebbleable: int, seconds: float) -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    out: list[dict] = []
    for row in rows_to_check(max_pebbleable):
        params = tuple(int(x) for x in row["params"].split(":"))
        ga, t = anc(build(row["family"], params))
        p = int(row["p"])
        t0 = time.monotonic()
        r = solve_intervals_auto(ga, t, p, max_seconds=seconds)
        el = time.monotonic() - t0
        rec = {
            "family": row["family"], "params": row["params"],
            "pebbleable": row["pebbleable"], "p": p,
            "bfs_mstar": row["mstar"],
            "cpsat_mstar": "" if r.moves is None else r.moves,
            "status": r.status, "cap": r.cap,
            "cap_tight": "1" if r.cap_tight else "0",
            "seconds": f"{el:.1f}",
        }
        out.append(rec)
        mark = "OK " if str(r.moves) == row["mstar"] else "?? "
        print(f"{mark}{row['family']}({row['params']}) N={row['pebbleable']:>3s} p={p}: "
              f"BFS={row['mstar']:>4s} CPSAT={r.moves} [{r.status}] C={r.cap} {el:.1f}s",
              flush=True)
    with CSV_PATH.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(out)
    # 比較は文字列に揃える（`r.moves` は int、台帳の値は str）
    agree = sum(1 for r in out if str(r["cpsat_mstar"]) == r["bfs_mstar"])
    opt = sum(1 for r in out if r["status"] == "OPTIMAL")
    clean = sum(1 for r in out if r["status"] == "OPTIMAL" and r["cap_tight"] == "0")
    print(f"wrote {CSV_PATH} ({len(out)} 行 / OPTIMAL {opt}（うち C に余裕あり {clean}）"
          f" / 値を返した行が BFS と一致 {agree}）")
    return 0


def cmd_verify() -> int:
    """**矛盾が無いこと**だけを検査する（軽い）。

    `OPTIMAL` かつ BFS と食い違う行が 1 つでもあれば、**どちらかにバグがある**。
    `UNKNOWN` は矛盾ではないので通す。`FEASIBLE` は上界だけなので、
    BFS の値と等しいことだけ見る（下回っていたら BFS 側がおかしい）。
    """
    if not CSV_PATH.exists():
        print(f"NG: {CSV_PATH} が無い")
        return 1
    bad: list[str] = []
    opt = 0
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        for r in csv.DictReader(fh):
            tag = f"{r['family']}({r['params']}) p={r['p']}"
            if r["status"] != "OPTIMAL":
                continue
            opt += 1
            if r["cpsat_mstar"] != r["bfs_mstar"]:
                bad.append(f"{tag}: CP-SAT が OPTIMAL で {r['cpsat_mstar']}、"
                           f"BFS は {r['bfs_mstar']}（どちらかにバグ）")
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        for r in csv.DictReader(fh):
            if r["status"] == "FEASIBLE" and r["cpsat_mstar"]:
                if int(r["cpsat_mstar"]) < int(r["bfs_mstar"]):
                    bad.append(f"{r['family']}({r['params']}): CP-SAT が BFS より短い"
                               f"スケジュールを見つけた（{r['cpsat_mstar']} < {r['bfs_mstar']}）"
                               f"＝ BFS 側がおかしい")
    for b in bad:
        print(f"NG: {b}")
    if bad:
        return 1
    print(f"OK  CP-SAT の OPTIMAL 行 {opt} 件が BFS と矛盾しない")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--max-pebbleable", type=int, default=21)
    ap.add_argument("--seconds", type=float, default=20.0)
    ns = ap.parse_args()
    if ns.build:
        return cmd_build(ns.max_pebbleable, ns.seconds)
    if ns.verify:
        return cmd_verify()
    ap.print_help()
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
