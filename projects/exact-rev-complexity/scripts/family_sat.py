"""台帳の**下界**に、機械検証可能な証明書を付ける（`data/families/sat.csv`）。

## この単位だけが下界に証書を付けられる

台帳の値の根拠は全数 BFS である。BFS は上界側にはスケジュールという**再生可能な証書**を
残すが、下界側（「これより短い手順は存在しない」）には**何も残らない**——
再確認するには同じ探索をやり直すしかない。

CP-SAT の `INFEASIBLE` も「ソルバがそう言った」であり第三者が検査できる証明ではない
（`scripts/sat_lower_bound.py` の docstring・`docs/31_tool_import.md` §10.4）。

SAT ソルバは UNSAT に **DRAT 証明**を出し、独立な検査器 `drat-trim` が検証する。
ここで得られる `VERIFIED` は、**このプロジェクトで下界側に付く唯一の証書**である。

## 何を UNSAT にするのか

$M^*$ は常に奇数（$M^*=2A-1$）なので、1 段良い手数は $M^*-2$ である。
「ピーク $p$・消去 0 でちょうど $M^*-2$ 手」を CNF にして UNSAT を示す。

### なぜ $M^*-2$ の 1 本で下界全体が言えるのか

**到達可能な手数は 2 刻みで上に閉じている。** 実際、任意の合法スケジュールの先頭に
「先行点が全て `free` な頂点 $v$ を put して即 take する」2 手を差し込めば、
ピークは $1\\le p$ を超えず、長さが 2 増えた合法スケジュールになる
（祖先に制限した DAG には必ずそのような $v$ がある）。したがって

  長さ $L$ が実現可能 $\\Rightarrow$ 長さ $L+2$ も実現可能

であり、対偶から **$M^*-2$ が UNSAT なら $M^*-4, M^*-6, \\dots$ も UNSAT** である。
$M^*$ 未満の長さは全て偶奇が合う $M^*-2, M^*-4,\\dots$ のいずれかなので、
$M^*-2$ の UNSAT 1 本で「$M^*$ 未満は不可能」が従う。
"""

from __future__ import annotations

import argparse
import csv
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from families import anc, build  # noqa: E402
from sat_lower_bound import encode, run  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "families"
ATLAS = OUT / "atlas.csv"
CSV_PATH = OUT / "sat.csv"
WORK = ROOT / "data" / "families" / "sat_work"

FIELDS = ["family", "params", "pebbleable", "p", "mstar", "moves_tested",
          "verdict", "checked", "vars", "clauses", "proof_bytes", "seconds"]


def rows_to_check(max_mstar: int) -> list[dict]:
    with ATLAS.open(encoding="utf-8", newline="") as fh:
        rows = [
            r for r in csv.DictReader(fh)
            if r["status"] == "exhaustive"
            and r["p"] == r["pmin"]
            # $M^*=1$（頂点 1 個）は絶対床 $2N-1$ そのもので、1 段良い手数が存在しない
            # （$M^*-2=-1$）。試す対象が無いので外す。
            and 3 <= int(r["mstar"]) <= max_mstar
        ]
    return sorted(rows, key=lambda r: int(r["mstar"]))


def _write(out: list[dict]) -> None:
    with CSV_PATH.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(out)


def _done_keys() -> set[tuple[str, str]]:
    """既に結果がある行（再開用）。`ERROR:` の行はやり直す。"""
    if not CSV_PATH.exists():
        return set()
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        return {
            (r["family"], r["params"]) for r in csv.DictReader(fh)
            if not r["verdict"].startswith("ERROR:")
        }


def cmd_build(max_mstar: int, timeout: float) -> int:
    """**1 行ごとに CSV を書く**（末尾でまとめて書かない）。

    2026-08-05・U9 で、$M^*\\le120$ の走行が全体の `timeout` に当たって
    **50 分ぶんの結果を丸ごと失った**。原因は書き出しが最後の 1 回だけだったこと。
    さらに `... | tail` に通していたためパイプの終了コードが `tail` のものになり、
    **強制終了が成功に見えていた**。両方ともここで塞ぐ。
    """
    OUT.mkdir(parents=True, exist_ok=True)
    out: list[dict] = []
    if CSV_PATH.exists():  # 既存の結果を引き継ぐ（再開）
        with CSV_PATH.open(encoding="utf-8", newline="") as fh:
            out = [r for r in csv.DictReader(fh) if not r["verdict"].startswith("ERROR:")]
    done = _done_keys()
    for row in rows_to_check(max_mstar):
        if (row["family"], row["params"]) in done:
            continue
        params = tuple(int(x) for x in row["params"].split(":"))
        ga, t = anc(build(row["family"], params))
        p, m = int(row["p"]), int(row["mstar"])
        moves = m - 2
        tag = f"{row['family']}_{'_'.join(map(str, params))}_p{p}_m{moves}"
        t0 = time.monotonic()
        try:
            cnf = encode(ga, t, p, 0, moves)
            res = run(cnf, WORK, tag, timeout=timeout)
        except Exception as exc:  # noqa: BLE001
            res = {"verdict": f"ERROR:{type(exc).__name__}", "vars": 0,
                   "clauses": 0, "proof_bytes": 0, "checked": None}
        el = time.monotonic() - t0
        out.append({
            "family": row["family"], "params": row["params"],
            "pebbleable": row["pebbleable"], "p": p, "mstar": m,
            "moves_tested": moves, "verdict": res["verdict"],
            "checked": res["checked"] or "", "vars": res["vars"],
            "clauses": res["clauses"], "proof_bytes": res["proof_bytes"],
            "seconds": f"{el:.1f}",
        })
        _write(out)  # ← 1 行ごとに永続化する。途中で殺されても失わない
        print(f"{row['family']}({row['params']}) p={p} M*={m}: {moves} 手は "
              f"{res['verdict']} / drat-trim {res['checked']} "
              f"({res['vars']} 変数 {res['clauses']} 節, {el:.1f}s)", flush=True)
    ver = sum(1 for r in out if r["checked"] == "VERIFIED")
    print(f"wrote {CSV_PATH} ({len(out)} 行 / drat-trim VERIFIED {ver})")
    return 0


def cmd_verify() -> int:
    """矛盾が無いことだけを検査する（軽い）。

    - `SATISFIABLE` が出た行があれば **BFS の $M^*$ が最適でない**ことになる（重大なバグ）。
    - `checked` が `FAILED` の行があれば DRAT 証明が壊れている。
    """
    if not CSV_PATH.exists():
        print("OK  sat.csv はまだ無い（U9 未実施）")
        return 0
    bad: list[str] = []
    ver = 0
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        for r in csv.DictReader(fh):
            tag = f"{r['family']}({r['params']}) p={r['p']}"
            if r["verdict"] == "SATISFIABLE":
                bad.append(f"{tag}: {r['moves_tested']} 手が SAT。"
                           f"台帳の M*={r['mstar']} は最適でない（BFS 側にバグ）")
            if r["checked"] == "FAILED":
                bad.append(f"{tag}: drat-trim が証明を検証できなかった")
            if r["checked"] == "VERIFIED":
                ver += 1
    for b in bad:
        print(f"NG: {b}")
    if bad:
        return 1
    print(f"OK  下界の DRAT 証明 {ver} 件が drat-trim で検証済み")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--max-mstar", type=int, default=30)
    ap.add_argument("--timeout", type=float, default=180.0)
    ns = ap.parse_args()
    if ns.build:
        return cmd_build(ns.max_mstar, ns.timeout)
    if ns.verify:
        return cmd_verify()
    ap.print_help()
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
