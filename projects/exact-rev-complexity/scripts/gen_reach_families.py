"""`data/reach_families.md` を生成する（**手編集禁止**。data/ は自動生成）。

    python3 scripts/gen_reach_families.py --csv data/reach_pyramid.csv data/reach_cbt.csv ...

入力は `scripts/exp03_reach_dag.py --out` が吐く CSV
（列: family,p,e,reach,status,reason）。

出力の約束:
- **`exact` と `UNKNOWN` を必ず区別する**。上限に当たって決まらなかった升は `?` と書き、
  空欄や `-`（＝不可解）とは別扱いにする。理由も脚注に残す
  （`~/.claude/rules`「打ち切り値を結果と読まない」）。
- 族をまたいで比べられるよう、族の添字だけでなく**その要素の頂点数**も併記する。
  鎖は添字＝頂点数だが、cbt(h)・pyramid(h) は h を 1 増やすと頂点数が跳ぶ。
- **予想は書かない。** 差分列だけを出し、判断は読み手（と後続セッション）に渡す。
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from exp03_reach_dag import FAMILIES  # noqa: E402

DATA = ROOT / "data"


def load(paths: list[Path]) -> dict[str, dict[tuple[int, int], tuple[str, str, str]]]:
    out: dict[str, dict[tuple[int, int], tuple[str, str, str]]] = {}
    for path in paths:
        with path.open(encoding="utf-8") as fh:
            for row in csv.DictReader(fh):
                fam = row["family"]
                out.setdefault(fam, {})[(int(row["p"]), int(row["e"]))] = (
                    row["reach"], row["status"], row.get("reason", ""))
    return out


def _sizes(fam: str, k: int) -> tuple[int, int]:
    g = FAMILIES[fam](k)
    return g.n, len(g.pebbleable())


def render_family(fam: str, tbl: dict[tuple[int, int], tuple[str, str, str]]) -> list[str]:
    ps = sorted({p for p, _ in tbl})
    es = sorted({e for _, e in tbl})
    out: list[str] = []
    out.append(f"### 族 `{fam}`")
    out.append("")
    # 本体表
    out.append("`reach_" + fam + "(p,e)` = その族で p ペブル・e 消去で clean 可解な最大の添字。")
    out.append("")
    out.append("記号: 数値 = 厳密確定 / **`?` = 上限に当たって決まらなかった**（不可解ではない） / "
               "**`·` = まだ計算していない**（実行中・未着手）。")
    out.append("**3 つを混ぜないこと。** `?` と `·` はどちらも「不可解」ではない。")
    out.append("")
    out.append("| p \\ e | " + " | ".join(str(e) for e in es) + " |")
    out.append("|---" * (len(es) + 1) + "|")
    for p in ps:
        cells = []
        for e in es:
            v, st, _ = tbl.get((p, e), ("", "missing", ""))
            cells.append(v if st == "exact" else ("·" if st == "missing" else "?"))
        out.append(f"| **{p}** | " + " | ".join(cells) + " |")
    out.append("")
    # 頂点数での併記（族をまたいだ比較用）
    out.append("同じ表を**頂点数**で（`F(reach)` の頂点数 / うち free でないもの）:")
    out.append("")
    out.append("| p \\ e | " + " | ".join(str(e) for e in es) + " |")
    out.append("|---" * (len(es) + 1) + "|")
    for p in ps:
        cells = []
        for e in es:
            v, st, _ = tbl.get((p, e), ("", "missing", ""))
            if st == "exact" and v != "":
                n, m = _sizes(fam, int(v))
                cells.append(f"{n}/{m}")
            else:
                cells.append("·" if st == "missing" else "?")
        out.append(f"| **{p}** | " + " | ".join(cells) + " |")
    out.append("")
    # e 方向の差分（予想は書かない）
    out.append("`e` 方向の階差 `reach(p,e+1) − reach(p,e)`（確定升のみ）:")
    out.append("")
    out.append("| p | " + " | ".join(f"{e}→{e+1}" for e in es[:-1]) + " |")
    out.append("|---" * len(es) + "|")
    for p in ps:
        cells = []
        for a, b in zip(es, es[1:]):
            va, sa, _ = tbl.get((p, a), ("", "x", ""))
            vb, sb, _ = tbl.get((p, b), ("", "x", ""))
            if sa == "exact" and sb == "exact":
                cells.append(str(int(vb) - int(va)))
            elif "missing" in (sa, sb):
                cells.append("·")
            else:
                cells.append("?")
        out.append(f"| **{p}** | " + " | ".join(cells) + " |")
    out.append("")
    # 打ち切り理由
    n_missing = sum(1 for p in ps for e in es if (p, e) not in tbl)
    if n_missing:
        out.append(f"**未計算の升 `·` が {n_missing} 個ある**（この族はまだ回し終えていない）。")
        out.append("")
    reasons = sorted({r for (_p, _e), (_v, st, r) in tbl.items() if st != "exact" and r})
    if reasons:
        out.append("打ち切りの理由（`?` の升）:")
        out.append("")
        for r in reasons:
            out.append(f"- {r}")
        out.append("")
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--csv", nargs="+", required=True)
    ap.add_argument("--out", default=str(DATA / "reach_families.md"))
    ap.add_argument("--note", default="", help="冒頭に入れる補足（実行環境など）")
    args = ap.parse_args()

    data = load([Path(c) for c in args.csv])
    lines = [
        "# `reach_F(p,e)` — 族ごとの厳密値",
        "",
        "**自動生成**（`scripts/gen_reach_families.py`）。手編集しないこと。",
        "",
        "定義: `reach_F(p,e) = max{ k : F(k) が p ペブル・e 回の不可逆消去で clean 可解 }`。",
        "モデルは `scripts/exp03_reach_dag.py`（= `scripts/landauer.py` の `mode=\"ops\"`）。",
        "",
        "**読み方の約束**:",
        "",
        "- `?` は**打ち切りで決まらなかった**升であり、「不可解」ではない。",
        "  上限（訪問表のメモリ／確定状態数）を上げれば決まる可能性がある。",
        "- 族の添字は族ごとに意味が違う（鎖は頂点数、cbt/pyramid は高さ）。",
        "  族をまたいで比べるときは**頂点数の表**のほうを見ること。",
        "- **本ファイルに予想は書かない。** 階差だけを出す。",
        "  少数点の当てはめは過去 4 回崩れている（`CLAUDE.md`、`data/exp01_findings.md` §4）。",
        "",
    ]
    if args.note:
        lines += [args.note, ""]
    lines += ["---", ""]
    for fam in sorted(data):
        lines += render_family(fam, data[fam])
        lines += ["---", ""]
    Path(args.out).write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"-> {args.out}  ({len(data)} 族)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
