"""JSSST レター（アトラス Phase 4）の表を CSV から生成する（**手打ち禁止**の規約）。

出力先は Overleaf 側（`~/dev/overleaf/2026_resource_atlas_letter/tables/`）。
`main.tex` は `tables/` を `\\input` で取り込む。候補3論文の `gen_tables.py` と同じ運用。

    python3 scripts/gen_atlas_tables.py

- 表1 カテゴリ別の要約（`data/atlas/atlas.csv`、findings_phase1 §2）
- 表2 規模を振った計測（`data/atlas/scaling.csv`、findings_phase2 §1）
- 表3 厳密最適の基準線（`data/atlas/baselines.csv`、findings_phase3 §1）

**推定で埋めない。** 基準線が届かないサイズは空欄のままにする。
"""

from __future__ import annotations

import csv
import statistics
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
OUT = Path.home() / "dev/overleaf/2026_resource_atlas_letter/tables"
HEAD = "% 自動生成（scripts/gen_atlas_tables.py）。手編集しないこと。\n"

#: 表2・表3 に出す族の表示名（`_` は LaTeX 用にエスケープする）
DISPLAY = {
    "fib_pairs_2017": "fib_pairs",
    "cutrod_linear": "cutrod_linear",
}
#: 表1 の区分の並び（本数の多い順ではなく、性格の近いものを隣に置く）
CATEGORY_ORDER = ["algorithm", "memoization", "injective", "structs", "jana"]
#: 区分の表示名。本文の言い方（「単射関数の実装」「構造体の操作」）とそろえる
CATEGORY_JA = {
    "algorithm": "アルゴリズム",
    "memoization": "メモ化",
    "injective": "単射関数",
    "structs": "構造体",
    "jana": "jana",
}


def rows(name: str) -> list[dict[str, str]]:
    with (REPO / "data" / "atlas" / name).open() as fh:
        return list(csv.DictReader(fh))


def tex_name(family: str) -> str:
    return DISPLAY.get(family, family).replace("_", r"\_")


def table(spec: str, header: str, body: list[str]) -> str:
    lines = [
        HEAD.rstrip("\n"),
        rf"\begin{{tabular}}{{{spec}}}",
        r"\toprule",
        header,
        r"\midrule",
        *body,
        r"\bottomrule",
        r"\end{tabular}",
        "",
    ]
    return "\n".join(lines)


def category_table() -> str:
    """表1: 区分ごとの本数・steps 中央値・スタックを使う本数・終端ビット中央値。"""
    by: dict[str, list[dict[str, str]]] = defaultdict(list)
    for r in rows("atlas.csv"):
        by[r["category"]].append(r)

    body = []
    for cat in CATEGORY_ORDER + sorted(set(by) - set(CATEGORY_ORDER)):
        rs = by.get(cat)
        if not rs:
            continue
        steps = statistics.median(int(r["steps"]) for r in rs)
        bits = statistics.median(int(r["final_live_bits"]) for r in rs)
        uses = sum(1 for r in rs if int(r["stack_peak"]) > 0)
        body.append(
            f"{CATEGORY_JA.get(cat, cat)} & {len(rs)} & {steps:g} & "
            f"{uses}/{len(rs)} & {bits:g}" + r" \\"
        )
    header = (
        r"区分 & 本数 & steps 中央値 & スタックを使う本数 & "
        r"$\mathit{final\_live\_bits}$ 中央値 \\"
    )
    return table("l r r r r", header, body)


def scaling_table() -> str:
    """表2: 族ごとの steps 実測列・隣接比（初と末）・stack\\_peak（初と末）。

    当てはめはしない（`docs/81` §3 Phase 2 の規約）。報告は実測値と比のみ。
    """
    by: dict[str, list[dict[str, str]]] = defaultdict(list)
    for r in rows("scaling.csv"):
        if r["error"]:
            continue
        by[r["family"]].append(r)

    body = []
    for family, rs in by.items():
        rs = sorted(rs, key=lambda r: int(r["n"]))
        steps = [int(r["steps"]) for r in rs]
        stack = [int(r["stack_peak"]) for r in rs]
        ratios = [b / a for a, b in zip(steps, steps[1:])]
        series = ", ".join(str(s) for s in steps)
        ratio = rf"{ratios[0]:.2f} $\to$ {ratios[-1]:.2f}"
        peak = "0" if set(stack) == {0} else rf"{stack[0]} $\to$ {stack[-1]}"
        body.append(f"{tex_name(family)} & {series} & {ratio} & {peak}" + r" \\")
    header = r"族 & steps（6 点） & 隣接比（初 $\to$ 末） & $\mathit{stack\_peak}$ \\"
    return table("l l c c", header, body)


def baseline_table() -> str:
    """表3: 族ごとに基準線が届いた最大サイズの 1 行。

    モデル対応が無効な族（実装のピーク $<$ \\pmin）には $\\dagger$ を付け、最後に置く。
    行は残す（`docs/82` §6 の限界の明示）。
    """
    by: dict[str, list[dict[str, str]]] = defaultdict(list)
    for r in rows("baselines.csv"):
        if r["mstar"]:
            by[r["family"]].append(r)

    valid, invalid = [], []
    for family, rs in by.items():
        r = max(rs, key=lambda r: int(r["n"]))
        broken = int(r["impl_peak"]) < int(r["p_min"])
        name = tex_name(family) + (r" $\dagger$" if broken else "")
        line = (
            f"{name} & {r['n']} & {r['dag_N']} & {r['floor']} & {r['mstar']} & "
            f"{r['p_min']} & {r['impl_moves']} & {r['impl_peak']}" + r" \\"
        )
        (invalid if broken else valid).append(line)

    header = (
        r"族 & $n$ & $N$ & 床 $2N-1$ & $M^{*}$ & $p_{\min}$ & "
        r"実装の手数 & 実装のピーク \\"
    )
    return table("l r r r r r r r", header, valid + invalid)


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    for name, text in [
        ("category.tex", category_table()),
        ("scaling.tex", scaling_table()),
        ("baselines.tex", baseline_table()),
    ]:
        (OUT / name).write_text(text)
        print(f"生成: {OUT.relative_to(Path.home())}/{name}（{len(text.splitlines())} 行）")


if __name__ == "__main__":
    main()
