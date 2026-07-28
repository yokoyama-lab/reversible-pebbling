"""論文の表を CSV から自動生成する（**手打ち禁止**の規約に従う）。

出力先は Overleaf 側のプロジェクト（`~/dev/overleaf/2026_erasure_pebbling/tables/`）。
`main.tex` 側は tables/ 以下を input で取り込む。

    python3 scripts/gen_tables.py
"""

from __future__ import annotations

import csv
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
OUT = Path.home() / "dev/overleaf/2026_erasure_pebbling/tables"
HEAD = "% 自動生成（scripts/gen_tables.py）。手編集しないこと。\n"


def rows(name: str) -> list[dict]:
    with (REPO / "data" / name).open() as fh:
        return list(csv.DictReader(fh))


def surface() -> str:
    """M*(n, p_min, e) の表（ops 変種）。e = 0..6。"""
    data = defaultdict(dict)
    for r in rows("exp03_surface_ops.csv"):
        if r["mode"] != "ops" or r["p"] != r["p_min"]:
            continue
        try:
            data[int(r["n"])][int(r["e"])] = int(r["mstar"])
        except ValueError:
            continue
    es = list(range(7))
    lines = [HEAD, r"\begin{tabular}{r r" + " r" * len(es) + r" r}", r"\toprule"]
    lines.append(
        r"$n$ & $p_{\min}$ & " + " & ".join(f"$e{{=}}{e}$" for e in es)
        + r" & $2n-1$ \\"
    )
    lines.append(r"\midrule")
    pmin = {int(r["n"]): int(r["p_min"]) for r in rows("exp03_surface_ops.csv")}
    for n in sorted(data):
        if n % 2 or n < 4 or n > 20:
            continue
        cells = [str(data[n].get(e, "")) for e in es]
        lines.append(f"{n} & {pmin.get(n,'')} & " + " & ".join(cells) + rf" & {2*n-1} \\")
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    return "\n".join(lines)


def esat() -> str:
    """飽和点 e* と公式の照合。"""
    lines = [HEAD, r"\begin{tabular}{r r r r c}", r"\toprule"]
    lines.append(
        r"$n$ & $p$ & $e^*$ (measured) & $\lceil (n-1)/(p-1)\rceil-1$ & agrees \\"
    )
    lines.append(r"\midrule")
    seen = 0
    for r in rows("exp03_esat.csv"):
        try:
            n, p = int(r["n"]), int(r["p"])
        except ValueError:
            continue
        # p_min 行だけに絞る。n の絞り込みはしない（以前 n を固定して
        # n=16,20 が落ちるという生成不具合を出したため。docs/STATUS.md の方針どおり
        # 「表は生成物を通す」を徹底する）
        if p != int(r["p_min"]) or n < 4 or n > 24 or n % 2:
            continue
        ok = r.get("match", "").strip().lower() in ("true", "1", "yes")
        lines.append(
            f"{n} & {p} & {r['e_star']} & {r['formula']} & "
            + (r"\checkmark" if ok else "?")
            + r" \\"
        )
        seen += 1
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    return "\n".join(lines) if seen else ""


def reach() -> str:
    """到達則: 実測 vs 我々の式 vs LTV Lemma 1。"""
    lines = [HEAD, r"\begin{tabular}{r r r r r}", r"\toprule"]
    lines.append(
        r"$p$ & $e$ & $\reach(p,e)$ & $(e+2)2^{p-2}$ & LTV $(e+1)2^{p-2}$ \\"
    )
    lines.append(r"\midrule")
    for r in rows("exp03_reach.csv"):
        try:
            p, e = int(r["p"]), int(r["e"])
        except ValueError:
            continue
        if p > 6 or e > 3:
            continue
        ltv = r.get("ltv_lemma1_lb") or (e + 1) * 2 ** (p - 2)
        lines.append(f"{p} & {e} & {r['reach']} & {r['formula']} & {ltv}" + r" \\")
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    return "\n".join(lines)


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    for name, text in [
        ("surface.tex", surface()),
        ("esat.tex", esat()),
        ("reach.tex", reach()),
    ]:
        if not text:
            print(f"（{name} は生成できるデータが無い）")
            continue
        (OUT / name).write_text(text)
        print(f"生成: {OUT.relative_to(Path.home())}/{name}（{len(text.splitlines())} 行）")


if __name__ == "__main__":
    main()
