"""論文の表を CSV から自動生成する（**手打ち禁止**の規約に従う）。

出力先は Overleaf 側のプロジェクト（`~/dev/overleaf/2026_erasure_pebbling/tables/`）。
`main.tex` 側は tables/ 以下を input で取り込む。

    python3 scripts/gen_tables.py               # Overleaf へ
    python3 scripts/gen_tables.py --out tables  # リポ内の tables/ へ
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


NA = "n/a"


def ours_lb(p: int, e: int) -> int | None:
    """定理 B1: reach(p,e) >= (e+2)2^{p-2}。主張は p >= 2 のみ。"""
    return (e + 2) * 2 ** (p - 2) if p >= 2 else None


def ltv_lb(p: int, e: int) -> int | None:
    """LTV Lemma 1（本文 Prop. ltv）: reach(p,e) >= (e+1)2^{p-2}。主張は p >= 2 かつ e >= 1 のみ。

    以前は data/exp03_reach.csv の ltv_lemma1_lb 列（2^{max(p-2,0)} で p=1 を丸めた値）を
    そのまま印字し、p=1 で厳密値 1 を上回る偽の保証 2,3,4 を出していた（査読 09-18 必須 1・2）。
    """
    return (e + 1) * 2 ** (p - 2) if p >= 2 and e >= 1 else None


def reach(data: list[dict] | None = None) -> str:
    """到達則: 実測 vs 我々の式 vs LTV Lemma 1。適用範囲外のセルは n/a。

    下界の列が厳密値を超えたら、あるいは CSV の formula 列が閉形式と食い違ったら止める。
    """
    if data is None:
        data = rows("exp03_reach.csv")
    lines = [HEAD, r"\begin{tabular}{r r r r r}", r"\toprule"]
    lines.append(
        r"$p$ & $e$ & $\reach(p,e)$ & $(e+2)2^{p-2}$ & LTV $(e+1)2^{p-2}$ \\"
    )
    lines.append(r"\midrule")
    for r in data:
        try:
            p, e = int(r["p"]), int(r["e"])
        except ValueError:
            continue
        if p > 6 or e > 3:
            continue
        exact = int(r["reach"])
        ours, ltv = ours_lb(p, e), ltv_lb(p, e)
        if ours is not None and int(r["formula"]) != ours:
            raise ValueError(f"CSV の formula 列が (e+2)2^(p-2) と食い違う: p={p} e={e} {r['formula']} != {ours}")
        for name, lb in (("定理 B1", ours), ("LTV", ltv)):
            if lb is not None and lb > exact:
                raise AssertionError(f"{name} の下界 {lb} が厳密値 reach({p},{e})={exact} を超える")
        cells = [str(exact)] + [NA if v is None else str(v) for v in (ours, ltv)]
        lines.append(f"{p} & {e} & " + " & ".join(cells) + r" \\")
    lines += [r"\bottomrule", r"\end{tabular}", ""]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> None:
    import argparse

    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, default=OUT, help=f"出力先（既定: {OUT}）")
    out = ap.parse_args(argv).out
    out.mkdir(parents=True, exist_ok=True)
    for name, text in [
        ("surface.tex", surface()),
        ("esat.tex", esat()),
        ("reach.tex", reach()),
    ]:
        if not text:
            print(f"（{name} は生成できるデータが無い）")
            continue
        (out / name).write_text(text)
        print(f"生成: {out}/{name}（{len(text.splitlines())} 行）")


if __name__ == "__main__":
    main()
