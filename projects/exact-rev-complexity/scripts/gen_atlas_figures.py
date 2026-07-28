"""JSSST レターの図 1・図 2 を CSV から生成する（**手描き禁止**、表と同じ規約）。

出力先は Overleaf 側（`~/dev/overleaf/2026_resource_atlas_letter/figs/`）。

    .venv/bin/python scripts/gen_atlas_figures.py

- 図 1 `fig1_stack_vs_steps.pdf` — steps × stack_peak の散布（111 点、区分ごとに印を変える）
- 図 2 `fig2_ratios.pdf` — 9 族の隣接比の推移（成長の 3 群が分かれることを示す）

軸ラベルは英語にする（和文フォントを図に埋め込まないため。説明は本文のキャプションで行う）。
描画には matplotlib を使うので、リポジトリ内の `.venv` から実行すること
（エージェント指示の既定「標準ライブラリのみ」とは別枠。CLAUDE.md の注記どおり）。
系列そのものの正しさは `tests/test_gen_atlas_figures.py` が固定する。
"""

from __future__ import annotations

import csv
from collections import defaultdict
from pathlib import Path
from typing import NamedTuple

REPO = Path(__file__).resolve().parents[1]
OUT = Path.home() / "dev/overleaf/2026_resource_atlas_letter/figs"

#: 区分ごとの印と色（灰色印刷でも区別できるよう印を変える）
STYLE = {
    "algorithm": ("o", "#1f77b4"),
    "memoization": ("s", "#d62728"),
    "injective": ("^", "#2ca02c"),
    "structs": ("v", "#9467bd"),
    "jana": ("D", "#ff7f0e"),
}
#: 図 2 で線種を分ける成長の 3 群（末端の隣接比で決まる。テストが境界を検査する）
GROUPS = {
    "linear": ("-", "#1f77b4"),
    "polynomial": ("--", "#2ca02c"),
    "fast": (":", "#d62728"),
}


class Point(NamedTuple):
    name: str
    category: str
    steps: int
    stack: int


def rows(name: str) -> list[dict[str, str]]:
    with (REPO / "data" / "atlas" / name).open() as fh:
        return list(csv.DictReader(fh))


def scatter_points() -> list[Point]:
    """図 1 の系列。111 本すべて（stack が 0 のものも落とさない）。"""
    return [
        Point(r["name"], r["category"], int(r["steps"]), int(r["stack_peak"]))
        for r in rows("atlas.csv")
    ]


def ratio_series() -> dict[str, list[float]]:
    """図 2 の系列。族ごとに steps の隣接比（6 点なら 5 つ）。"""
    by: dict[str, list[tuple[int, int]]] = defaultdict(list)
    for r in rows("scaling.csv"):
        if r["error"]:
            continue
        by[r["family"]].append((int(r["n"]), int(r["steps"])))
    out = {}
    for family, pairs in by.items():
        steps = [s for _, s in sorted(pairs)]
        out[family] = [b / a for a, b in zip(steps, steps[1:])]
    return out


def group_of(ratios: list[float]) -> str:
    last = ratios[-1]
    if last < 1.2:
        return "linear"
    if last >= 2.0:
        return "fast"
    return "polynomial"


def render() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    OUT.mkdir(parents=True, exist_ok=True)

    # --- 図 1 -----------------------------------------------------------------
    fig, ax = plt.subplots(figsize=(5.2, 3.4))
    pts = scatter_points()
    for cat, (marker, color) in STYLE.items():
        sel = [p for p in pts if p.category == cat]
        ax.scatter(
            [p.steps for p in sel], [p.stack for p in sel],
            marker=marker, c=color, s=22, alpha=0.75, linewidths=0,
            label=f"{cat} ({len(sel)})",
        )
    ax.set_xscale("log")
    ax.set_yscale("symlog", linthresh=1)  # stack = 0 の 75 本を落とさない
    ax.set_ylim(-0.35, 600)  # symlog の負側は使わない（0 の帯だけ見せる）
    ax.set_xlabel("steps")
    ax.set_ylabel("stack peak")
    ax.axhline(0.5, color="gray", lw=0.6, ls="--")
    ax.text(5, 0.55, "stack unused (75 programs)", fontsize=7, color="gray")
    ax.legend(fontsize=7, loc="upper left", framealpha=0.9)
    ax.grid(True, which="major", lw=0.3, alpha=0.4)
    fig.tight_layout()
    fig.savefig(OUT / "fig1_stack_vs_steps.pdf")
    plt.close(fig)

    # --- 図 2 -----------------------------------------------------------------
    fig, ax = plt.subplots(figsize=(5.2, 3.4))
    for family, ratios in sorted(ratio_series().items(), key=lambda kv: -kv[1][-1]):
        style, color = GROUPS[group_of(ratios)]
        ax.plot(
            range(1, len(ratios) + 1), ratios,
            style, color=color, marker="o", ms=3, lw=1.1,
            label=family.replace("_", " "),
        )
    ax.axhline(1.0, color="gray", lw=0.6)
    ax.set_ylim(0.9, 4.9)  # 凡例の場所を空ける
    ax.set_xlabel("index of adjacent pair (small to large input)")
    ax.set_ylabel("ratio of consecutive steps")
    ax.set_xticks(range(1, 6))
    ax.legend(fontsize=7, ncol=2, loc="upper right", framealpha=0.95)
    ax.grid(True, lw=0.3, alpha=0.4)
    fig.tight_layout()
    fig.savefig(OUT / "fig2_ratios.pdf")
    plt.close(fig)

    for name in ("fig1_stack_vs_steps.pdf", "fig2_ratios.pdf"):
        print(f"生成: {(OUT / name).relative_to(Path.home())}")


if __name__ == "__main__":
    render()
