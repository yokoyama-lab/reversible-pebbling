"""QRE 向けの図: 完全二分木で「時間最適 vs 空間最適」が指数的に離れることを 1 枚で示す。

    .venv/bin/python scripts/gen_qre_figure.py [出力ディレクトリ]

既定の出力先は `data/figs/`（`fig_time_vs_space.pdf` / `.png` / `.svg`）。
科研費調書（`~/dev/uni/kakenhi/2027_kiban_b/骨子.md`）と arXiv 原稿
（`docs/43_qre_abstract.md`）の両方で使う。

系列の出どころ（**手打ち禁止・すべて既存の実測と定理から**）:

* 時間最適 = `3*2^(D-1)+1`（D = h-1）。R-Q2-08 / Lean `tree_pmin_exact`。
  **両側とも一般の D で機械証明済み**（`lean/Revgarbage/ParPebbleWindow.lean`）。
* 空間最適 = 素の CNF で T を伸ばして測った最小ピーク。
  `data/q2_parallel_findings.md` の表（h=2..5 が厳密、h=9 は約 12）。
* 傾向線 = `h+2`。Královič 2004 Thm 4.9 の `h + Θ(lg* h)` の形と整合。
  **定理ではないので破線で描き、凡例にも trend と書く。**

軸ラベルは英語（和文フォントを図に埋め込まない）。説明はキャプションで行う。
系列そのものの正しさは `tests/test_gen_qre_figure.py` が固定する。
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import NamedTuple

REPO = Path(__file__).resolve().parents[1]
DEFAULT_OUT = REPO / "data" / "figs"

#: 図に描く高さの範囲（h=12 で |V|=4095）。h=2 は定理の範囲外なので入れない。
HEIGHTS = tuple(range(3, 13))

#: 並列モデルで自前に測った空間最適（`data/q2_parallel_findings.md`）。
#: 値と「厳密か」の対。h=9 の 12 は findings が「約 12」と書いているので厳密ではない。
QUBIT_MINIMAL_MEASURED: dict[int, tuple[int, bool]] = {
    2: (3, True),
    3: (5, True),
    4: (6, True),
    5: (7, True),
    9: (12, False),
}


def depth_optimal_peak(h: int) -> int:
    """完全二分木（高さ h）の時間最適な並列可逆ペブリングの最小ピーク。

    p_min = 3*2^(D-1) + 1 で D = h-1。**D >= 2 すなわち h >= 3 が境界**
    （変異注入が hD を 3<=D から 2<=D へ改良し、1<=D では落ちることを示した）。
    h=2 の実測は 3 で、式の 4 とは一致しない。
    """
    if h < 3:
        raise ValueError(f"定理は D>=2 すなわち h>=3 でのみ成立する（与えられた h={h}）")
    D = h - 1
    return 3 * 2 ** (D - 1) + 1


def qubit_minimal_trend(h: int) -> int:
    """空間最適の傾向線 h+2。**定理ではない**（Královič は h + Θ(lg* h)）。"""
    return h + 2


class Series(NamedTuple):
    heights: list[int]
    depth_optimal: list[int]
    trend: list[int]
    measured_exact: list[tuple[int, int]]
    measured_approx: list[tuple[int, int]]


def series() -> Series:
    # 図は定理の範囲（h>=3）に揃える。h=2 は p_min=3 で式の 4 と合わない
    # （D>=2 が境界）ので描かない。値そのものは辞書に残してテストが固定する。
    items = sorted((h, v, ok) for h, (v, ok) in QUBIT_MINIMAL_MEASURED.items() if h >= HEIGHTS[0])
    exact = [(h, v) for h, v, ok in items if ok]
    approx = [(h, v) for h, v, ok in items if not ok]
    return Series(
        heights=list(HEIGHTS),
        depth_optimal=[depth_optimal_peak(h) for h in HEIGHTS],
        trend=[qubit_minimal_trend(h) for h in HEIGHTS],
        measured_exact=exact,
        measured_approx=approx,
    )


def render(out_dir: Path) -> list[Path]:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    s = series()
    out_dir.mkdir(parents=True, exist_ok=True)

    fig, ax = plt.subplots(figsize=(6.0, 4.0))

    ax.plot(
        s.heights, s.depth_optimal,
        "-o", color="#d62728", markersize=4.5, linewidth=1.8,
        label=r"depth-optimal: $3\cdot 2^{D-1}+1$  (theorem, machine-checked)",
    )
    ax.plot(
        s.heights, s.trend,
        "--", color="#1f77b4", linewidth=1.4,
        label=r"qubit-minimal: $\Theta(D)$  (trend $h{+}2$; Královič 2004)",
    )
    ax.plot(
        [h for h, _ in s.measured_exact], [v for _, v in s.measured_exact],
        "s", color="#1f77b4", markersize=5.5, label="qubit-minimal, exact (SAT)",
    )
    ax.plot(
        [h for h, _ in s.measured_approx], [v for _, v in s.measured_approx],
        "o", markerfacecolor="none", markeredgecolor="#1f77b4",
        markersize=6.5, label="qubit-minimal, approximate",
    )

    ax.annotate(
        f"{s.depth_optimal[s.heights.index(9)]} vs 12\n"
        r"($\approx 32\times$, $|V|=511$)",
        xy=(9, depth_optimal_peak(9)), xytext=(9.15, 62),
        fontsize=8.5, color="#555555",
        arrowprops=dict(arrowstyle="->", color="#999999", lw=0.9),
    )

    ax.set_yscale("log")
    ax.set_xlabel("height $h$ of the complete binary tree   ($D = h-1$)")
    ax.set_ylabel("ancilla qubits (peak pebbles)")
    ax.set_xticks(list(HEIGHTS))
    ax.set_xlim(HEIGHTS[0] - 0.4, HEIGHTS[-1] + 0.4)
    ax.grid(True, which="both", linewidth=0.4, alpha=0.35)
    ax.legend(fontsize=7.6, loc="upper left", framealpha=0.95)
    fig.tight_layout()

    written = []
    for ext in ("pdf", "png", "svg"):
        p = out_dir / f"fig_time_vs_space.{ext}"
        fig.savefig(p, dpi=200)
        written.append(p)
    plt.close(fig)
    return written


def main() -> None:
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_OUT
    s = series()
    print("h    depth-optimal   qubit-minimal(trend)   measured")
    for i, h in enumerate(s.heights):
        m = QUBIT_MINIMAL_MEASURED.get(h)
        tag = "" if m is None else f"{m[0]}{'' if m[1] else ' (approx)'}"
        print(f"{h:<5}{s.depth_optimal[i]:<16}{s.trend[i]:<23}{tag}")
    for p in render(out):
        print(f"wrote {p}")


if __name__ == "__main__":
    main()
