"""最適スケジュールの構造分析（候補1・タスク1）。

`data/exp01_findings.md` §4 で「ピラミッドの $M^*$ が $h=5$ で当てはめ崩壊」した原因を
特定するため、$h=4,5$ の最適スケジュールを抽出して次を測る。

  - **再計算多重度** $\\mathrm{mult}(v)$ = 頂点 $v$ のトグル回数 / 2 の切り上げ
    （put の回数。1 なら再計算なし）。レベル別に集計する。
  - **ピーク占有の時系列**（何手のあいだ上限に張り付いているか = 飽和率）。
  - **飽和直線スイープ**（先行プロジェクト `notes/optimal-schedules.md` の構造知見）の検出:
    連続する put の最長ラン。

出力: `data/exp01b_schedules.md`（自動生成・手編集禁止）

実行: python3 scripts/exp01b_schedule.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import revpebble as rp  # noqa: E402
from exp01b_engine import all_pebbled, mstar, pmin, schedule, verify_schedule  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "exp01b_schedules.md"


def pyramid_levels(h: int) -> list[list[int]]:
    """pyramid(h) のレベル分け（levels[0] = 底辺）。revpebble.pyramid と同じ番号付け。"""
    levels: list[list[int]] = []
    counter = 0
    for lv in range(h + 1, 0, -1):
        levels.append(list(range(counter, counter + lv)))
        counter += lv
    return levels


def cbt_levels(h: int) -> list[list[int]]:
    """complete_binary_tree(h) のレベル分け（levels[0] = 葉）。"""
    levels: list[list[int]] = []
    counter = 0
    for lv in range(h, -1, -1):
        levels.append(list(range(counter, counter + 2**lv)))
        counter += 2**lv
    return levels


def analyze(seq: list[tuple[str, int]], levels: list[list[int]], p: int) -> dict:
    """スケジュールの構造指標を計算する。"""
    n = sum(len(x) for x in levels)
    toggles = [0] * n
    for _, v in seq:
        toggles[v] += 1
    puts = [t // 2 + (t % 2) for t in toggles]  # put 回数

    # ピーク占有の時系列
    occ: list[int] = []
    cur = 0
    for kind, _ in seq:
        cur += 1 if kind == "put" else -1
        occ.append(cur)
    saturated = sum(1 for x in occ if x == p)

    # 連続 put の最長ラン
    best = run = 0
    for kind, _ in seq:
        run = run + 1 if kind == "put" else 0
        best = max(best, run)

    lvl_of = {v: i for i, lv in enumerate(levels) for v in lv}
    per_level: list[dict] = []
    for i, lv in enumerate(levels):
        per_level.append(
            {
                "level": i,
                "size": len(lv),
                "toggles": sum(toggles[v] for v in lv),
                "puts": sum(puts[v] for v in lv),
                "max_puts": max(puts[v] for v in lv),
            }
        )
    return {
        "moves": len(seq),
        "vertices": n,
        "toggles": toggles,
        "puts": puts,
        "max_puts": max(puts),
        "total_puts": sum(puts),
        "saturated_moves": saturated,
        "saturation_ratio": saturated / len(seq),
        "longest_put_run": best,
        "per_level": per_level,
        "lvl_of": lvl_of,
    }


def render_triangle(levels: list[list[int]], puts: list[int]) -> str:
    """ピラミッド/木の形に put 回数を並べる（再計算の偏りを目で見る）。"""
    width = max(len(str(max(puts))), 1)
    lines = []
    for i in range(len(levels) - 1, -1, -1):
        row = " ".join(f"{puts[v]:>{width}}" for v in levels[i])
        pad = " " * ((len(levels[0]) - len(levels[i])) * (width + 1) // 2)
        lines.append(f"L{i:<2}{pad}{row}")
    return "\n".join(lines)


def report(g, levels, p: int, note: str = "") -> str:
    t = g.n - 1
    m = mstar(g, t, p)
    if m is None:
        return f"### {g.name}, p={p}: 到達不能\n"
    seq = schedule(g, t, p)
    assert seq is not None and len(seq) == m
    verify_schedule(g, t, p, seq)
    a = analyze(seq, levels, p)
    out = [f"### {g.name}, p={p}: $M^*$={m}{note}\n"]
    out.append(
        f"- 頂点数 {a['vertices']}、総 put {a['total_puts']}（= 平均 "
        f"{a['total_puts']/a['vertices']:.2f} 回/頂点）、最大 put {a['max_puts']} 回\n"
        f"- ピーク {p} に張り付いていた手数: {a['saturated_moves']}/{m} "
        f"（{a['saturation_ratio']*100:.0f}%）\n"
        f"- 連続 put の最長ラン: {a['longest_put_run']}\n"
    )
    out.append("\nレベル別（L0 = 底辺/葉、最上段 = 終端）:\n")
    out.append("| level | 頂点数 | toggles | puts | 1頂点の最大 puts |")
    out.append("|---|---|---|---|---|")
    for r in a["per_level"]:
        out.append(
            f"| L{r['level']} | {r['size']} | {r['toggles']} | {r['puts']} | {r['max_puts']} |"
        )
    out.append("\n頂点ごとの put 回数（配置図）:\n")
    out.append("```")
    out.append(render_triangle(levels, a["puts"]))
    out.append("```\n")
    return "\n".join(out)


def main() -> None:
    chunks: list[str] = [
        "# exp01b — 最適スケジュールの構造分析（自動生成・手編集禁止）\n",
        "生成: `python3 scripts/exp01b_schedule.py`。"
        "目的は `data/exp01_findings.md` §4 の「$h=5$ での当てはめ崩壊」の原因特定。\n",
        "## ピラミッド（all-pebbled 流儀）\n",
    ]
    for h in (3, 4, 5):
        g = all_pebbled(rp.pyramid(h))
        lv = pyramid_levels(h)
        p0 = pmin(g, g.n - 1)
        assert p0 is not None
        for k in (0, 1):
            note = "（= $p_{\\min}$）" if k == 0 else ""
            chunks.append(report(g, lv, p0 + k, note))

    chunks.append("## 完全二分木（all-pebbled 流儀）\n")
    for h in (2, 3, 4):
        g = all_pebbled(rp.complete_binary_tree(h))
        lv = cbt_levels(h)
        p0 = pmin(g, g.n - 1)
        assert p0 is not None
        chunks.append(report(g, lv, p0, "（= $p_{\\min}$）"))

    OUT.write_text("\n".join(chunks))
    print(f"→ {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
