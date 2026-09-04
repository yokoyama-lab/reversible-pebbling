"""$M^*(T_7)$ の上界と下界（厳密値は探索が届かない）。

$p_{\\min}(T_7)=10$ は確定済み（`data/exp01b_certificate.md`）。手数 $M^*(T_7,10)$ は
商グラフの状態数が 2^27 個の shape id を超えてしまい**確定できていない**。
そこで上下から挟む。**上界を $M^*$ として書いてはいけない。**

## 上界（構成的・検証器を通す）

位相ごとにペブル予算が違うことを使う（`treedp.compose_asymmetric`）。全体ピーク $P=10$:

| 位相 | 盤上の他の駒 | 部分木の許容ピーク | 使う手順 |
|---|---|---|---|
| $A$ を作る | なし | 10 | $M^*(T_6,10)=295$ |
| $B$ を作る | $a$ | 9 | $M^*(T_6,9)=339$ |
| 根を置く | $a,b$ | — | 1 |
| $B$ を片付ける | $a$, 根 | 8 | $M^*(T_6,8)=429$ |
| $A$ を片付ける | 根 | 9 | $M^*(T_6,9)=339$ |

合計 $295+339+1+429+339 = 1403$。従来の対称合成（4 位相すべて 429）は 1717 だった。

## 下界

任意の手順を部分木 $A$／$B$／根 の手に分解する（互いに素で全体を覆う）。
$A$ の制限手順は $\\varnothing \\to (a を含む配置) \\to \\varnothing$ を辿るので長さ
$\\ge 2g_5(10)$（状態グラフが無向なので往復は同距離）。根のトグルは $\\ge1$ 回。よって

$$M^*(T_7,10) \\;\\ge\\; 4\\,g_5(10) + 1 .$$

出力: `data/exp01b_bounds_t7.md`（自動生成・手編集禁止）

実行: python3 scripts/exp01b_bounds_t7.py [--cap 25000000]
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import revpebble as rp  # noqa: E402
from exp01b_engine import verify_schedule  # noqa: E402
from exp01b_lb_refine import (  # noqa: E402
    g_by_count,
    old_bound_from,
    refined_bound,
)
from treedp import (  # noqa: E402
    compose_asymmetric,
    first_root_pebbled_depth,
    realize_optimal,
)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "exp01b_bounds_t7.md"

# 既に確定済み（tests/test_exp01c_treedp.py::TRADEOFF に固定）
MSTAR_T6 = {8: 429, 9: 339, 10: 295}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cap", type=int, default=25_000_000, help="訪問状態数の上限（メモリ保護）")
    args = ap.parse_args()

    lines = [
        "# exp01b — $M^*(T_7,10)$ の上界と下界（自動生成・手編集禁止）\n",
        "生成: `python3 scripts/exp01b_bounds_t7.py`\n",
        "$T_h$ は free-leaves 流儀（$= $ Královič の $Bt(h)$）。",
        "$p_{\\min}(T_7)=10$ は確定済み。**$M^*(T_7)$ の厳密値は未確定。**\n",
    ]

    # ---- 上界 --------------------------------------------------------------
    P = 10
    print("上界の構成中…", flush=True)
    t0 = time.time()
    parts: dict[int, list[tuple[str, int]]] = {}
    for p in (P, P - 1, P - 2):
        t1 = time.time()
        try:
            seq = realize_optimal(6, p, cap=args.cap)
        except RuntimeError as exc:
            lines.append(f"- 上界: $T_6$ の $p={p}$ の手順を復元できず（{exc}）")
            seq = None
        assert seq is not None, f"T_6 の p={p} の手順が復元できない"
        assert len(seq) == MSTAR_T6[p], (p, len(seq), MSTAR_T6[p])
        g6 = rp.complete_binary_tree(6)
        verify_schedule(g6, g6.n - 1, p, seq)  # 部分木の手順自体も検証
        parts[p] = seq
        print(f"  T_6 p={p}: {len(seq)} 手 ({time.time()-t1:.1f}s)", flush=True)

    upper = compose_asymmetric(
        7,
        build_a=parts[P],
        build_b=parts[P - 1],
        clear_b=parts[P - 2],
        clear_a=parts[P - 1],
    )
    peak = cur = 0
    for kind, _ in upper:
        cur += 1 if kind == "put" else -1
        peak = max(peak, cur)
    g7 = rp.complete_binary_tree(7)
    verify_schedule(g7, g7.n - 1, P, upper)  # ← 上界の証書
    ub = len(upper)
    print(f"上界: {ub} 手・ピーク {peak}（検証 OK, {time.time()-t0:.1f}s）", flush=True)

    # 従来の対称合成との比較
    sym = compose_asymmetric(
        7,
        build_a=parts[P - 2],
        build_b=parts[P - 2],
        clear_b=parts[P - 2],
        clear_a=parts[P - 2],
    )
    verify_schedule(g7, g7.n - 1, P, sym)

    lines.append("## 上界（構成的・独立な検証器を通済み）\n")
    lines.append("| 位相 | 盤上の他の駒 | 部分木の許容ピーク | $T_6$ の手数 |")
    lines.append("|---|---|---|---|")
    lines.append(f"| $A$ を作る | なし | {P} | {len(parts[P])} |")
    lines.append(f"| $B$ を作る | $a$ | {P-1} | {len(parts[P-1])} |")
    lines.append("| 根を置く | $a,b$ | — | 1 |")
    lines.append(f"| $B$ を片付ける | $a$, 根 | {P-2} | {len(parts[P-2])} |")
    lines.append(f"| $A$ を片付ける | 根 | {P-1} | {len(parts[P-1])} |")
    lines.append("")
    lines.append(
        f"→ **$M^*(T_7,10) \\le {ub}$**（実際のピークは {peak}）。"
        f"従来の対称合成は {len(sym)} 手だったので {len(sym)-ub} 手改善。"
    )

    # ---- 下界 --------------------------------------------------------------
    print("下界の計算中（g_5(10), g_5(9)）…", flush=True)
    t0 = time.time()
    gs: dict[int, int | None] = {}
    for q in (P, P - 1):
        try:
            gs[q] = first_root_pebbled_depth(5, q, cap=args.cap)
        except RuntimeError as exc:
            print(f"  g_5({q}): 到達できず（{exc}）", flush=True)
            gs[q] = None
        print(f"  g_5({q}) = {gs[q]} ({time.time()-t0:.1f}s)", flush=True)

    g10, g9 = gs.get(P), gs.get(P - 1)
    lines.append("\n## 下界\n")
    if g10 is None:
        lines.append("到達できなかった。")
    else:
        lines.append(
            f"$g_m(p)$ = $\\varnothing$ から「高さ $m$ の木の根がペブル済みの**何らかの**"
            f"配置」への最小手数（clean である必要はない）。実測 $g_5(10)={g10}$"
            + (f"、$g_5(9)={g9}$" if g9 is not None else "")
            + "。"
        )
        lb_simple = 4 * g10 + 1
        lines.append("")
        lines.append(
            f"**素朴な分解**: 手順を部分木 $A$／$B$／根 に分けると各部分木は"
            f"$\\varnothing\\to(a を含む配置)\\to\\varnothing$ を辿るので"
            f"$M^* \\ge 4g_5(10)+1 = {lb_simple}$。"
        )
        lb = lb_simple
        if g9 is not None:
            lb_phased = 2 * (g10 + g9) + 1
            lines.append("")
            lines.append(
                f"**位相を分けた改良**: 根が最後に置かれた時刻 $t^*$ 以降は"
                f"根が 1 本占めるので、各部分木の復路はピーク $9$ で走る。よって"
                f"$M^* \\ge 2(g_5(10)+g_5(9))+1 = 2({g10}+{g9})+1 = {lb_phased}$。"
            )
            lb = max(lb, lb_phased)

        # ---- 駒数の結合制約で締めた版（2026-09-04 追加）--------------------
        print("下界の計算中（駒数の結合制約）…", flush=True)
        t1 = time.time()
        try:
            lb_joint, info = refined_bound(7, P, cap=args.cap)
        except RuntimeError as exc:
            print(f"  打ち切り（{exc}）", flush=True)
            lb_joint, info = None, None
        if lb_joint is not None:
            x, y = info["arg"]
            gP, gQ = info["gP"], info["gQ"]
            prev = old_bound_from(gP, gQ)
            lines.append("")
            lines.append(
                "**駒数の結合制約（2026-09-04）**: 上の 2 つは部分木 $A$ と $B$ を"
                "独立に扱い、どちらにも全体の予算を許している。"
                "実際には根が最後に置かれた時刻 $t^*$ で "
                "$x+y+1\\le P$（$x=A$ の駒数, $y=B$ の駒数, $x,y\\ge1$）が成り立つ。"
                "$g_p(x)$ を「ピーク $\\le p$ で $\\varnothing$ から"
                "『$a$ を含み駒数ちょうど $x$』へ」の最小手数とすると"
            )
            lines.append("")
            lines.append("$$M^*(T_7,10)\\;\\ge\\;\\min_{x,y\\ge1,\\;x+y\\le 9}"
                         "\\bigl[g_{10}(x)+g_9(x)+g_{10}(y)+g_9(y)\\bigr]+1"
                         f"\\;=\\;{lb_joint}$$")
            lines.append("")
            lines.append(f"最小は $(x,y)=({x},{y})$ で達成される。実測値:")
            lines.append("")
            lines.append("| $x$ | " + " | ".join(str(k) for k in sorted(gP)) + " |")
            lines.append("|---|" + "---|" * len(gP))
            lines.append("| $g_{10}(x)$ | "
                         + " | ".join(str(gP[k]) for k in sorted(gP)) + " |")
            lines.append("| $g_9(x)$ | "
                         + " | ".join(str(gQ.get(k, "—")) for k in sorted(gP)) + " |")
            lines.append("")
            lines.append(
                f"⚠ 駒数を無視した版はこの min の下側なので**必ず従来以上**になる"
                f"（従来 {prev} → {lb_joint}）。"
                "健全性は既知の $M^*$（$T_4$〜$T_6$）で校正済み: "
                "`python3 scripts/exp01b_lb_refine.py --calibrate`。"
            )
            lb = max(lb, lb_joint)
            print(f"  結合制約版: {lb_joint}（従来 {prev}・{time.time()-t1:.1f}s）",
                  flush=True)

        lines.append("")
        lines.append(
            f"## 結論\n\n$$ {lb} \\;\\le\\; M^*(T_7,10) \\;\\le\\; {ub} $$\n\n"
            f"幅は {ub-lb}（上界の {100*(ub-lb)/ub:.0f}%）。**厳密値は未確定。**\n\n"
            f"下界がまだ緩い主因は、$g_p(x)$ が「$a$ を含む**何らかの**配置」への"
            f"到達距離であって clean を要求していないこと"
            f"（$x=1$ のときだけ clean と一致し $g_{{10}}(1)=M^*(T_6,10)=295$ になる）。"
            f"次の一手は、往路と復路が**同じ**配置 $C_A$ を通ることを使って"
            f"$\\min_C [d(\\varnothing,C)+d(C,\\varnothing)]$ を配置ごとに取ること。"
        )
        print(f"下界: {lb}（上界 {ub}）", flush=True)

    OUT.write_text("\n".join(lines) + "\n")
    print(f"\n→ {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
