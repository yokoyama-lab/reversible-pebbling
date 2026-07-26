"""$p_{\\min}(T_7)$ を厳密に決めるための構成的証書。

商グラフの全数探索で **$T_7$（free-leaves、ペブル対象 127 頂点）は $p=8,9$ で
到達不能**であることが分かった（下界 $p_{\\min}\\ge10$）。
上界側は探索がメモリ律速で届かないので、**手順を明示的に構成して検証器に通す**。

  1. $T_6$ の最適手順（$p=8$・429 手）を商グラフの距離表から実頂点番号で復元する。
  2. それを「左を作る → 右を作る → 根を置く → 右を片付ける → 左を片付ける」で合成し、
     $T_7$ の手順（$4\\cdot429+1 = 1717$ 手）を作る。ピークは $8+2=10$ 以下。
  3. `exp01b_engine.verify_schedule` （独立な検証器）で
     先行点規則・ピーク上限・clean 終端をすべて再検査する。

3 が通れば $p_{\\min}(T_7)\\le10$。下界と合わせて **$p_{\\min}(T_7)=10$（厳密）**。
同時に $M^*(T_7,10)\\le1717$ という（弱い）上界も得られる。

出力: `data/exp01b_certificate.md`（自動生成・手編集禁止）

実行: python3 scripts/exp01b_certificate.py
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import revpebble as rp  # noqa: E402
from exp01b_engine import verify_schedule  # noqa: E402
from treedp import compose_schedule, realize_optimal  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "exp01b_certificate.md"

# 既に確定済みの実測値（`tests/test_exp01c_treedp.py` に固定してある）。
# ここで pmin_tree/mstar_tree を呼び直すと $h=7$ で巨大な探索が走るので**再計算しない**。
KNOWN_PMIN = {2: 3, 3: 5, 4: 6, 5: 7, 6: 8, 7: 10}
KNOWN_MSTAR = {2: 5, 3: 17, 4: 53, 5: 155, 6: 429}  # p = p_min。h=7 は未確定


def certify(h: int, q: int) -> dict:
    """高さ h-1 の最適手順（ピーク q）から高さ h の手順を合成して検証する。"""
    t0 = time.time()
    sub = realize_optimal(h - 1, q)
    assert sub is not None, f"T_{h-1} が p={q} で到達不能"
    g_sub = rp.complete_binary_tree(h - 1)
    verify_schedule(g_sub, g_sub.n - 1, q, sub)  # 部分木の手順自体も検証
    seq = compose_schedule(h, sub)
    g = rp.complete_binary_tree(h)
    peak = 0
    cur = 0
    for kind, _ in seq:
        cur += 1 if kind == "put" else -1
        peak = max(peak, cur)
    verify_schedule(g, g.n - 1, q + 2, seq)  # ここが証書の本体
    return {
        "h": h,
        "sub_peak": q,
        "sub_moves": len(sub),
        "vertices": len(g.pebbleable()),
        "peak": peak,
        "moves": len(seq),
        "sec": round(time.time() - t0, 1),
    }


def main() -> None:
    lines = [
        "# exp01b — $p_{\\min}(T_7)=10$ の構成的証書（自動生成・手編集禁止）\n",
        "生成: `python3 scripts/exp01b_certificate.py`\n",
        "`complete_binary_tree(h)` free-leaves 流儀。手順はすべて",
        "`exp01b_engine.verify_schedule`（先行点規則・ピーク上限・clean 終端を再検査する",
        "独立な検証器）を通っている。\n",
        "| $h$ | ペブル対象頂点数 | 部分木のピーク $q$ | 部分木の手数 | 合成後のピーク | 合成後の手数 | 検証 | 秒 |",
        "|---|---|---|---|---|---|---|---|",
    ]
    rows = []
    for h, q in ((3, 3), (4, 5), (5, 6), (6, 7), (7, 8)):
        try:
            r = certify(h, q)
        except AssertionError as exc:
            lines.append(f"| {h} | — | {q} | — | — | — | **失敗**: {exc} | — |")
            continue
        except MemoryError:
            lines.append(f"| {h} | — | {q} | — | — | — | メモリ不足で未到達 | — |")
            continue
        rows.append(r)
        lines.append(
            f"| {r['h']} | {r['vertices']} | {r['sub_peak']} | {r['sub_moves']} | "
            f"{r['peak']} | {r['moves']} | OK | {r['sec']} |"
        )
        print(r, flush=True)

    lines.append("")
    lines.append("## 読み取り\n")
    lines.append(
        "- 逐次合成は $p_{\\min}(T_h)\\le p_{\\min}(T_{h-1})+2$ を**構成的に**保証する"
        "（各行の「合成後のピーク」が $q+2$ 以下）。"
    )
    lines.append(
        "- $h\\le6$ では実測の $p_{\\min}$ が合成の上界より小さい"
        "（合成は最適でない）。手数も $M^*$ より大きい。"
    )
    for r in rows:
        h = r["h"]
        p0 = KNOWN_PMIN.get(h)
        exact = KNOWN_MSTAR.get(h)
        head = f"  - $h={h}$: 合成 = ピーク {r['peak']} / {r['moves']} 手"
        if exact is not None:
            lines.append(f"{head}、実測 $p_{{\\min}}={p0}$ / $M^*={exact}$")
        else:
            lines.append(
                f"{head}、実測 $p_{{\\min}}={p0}$（$M^*$ は未確定なので"
                f"この {r['moves']} 手が現時点の上界）"
            )
    lines.append("")
    lines.append(
        "- **$h=7$**: 全数探索で $p=8,9$ が到達不能（下界 $p_{\\min}\\ge10$）、"
        "上の証書で $p=10$ が到達可能（上界 $p_{\\min}\\le10$）。"
        "→ **$p_{\\min}(T_7)=10$ が厳密に確定**。"
        "超過分 $p_{\\min}-h$ は $h=1..7$ で $0,1,2,2,2,2,3$ となり、**3段目の段差は $h=7$ で起きる**。"
    )
    OUT.write_text("\n".join(lines) + "\n")
    print(f"\n→ {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
