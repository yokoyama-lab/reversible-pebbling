"""本プロジェクトで得た全ての厳密数列に holonomic guessing を適用する。

出力: data/holonomic_guess.md（自動生成・手編集禁止）

## 設計上の要点（重要）

M*(G, p_min) の数列は **$p_{\min}$ が段差で変わる位置で不連続に落ちる**
（ピラミッド $h=5\to6$: $105\to99$、spinal $k=7\to8$: $61\to57$）。
これは**区分的な量**であり、単一の漸化式が成り立つ理由がない。

→ **固定 $p$ での $n$（または $h$）に関する数列のほうが、holonomic の候補として自然。**
本スクリプトは両方を試し、その差自体を結果として報告する。

使い方:
    python3 scripts/exp_guess_sequences.py            # 既定（数分）
    python3 scripts/exp_guess_sequences.py --pmax 7   # 鎖の固定 p を増やす（重い）
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp01b_engine import mstar  # 高速なビットマスク双方向 BFS  # noqa: E402
from holonomic import report  # noqa: E402
from revpebble import chain  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "holonomic_guess.md"

# --- 出典つきの既知数列（手入力。各行に生成元を明記すること） -------------------

SEQUENCES: list[tuple[str, list[int], str]] = [
    (
        "鎖の $M^*(p_{\\min})$",
        [1, 3, 5, 9, 11, 15, 19, 25, 25, 29, 33, 39, 45, 53, 61, 71],
        "先行プロジェクト 2026_exact_reversible_pebbling（$n=1..16$）。OEIS 未登録。"
        "$p_{\\min}$ が $n=9$ で変わるため区分的。",
    ),
    (
        "完全二分木の $M^*(T_h)$",
        [1, 5, 17, 53, 155, 429],
        "data/exp01_results.md §2.1（$h=1..6$、free-leaves 流儀）。OEIS 未登録。"
        "予想 $2\\cdot3^h-1$ は反証済み。",
    ),
    (
        "ピラミッドの $M^*(P_h, p_{\\min})$",
        [5, 13, 27, 47, 105, 99],
        "data/exp01_results.md §2.2（$h=1..6$、all-pebbled 流儀）。"
        "$h=6$ で $p_{\\min}$ が 2 段上がり値が**減る**（区分的）。",
    ),
    (
        "ピラミッドの $M^*(P_h, p_{\\min})$（段差前のみ $h=1..5$）",
        [5, 13, 27, 47, 105],
        "上の数列から $p_{\\min}$ 段差の手前だけを取り出したもの。"
        "4点当てはめ $3h^2-h+3$ が5点目で崩壊した実例。",
    ),
    (
        "spinal tree $S_k^*$ の $M^*(p_{\\min})$",
        [5, 11, 19, 25, 35, 45, 61, 57, 71, 85, 101, 119, 137, 155, 179, 153],
        "data/exp01_results.md §2.3（$k=1..16$、all-pebbled 流儀）。OEIS 未登録。"
        "$k=8,16$ で $p_{\\min}$ 段差＝値が減る（区分的）。",
    ),
    (
        "spinal tree $S_k^*$ の $M^*(p_{\\min})$（段差の内側 $k=8..15$）",
        [57, 71, 85, 101, 119, 137, 155, 179],
        "上の数列から $p_{\\min}=6$ が続く区間だけを取り出したもの（固定 $p$ 相当）。",
    ),
    (
        "spinal tree $S_k^*$ の $M^*(p_{\\min}+1)$",
        [5, 9, 17, 23, 31, 39, 47, 53, 61, 71, 81, 91, 105, 121, 137, 125],
        "data/exp01_results.md §2.3。",
    ),
    (
        "$\\Sigma_{\\mathrm{rev}}(k)$（可逆 BB の最大 1 の個数）",
        [1, 2, 4, 8, 16],
        "data/exp05_results.md（$k=1..5$、五つ組形式）。bbchallenge wiki に無い量。OEIS 未登録。",
    ),
    (
        "四つ組形式 $\\mathrm{BB}^4_{\\mathrm{rev}}(k)$",
        [2, 4, 6, 12, 22, 34],
        "data/exp05_results.md（$k=1..6$、Morita 流四つ組）。wiki 未収録。",
    ),
    (
        "五つ組 $\\mathrm{BB}_{\\mathrm{rev}}(k)$（既知値・対照）",
        [6, 17, 48, 388],
        "bbchallenge wiki（$k=2..5$）。**我々の発見ではなく既知値の独立再現**。",
    ),
]


def fixed_p_chain(pmax: int) -> list[tuple[str, list[int], str]]:
    """鎖の固定 $p$ における $M^*(n,p)$（$n=1..2^{p-1}$）。holonomic の本命候補。"""
    out = []
    for p in range(3, pmax + 1):
        seq: list[int] = []
        for n in range(1, 2 ** (p - 1) + 1):
            g = chain(n)
            v = mstar(g, n, p)
            if v is None:
                break
            seq.append(v)
        if len(seq) >= 6:
            out.append(
                (
                    f"鎖の $M^*(n, p={p})$（固定 $p$）",
                    seq,
                    f"本スクリプトが `exp01b_engine.mstar` で計算（$n=1..{len(seq)}$、"
                    f"到達限界 $2^{{p-1}}={2 ** (p - 1)}$）。"
                    "**$p$ を固定しているので区分性が無く、holonomic の本命候補。**",
                )
            )
    return out


def fib_from_csv() -> list[tuple[str, list[int], str]]:
    path = ROOT / "data" / "exp04_fib.csv"
    if not path.exists():
        return []
    rows = list(csv.DictReader(path.open()))
    out = []
    for col, label in [
        ("M*_p_min+0", "$M^*(p_{\\min})$"),
        ("M*_p_min+1", "$M^*(p_{\\min}+1)$"),
    ]:
        seq = []
        for r in rows:
            v = r.get(col, "")
            if not v or v == "None":
                break
            seq.append(int(v))
        if len(seq) >= 6:
            out.append(
                (
                    f"Fibonacci 型メモ化 DAG の {label}",
                    seq,
                    f"data/exp04_fib.csv（{len(seq)} 項）。OEIS 未登録。"
                    "$p_{\\min}$ の段差で区分的。",
                )
            )
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pmax", type=int, default=6, help="鎖の固定 p の上限（既定 6 = n<=32）")
    args = ap.parse_args()

    seqs = fixed_p_chain(args.pmax) + SEQUENCES + fib_from_csv()

    lines = [
        "# holonomic guessing の適用結果（自動生成・手編集禁止）",
        "",
        "生成: `python3 scripts/exp_guess_sequences.py`／実装: `scripts/holonomic.py`",
        "（厳密整数演算のみ・外部依存なし。テストは `tests/test_holonomic.py`）",
        "",
        "**読み方**: 「見つかった」は *推測* であって証明ではない。ただし推測に使わなかった",
        "held-out の式すべてで成立することを確認しているので、当てはめとは信頼度が違う。",
        "「見つからなかった」は holonomic でない証拠にはならない（探索範囲・項数の問題）。",
        "",
        "---",
        "",
    ]
    found = 0
    for name, seq, prov in seqs:
        block = report(name, seq)
        lines.append(block)
        lines.append(f"- 出典: {prov}\n")
        if "**推測**" in block:
            found += 1
        lines.append("---\n")

    lines.insert(
        8,
        f"**要約: {len(seqs)} 本中 {found} 本で漸化式が見つかった。**\n",
    )
    OUT.write_text("\n".join(lines))
    print("\n".join(lines[:9]))
    print(f"→ {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
