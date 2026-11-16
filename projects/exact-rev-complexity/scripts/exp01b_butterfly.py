"""バタフライ $BF_k$ の「出力を同時に clean」流儀の厳密表（候補1 タスク3）。

## なぜこの終端条件なのか

- **単一出力**を終端にすると $M^*(BF_k,p) = M^*(T_k,p)$ に**厳密に潰れる**
  （1 出力の祖先錐が先行点で閉じた完全二分木になるため。`tests/test_exp01d_kralovic.py`）。
  → バタフライ固有の情報はゼロ。
- **Královič の $S_{\\min}(Bf(d))$ も新情報を与えない**: 彼の complete computation は
  「全頂点が一度カバーされる」で、これは「各出力を**順番に**カバーする」と同値なので
  $S_{\\min}(Bf(d)) = S_{\\min}(Bt(d))$（彼の Lem 4.10/4.11）。順番にやれば1つの錐で足りる。
- **同時性を要求すると初めて潰れなくなる**。そこで終端を
  「最終段の $2^k$ 頂点が**同時に**ペブルされた clean 状態」に取る。
  これは本プロジェクトの新しい量である（彼の論文には無い）。

中間の点も取るため、終端を「最終段のうち $j$ 個を同時に clean」として
$j = 1,2,4,\\dots,2^k$ で測る（$j=1$ が完全二分木、$j=2^k$ が全出力）。

出力: `data/exp01b_butterfly.csv`（自動生成・手編集禁止）

実行: python3 scripts/exp01b_butterfly.py [--kmax 3] [--extra 3]
"""

from __future__ import annotations

import argparse
import csv
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import revpebble as rp  # noqa: E402
from exp01b_engine import (  # noqa: E402
    butterfly,
    mstar,
    mstar_mask,
    pmin_mask,
    smin_kralovic,
)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "exp01b_butterfly.csv"


def output_mask(k: int, j: int) -> int:
    """$BF_k$ の最終段の先頭 $j$ 頂点のマスク。"""
    w = 2**k
    m = 0
    for i in range(j):
        m |= 1 << (k * w + i)
    return m


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=3)
    ap.add_argument("--extra", type=int, default=3)
    ap.add_argument("--cap", type=int, default=20_000_000)
    ap.add_argument("--budget", type=float, default=480.0)
    args = ap.parse_args()

    rows: list[dict] = []
    for k in range(1, args.kmax + 1):
        g = butterfly(k)
        w = 2**k
        # 彼の S_min（1 出力の錐 = 完全二分木の値に等しい）
        s_his = smin_kralovic(g, g.n - 1)
        j = 1
        while j <= w:
            goal = output_mask(k, j)
            t0 = time.time()
            row: dict[str, object] = {
                "k": k,
                "vertices": g.n,
                "pebbleable": len(g.pebbleable()),
                "outputs_simultaneous": j,
                "smin_kralovic_1out": s_his,
            }
            try:
                p0 = pmin_mask(g, goal)
            except RuntimeError:
                row["p_min"] = "NR"
                rows.append(row)
                break
            row["p_min"] = p0
            if p0 is not None:
                for e in range(args.extra + 1):
                    if time.time() - t0 > args.budget:
                        row[f"M*_p{e}"] = "TO"
                        break
                    try:
                        row[f"M*_p{e}"] = mstar_mask(g, goal, p0 + e, cap=args.cap)
                    except RuntimeError:
                        row[f"M*_p{e}"] = "NR"
                        break
            row["sec"] = round(time.time() - t0, 1)
            rows.append(row)
            print(
                f"BF_{k} 出力 {j}/{w} 同時: p_min={p0} "
                + " ".join(str(row.get(f"M*_p{e}")) for e in range(args.extra + 1))
                + f"  ({row['sec']}s)",
                flush=True,
            )
            j *= 2

        # 単一出力が完全二分木に潰れることの再確認
        if k <= 3:
            same = mstar(g, g.n - 1, k + 4) == mstar(
                rp.complete_binary_tree(k), 2 ** (k + 1) - 2, k + 4
            )
            print(f"  BF_{k} 単一出力 == cbt({k}): {same}", flush=True)

    fields = [
        "k",
        "vertices",
        "pebbleable",
        "outputs_simultaneous",
        "p_min",
        "smin_kralovic_1out",
    ] + [f"M*_p{e}" for e in range(args.extra + 1)] + ["sec"]
    with OUT.open("w", newline="") as fh:
        wr = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore")
        wr.writeheader()
        for r in rows:
            wr.writerow(r)
    print(f"\n→ {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
