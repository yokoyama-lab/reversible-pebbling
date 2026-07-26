"""飽和指標 $\\sigma$ の検証（`data/exp01_results.md` §3.3 の仮説）。

$$\\sigma(G) := \\frac{M^*(G,p_{\\min})}{M^*(G,p_{\\min}+1)}$$

**仮説**: $\\sigma$ は「$p_{\\min}$ に余分な段差が入る直前の族員」で上昇し、**段差の直後に急落する**。

検証台に **spinal tree $S_k^*$**（all-pebbled 流儀、$2k+1$ 頂点）を使う。
理由: $p_{\\min}(S_k^*) = \\lfloor\\log_2 k\\rfloor + 3$ が $k\\le16$ で厳密に成立し、
**段差位置が $k=2,4,8,16$（ちょうど 2 の冪）と事前に予測できる**。
当てはめではなく「予測 → 確認」の形になる。

$k=16$ 前後（3 段目→4 段目の段差）で急落が再現するかが判定点。

出力: `data/exp01b_saturation.csv`（自動生成・手編集禁止）

実行: python3 scripts/exp01b_saturation.py [--kmax 17]
"""

from __future__ import annotations

import argparse
import csv
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp01b_engine import all_pebbled, mstar, pmin, spinal_tree  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "data" / "exp01b_saturation.csv"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--kmax", type=int, default=17)
    ap.add_argument("--cap", type=int, default=30_000_000, help="訪問状態数の上限（メモリ保護）")
    args = ap.parse_args()

    rows: list[dict] = []
    for k in range(1, args.kmax + 1):
        g = all_pebbled(spinal_tree(k))
        t = g.n - 1
        t0 = time.time()
        # 観測された規則: p_min(S_k*) = floor(log2 k) + 3（段差はちょうど 2 の冪）
        predicted = (k.bit_length() - 1) + 3
        try:
            p0 = pmin(g, t)
            m0 = mstar(g, t, p0, cap=args.cap) if p0 else None
            m1 = mstar(g, t, p0 + 1, cap=args.cap) if p0 else None
        except RuntimeError as exc:
            print(f"k={k}: 到達できなかった（{exc}）", flush=True)
            rows.append({"k": k, "vertices": g.n, "p_min": "NR"})
            continue
        sigma = (m0 / m1) if (m0 and m1) else None
        rows.append(
            {
                "k": k,
                "vertices": g.n,
                "p_min": p0,
                "p_min_predicted": predicted,
                "M*_p_min": m0,
                "M*_p_min+1": m1,
                "sigma": round(sigma, 4) if sigma else None,
                "is_power_of_two": int(k > 0 and (k & (k - 1)) == 0),
                "sec": round(time.time() - t0, 1),
            }
        )
        print(
            f"k={k:<3} V={g.n:<3} p_min={p0} (予測 {predicted}) "
            f"M*={m0:<5} M*+1={m1:<5} sigma={sigma:.3f}"
            + ("  <- 2の冪（段差）" if (k & (k - 1)) == 0 else "")
            + f"  ({time.time()-t0:.1f}s)",
            flush=True,
        )

    fields = [
        "k",
        "vertices",
        "p_min",
        "p_min_predicted",
        "M*_p_min",
        "M*_p_min+1",
        "sigma",
        "is_power_of_two",
        "sec",
    ]
    with OUT.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        for r in rows:
            w.writerow(r)
    print(f"\n→ {OUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
