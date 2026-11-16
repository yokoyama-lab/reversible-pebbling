#!/usr/bin/env python3
"""night80r3_level_profile_cmp.py — レベル幅の列どうしを突き合わせる.

**なぜ 1 個の数ではなく列を比べるのか。**
$M^*(T_7,10)=1001$ は 3 実装（第49夜・第75夜・今夜）が出しているが、一致しているのは
**数 1 個**である。偶然でない一致の証拠としては弱い。一方 BFS のレベル幅の列
$|L_0|,\\dots,|L_{1000}|$ は 1001 本の独立な数で、**途中で 1 つでもずれたら
正準化か後続関数のどちらかが違う**ことが分かる。

比べる 2 つ:
  * 第76夜のレベル集合証書 `/work/tmp/night76_cert/h7p10/L%05d.bin`
    （preorder-u128-le16 符号化。1 状態 = 16 バイトなので **ファイルサイズ/16 が幅**）
  * 今夜の `--levels` 出力（`d<TAB>|L_d|<TAB>累計<TAB>経過秒`）

⚠ 第76夜の証書は $L_0..L_{1000}$ だけで、goal を含む $L_{1001}$ は入っていない。
したがって突き合わせは $d\\le 1000$ まで。

走行中でも使える（今夜の列が途中までしか無ければ、**そこまでを**比べて進捗を返す）。
"""

from __future__ import annotations

import argparse
import json
import os
import sys

CERT_DIR = "/work/tmp/night76_cert/h7p10"


def cert_profile(cert_dir: str) -> list[int]:
    """証書のファイルサイズから各レベルの幅を読む（中身は読まない）。"""
    out = []
    d = 0
    while True:
        path = os.path.join(cert_dir, f"L{d:05d}.bin")
        if not os.path.exists(path):
            break
        size = os.path.getsize(path)
        if size % 16 != 0:
            raise SystemExit(f"{path}: サイズ {size} が 16 の倍数でない")
        out.append(size // 16)
        d += 1
    return out


def levels_profile(path: str) -> tuple[list[int], int | None]:
    """--levels の出力を読む。(幅の列, goal の深さ or None)。"""
    widths: list[int] = []
    goal_depth = None
    with open(path) as fh:
        for line in fh:
            f = line.rstrip("\n").split("\t")
            if len(f) < 2:
                continue
            d, w = int(f[0]), int(f[1])
            if len(f) >= 5 and f[4] == "GOAL":
                goal_depth = d
                # goal を含むレベルも幅としては正しいので列に入れる
            if d != len(widths):
                raise SystemExit(f"{path}: 深さが飛んでいる（期待 {len(widths)}・実際 {d}）")
            widths.append(w)
    return widths, goal_depth


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cert-dir", default=CERT_DIR)
    ap.add_argument("--levels", required=True)
    ap.add_argument("--json", type=str)
    args = ap.parse_args()

    cert = cert_profile(args.cert_dir)
    mine, goal_depth = levels_profile(args.levels)
    n = min(len(cert), len(mine))
    if n == 0:
        raise SystemExit("比べる深さが無い")

    mismatches = [(d, cert[d], mine[d]) for d in range(n) if cert[d] != mine[d]]
    rec = {
        "cert_levels": len(cert),
        "mine_levels": len(mine),
        "compared": n,
        "mismatches": len(mismatches),
        "first_mismatches": mismatches[:5],
        "cert_sum_compared": sum(cert[:n]),
        "mine_sum_compared": sum(mine[:n]),
        "mine_goal_depth": goal_depth,
        "mine_max_width": max(mine) if mine else None,
        "cert_max_width": max(cert) if cert else None,
        "complete": len(cert) == 1001 and goal_depth is not None,
    }
    print(json.dumps(rec, ensure_ascii=False, indent=2))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(rec, fh, ensure_ascii=False, indent=2)
    if mismatches:
        print(f"NG: {len(mismatches)} 本のレベルで幅が違う", file=sys.stderr)
        return 1
    print(f"OK: 深さ 0..{n - 1} の {n} 本すべてで幅が一致"
          f"（累計 {sum(mine[:n])} 状態）", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
