"""ZDD 記号的 BFS を**プロセスを跨いで分割実行**するドライバ（候補1・$M^*(T_7)$ 用）。

> **このスクリプトは `.venv` を要求する**（`graphillion` が `.venv` にある）。

## なぜ分割が必要か

graphillion（SAPPOROBDD）の**ノード表と演算キャッシュは単調増加で GC されない**。
`exp01b_zdd.mstar_zdd(two_level=True)` はロジカルな ZDD を 2 レベルだけに保つので
論理的なメモリは小さいが、**プロセスの RSS は伸び続ける**（$h=7$ で毎秒 6MB 程度、
実測で 12.7GB まで到達）。並行作業者がいる共有マシンでこれを何十分も走らせるのは危険。

そこで **「N レベル進める → 直前 2 レベルを保存 → プロセス終了」** を 1 セグメントとし、
シェルループで繰り返す。プロセスが終わるたびにノード表がリセットされるので
**RSS がセグメント内に収まる**。無向グラフの BFS は直前 2 レベルだけで再開できる
（`exp01b_zdd` §16.2）ので、この分割は**厳密性を一切損なわない**。

## 使い方

```bash
# 1 セグメント（既定 100 レベル）進める。答えが出たら stdout に "RESULT" を出す
.venv/bin/python scripts/exp01b_zdd_segment.py --h 7 --p 10 --levels 100 \\
    --ckpt data/exp01b_zdd_t7.ckpt

# 決着するまで繰り返す（各セグメントは独立プロセス）
until .venv/bin/python scripts/exp01b_zdd_segment.py --h 7 --p 10 --levels 100 \\
        --ckpt data/exp01b_zdd_t7.ckpt | tee -a data/exp01b_zdd_t7.log \\
        | grep -q "^RESULT"; do :; done
```

終了コード: 0 = 決着（RESULT 行を出力）／3 = セグメント完了・未決着（続行が必要）。
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp01b_zdd import (  # noqa: E402
    HAS_GRAPHILLION,
    load_checkpoint,
    mstar_zdd,
    save_checkpoint,
    set_universe_for,
)


def main() -> int:
    if not HAS_GRAPHILLION:
        print("ERROR: graphillion が無い。.venv/bin/python で実行すること。")
        return 2
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--levels", type=int, default=100, help="このセグメントで進めるレベル数")
    ap.add_argument("--ckpt", type=Path, required=True)
    ap.add_argument("--log-every", type=int, default=25)
    args = ap.parse_args()

    resume = None
    start = 0
    if args.ckpt.exists():
        h, p, start, prev, frontier = load_checkpoint(args.ckpt)
        if (h, p) != (args.h, args.p):
            print(f"ERROR: checkpoint は h={h}, p={p} 用（要求は h={args.h}, p={args.p}）")
            return 2
        resume = (start, prev, frontier)
        print(f"[resume] レベル {start} から再開", flush=True)
    else:
        set_universe_for(args.h)
        print("[start] 新規開始", flush=True)

    t0 = time.time()
    try:
        m = mstar_zdd(
            args.h,
            args.p,
            log_every=args.log_every,
            two_level=True,
            resume=resume,
            checkpoint=args.ckpt,
            checkpoint_every=max(args.levels, 1),
            max_levels=start + args.levels,
        )
    except TimeoutError:
        # セグメント完了（checkpoint は mstar_zdd が保存済み）。続行が必要。
        _, _, d, _, _ = load_checkpoint(args.ckpt)
        print(
            f"[segment] レベル {start} → {d} まで進めた（{time.time()-t0:.0f}s）。未決着。",
            flush=True,
        )
        return 3
    if m is None:
        print(f"RESULT h={args.h} p={args.p}: 到達不能（M* は存在しない）", flush=True)
    else:
        print(f"RESULT h={args.h} p={args.p}: M* = {m}  ({time.time()-t0:.0f}s)", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
