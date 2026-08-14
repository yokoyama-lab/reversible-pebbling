"""数列を**計算で伸ばす**（予想キューの律速は項数なので、そこに計算時間を使う）。

出力: `data/sequences_extended.csv`（追記。既存の自動生成 CSV は書き換えない）

`data/conjecture_queue.md` で「判定不能（項数不足）」になった数列は、
**1 点計算するたびに評価できる $(order, degree)$ の組が増える**。
holonomic の必要項数は $(r{+}1)(d{+}1) + r + \\mathrm{slack}$ なので、
項数を数点足すだけで到達できる範囲が広がる。

列: key, index, value, family, param, p, seconds, host
`key` は `scripts/sequences_index.py` の key に合わせる（そのまま数列に合流できる）。

    # Fibonacci 型メモ化 DAG を n=30..33 まで（3 列ぶん）
    python3 scripts/extend_sequences.py fib --from 30 --to 33
    # 円筒 (幅2) を k=19..20 まで
    python3 scripts/extend_sequences.py cylinder --width 2 --from 19 --to 20

**この計算は決定的**（乱数不使用）なので、途中で落ちても同じ点を計算し直せる。
"""

from __future__ import annotations

import argparse
import csv
import socket
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

OUT = ROOT / "data" / "sequences_extended.csv"
HEADER = ["key", "index", "value", "family", "param", "p", "seconds", "host"]


def append(rows: list[dict]) -> None:
    exists = OUT.exists()
    with OUT.open("a", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=HEADER)
        if not exists:
            w.writeheader()
        for r in rows:
            w.writerow(r)


def fast_pmin(g, target: int, lo: int = 1, hi: int = 40) -> int | None:
    """最小ピーク $p_{\\min}$ を**高速エンジン**で求める。

    `revpebble.pmin` は素朴 BFS を $p=1$ から回すので、$n=30$ で 76 秒かかる
    （実測）。ここでは `exp01b_engine.mstar`（双方向 BFS）を使い、さらに
    **$p_{\\min}$ が $n$ について単調非減少**であることを使って前の $n$ の値から探し始める。
    `revpebble.py` は読むだけ・編集禁止なので、探索はこちら側に置く。
    """
    from exp01b_engine import mstar          # noqa: PLC0415
    for p in range(max(1, lo), hi + 1):
        if mstar(g, target, p) is not None:
            return p
    return None


def run_fib(lo: int, hi: int, offsets: list[int]) -> None:
    from exp01b_engine import mstar          # noqa: PLC0415
    from memo_dags import fib_dag            # noqa: PLC0415
    host = socket.gethostname()
    pm_lo = 1
    for n in range(lo, hi + 1):
        g = fib_dag(n)
        t0 = time.time()
        pm = fast_pmin(g, n, lo=pm_lo)
        if pm is None:
            print(f"fib({n}): p_min が見つからない", flush=True)
            continue
        pm_lo = pm
        rows = []
        for off in offsets:
            t = time.time()
            v = mstar(g, n, pm + off)
            sec = time.time() - t
            if v is None:
                print(f"fib({n}) off={off}: 到達不能", flush=True)
                continue
            rows.append({"key": f"fib:M*_p_min+{off}", "index": n, "value": v,
                         "family": "fib", "param": "", "p": pm + off,
                         "seconds": f"{sec:.2f}", "host": host})
            rows.append({"key": f"slice:fib:M*_p_min+{off}:p{pm}", "index": n,
                         "value": v, "family": "fib", "param": "", "p": pm + off,
                         "seconds": f"{sec:.2f}", "host": host})
            print(f"fib({n}) p_min={pm} M*(p_min+{off})={v}  {sec:.1f}s", flush=True)
        append(rows)
        print(f"  → fib({n}) 完了（p_min 計算込み {time.time() - t0:.1f}s）", flush=True)


def run_cylinder(width: int, lo: int, hi: int, offsets: list[int]) -> None:
    from exp01b_engine import mstar          # noqa: PLC0415
    from families import cylinder            # noqa: PLC0415
    host = socket.gethostname()
    pm_lo = 1
    for k in range(lo, hi + 1):
        g = cylinder(width, k)
        target = g.n - 1
        t0 = time.time()
        pm = fast_pmin(g, target, lo=pm_lo)
        if pm is None:
            continue
        pm_lo = pm
        rows = []
        for off in offsets:
            t = time.time()
            v = mstar(g, target, pm + off)
            sec = time.time() - t
            if v is None:
                continue
            rows.append({"key": f"fam:cylinder:k[w={width}]:off{off}", "index": k,
                         "value": v, "family": "cylinder", "param": f"{width}:{k}",
                         "p": pm + off, "seconds": f"{sec:.2f}", "host": host})
            rows.append({"key": f"slice:fam:cylinder:k[w={width}]:off{off}:p{pm}",
                         "index": k, "value": v, "family": "cylinder",
                         "param": f"{width}:{k}", "p": pm + off,
                         "seconds": f"{sec:.2f}", "host": host})
            print(f"cylinder({width},{k}) p_min={pm} M*(+{off})={v}  {sec:.1f}s",
                  flush=True)
        append(rows)
        print(f"  → cylinder({width},{k}) 完了（{time.time() - t0:.1f}s）", flush=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("what", choices=["fib", "cylinder"])
    ap.add_argument("--from", dest="lo", type=int, required=True)
    ap.add_argument("--to", dest="hi", type=int, required=True)
    ap.add_argument("--width", type=int, default=2)
    ap.add_argument("--offsets", type=str, default="0,1,2")
    args = ap.parse_args()
    offs = [int(x) for x in args.offsets.split(",")]
    if args.what == "fib":
        run_fib(args.lo, args.hi, offs)
    else:
        run_cylinder(args.width, args.lo, args.hi, offs)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
