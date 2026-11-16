#!/usr/bin/env python3
"""鎖で「並列時間最適 2n-1 が保てる上限」 n*(p) を挟み撃ちで決める（台帳 Q2）。

**途中から再開できる**: 結果は 1 行ずつ CSV へ追記＋flush し、
既に決まっている p は読み飛ばす（2026-08-13 の指示）。

予想（p=4..9 で確認済み）: n*(p) = (p-2)(p-3) + 5
  p:      4   5   6   7   8   9
  n*(p):  7  11  17  25  35  47

使い方:
  q2_threshold.py --pmax 11 --out data/q2_threshold.csv
  q2_threshold.py --pmax 12 --out data/q2_threshold.csv   # 続きから
"""
from __future__ import annotations

import argparse
import csv
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from parallel_revpebble import line, solve  # noqa: E402


def opt_ok(n: int, p: int, max_sec: float):
    """n 頂点の鎖が p ペブルで T=2n-1 に到達できるか。True/False/None(打ち切り)。"""
    par, sk = line(n)
    return solve(par, sk, p, 2 * n - 1, True, False, max_sec=max_sec)


def find_threshold(p: int, lo: int, hi: int, max_sec: float, log=print):
    """[lo,hi] で「2n-1 が可能な最大の n」を二分探索する。

    ⚠ **単調性を仮定している**（n が大きいほど難しい）。仮定が破れたら値は無意味。
    そこで最後に n*+1 が本当に不可能かを確かめる。打ち切りが出たら None を返す。
    """
    best = None
    while lo <= hi:
        mid = (lo + hi) // 2
        r = opt_ok(mid, p, max_sec)
        log(f"    p={p} n={mid}: {r}")
        if r is None:
            return None, "打ち切り"
        if r:
            best = mid
            lo = mid + 1
        else:
            hi = mid - 1
    if best is None:
        return None, "範囲内に可能な n が無い"
    # **境界の確認**: n*+1 が不可能であることを直接見る
    r = opt_ok(best + 1, p, max_sec)
    if r is None:
        return best, "境界は未確認（打ち切り）"
    if r:
        return None, f"**単調性が破れた: n={best+1} が可能**"
    return best, "確認済み"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--pmin", type=int, default=4)
    ap.add_argument("--pmax", type=int, default=11)
    ap.add_argument("--out", required=True)
    ap.add_argument("--max-sec", type=float, default=600.0)
    a = ap.parse_args()

    done = {}
    if os.path.exists(a.out):
        with open(a.out, newline="") as f:
            for r in csv.DictReader(f):
                done[int(r["p"])] = r
        print(f"# 再開: 済み {sorted(done)} を飛ばす", file=sys.stderr)
        fh = open(a.out, "a", newline="")
        w = csv.writer(fh)
    else:
        fh = open(a.out, "w", newline="")
        w = csv.writer(fh)
        w.writerow(["p", "n_star", "predicted", "match", "note", "sec"])
        fh.flush()

    for p in range(a.pmin, a.pmax + 1):
        if p in done:
            continue
        pred = (p - 2) * (p - 3) + 5
        # 予想の周辺を十分に含む範囲。上は実行可能性 2^(p-1) で頭打ち
        lo, hi = max(2, pred - 12), min(pred + 12, 2 ** (p - 1))
        t0 = time.time()
        print(f"  p={p}: 予想 {pred}、範囲 [{lo},{hi}] を二分探索", file=sys.stderr)
        ns, note = find_threshold(p, lo, hi, a.max_sec,
                                  log=lambda s: print(s, file=sys.stderr))
        m = "○" if ns == pred else ("**✗**" if ns is not None else "-")
        w.writerow([p, ns if ns is not None else "", pred, m, note,
                    round(time.time() - t0, 1)])
        fh.flush()
        print(f"  p={p}: n*={ns} 予想 {pred} {m} （{note}）", file=sys.stderr)


if __name__ == "__main__":
    main()
