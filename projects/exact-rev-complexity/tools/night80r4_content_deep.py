#!/usr/bin/env python3
"""night80r4_content_deep.py — レベル集合の**中身**を、主張を担う深さで証書と突き合わせる.

第 80 夜 周 3 は深さ 0..22 の 23 本をバイト列まで一致させた。だが
$M^*(T_7,10)\\ge 1001$ という主張を担っているのは**深さ 1000 の側**である
（「深さ 1000 以下に goal が無い」）。浅い側だけを一致させても、
「深い側で両実装が同じ幅のまま別の集合を持っている」可能性は残る。

ここは (a) 浅い側（回帰）・(b) 中間・(c) **深さ 990..1000** の 3 つの帯で中身を比べる。

## 周 3 との違い — 翻訳を 1 状態 400 μs から ~5 μs へ

周 3 の `night80r3_content_cmp.py` は「id → 代表配置 → preorder のビットマスク →
`cert_canon`」と、状態ごとに木を 2 回降りていた。深い帯は 1 レベルが 70 万状態あり、
この速さでは 1 レベル 5 分かかって帯を比べられない。

観察: 証書の `canon` は**部分木ごとの再帰**で、各節点で子 2 つの値を大小で並べ替える。
こちらの状態表現は**部分木ごとに hash-cons した id** である。したがって

    cc(j, i) = b | (max(cc(j-1,L), cc(j-1,R)) << 1)
                 | (min(cc(j-1,L), cc(j-1,R)) << (1 + S(j-1)))

を id について memo 化すれば、**同じ部分木を二度降りない**。並べ替えの基準が
こちらの id 順でなく証書の値順である点は max/min で吸収される（cc は子の
**非順序対**の関数なので well-defined）。

⚠ 速い翻訳は周 3 の（既に監査済みの）素朴な翻訳と**一致を確かめてから**使う
（`--selfcheck-depth`、既定 12）。ここを省くと「速い方が間違っていて両方同じに見える」
という最悪の形になる。

使い方:
    python3 tools/night80r4_content_deep.py --h 7 --p 10 \\
        --depths 0-30,300-301,500-501,700-701,990-1000 \\
        --jsonl autoresearch/results/night80r4_deep.jsonl
    python3 tools/night80r4_content_deep.py --h 7 --p 10 --depths 0-12 --mutate 10
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from night80r2_quotbfs import Quotient  # noqa: E402
from night80r3_content_cmp import heap_to_pre, top_to_cert  # noqa: E402

CERT_DIR = "/work/tmp/night76_cert/h7p10"


class FastTrans:
    """id → 証書の canon 値（部分木ごとに memo 化）."""

    def __init__(self, q: Quotient, memo_max: int):
        self.q = q
        self.h = q.h
        self.memo_max = memo_max
        self.memo = [dict() for _ in range(q.h + 1)]
        # 高さ j の節点の右の子の詰め先 = 1 + S(j-1) = 2^(j-1)
        self.rshift = [0] + [1 << (j - 1) for j in range(1, q.h + 1)]

    def cc(self, j: int, i: int) -> int:
        if j == 0:
            return 0
        memo = self.memo[j] if j <= self.memo_max else None
        if memo is not None:
            v = memo.get(i)
            if v is not None:
                return v
        b, L, R, _ = self.q.info[j][i]
        a = self.cc(j - 1, L)
        c = self.cc(j - 1, R)
        if a < c:
            a, c = c, a
        v = b | (a << 1) | (c << self.rshift[j])
        if memo is not None:
            memo[i] = v
        return v

    def top(self, key: int) -> int:
        h = self.h
        b = key & 1
        a = self.cc(h - 1, (key >> 1) & 0xFFFFFFFF)
        c = self.cc(h - 1, key >> 33)
        if a < c:
            a, c = c, a
        return b | (a << 1) | (c << self.rshift[h])


def parse_depths(spec: str) -> set[int]:
    out: set[int] = set()
    for part in spec.split(","):
        part = part.strip()
        if not part:
            continue
        if "-" in part:
            a, b = part.split("-")
            out.update(range(int(a), int(b) + 1))
        else:
            out.add(int(part))
    return out


def read_level(cert_dir: str, d: int) -> list[int]:
    with open(os.path.join(cert_dir, f"L{d:05d}.bin"), "rb") as fh:
        raw = fh.read()
    return [int.from_bytes(raw[i:i + 16], "little") for i in range(0, len(raw), 16)]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--depths", required=True, help="例 0-30,500-501,990-1000")
    ap.add_argument("--cert-dir", default=CERT_DIR)
    ap.add_argument("--memo-max", type=int, default=None,
                    help="cc を memo 化する最大の高さ（既定 h-2）")
    ap.add_argument("--selfcheck-depth", type=int, default=12,
                    help="この深さまでは素朴な翻訳とも突き合わせる（0 で無効）")
    ap.add_argument("--mutate", type=int, default=None,
                    help="この深さで自分の集合を 1 ビット壊す（検出力の確認）")
    ap.add_argument("--jsonl", type=str, help="レベルごとの判定を逐次追記する")
    ap.add_argument("--json", type=str)
    ap.add_argument("--levels", type=str, help="レベル幅を 1 行ずつ追記する")
    args = ap.parse_args()

    h, p = args.h, args.p
    want = parse_depths(args.depths)
    dmax = max(want)
    memo_max = args.memo_max if args.memo_max is not None else max(1, h - 2)

    q = Quotient(h, p)
    tr = FastTrans(q, memo_max)
    h2p = heap_to_pre(h)
    e = q.empty[h - 1]
    start = q.top_key(0, e, e)
    goal = q.top_key(1, e, e)
    goal_cert = tr.top(goal)

    jl = open(args.jsonl, "w") if args.jsonl else None
    lv = open(args.levels, "w") if args.levels else None
    t0 = time.time()

    def emit(rec: dict) -> None:
        if jl is not None:
            jl.write(json.dumps(rec, ensure_ascii=False) + "\n")
            jl.flush()

    emit({"kind": "meta", "h": h, "p": p, "depths": sorted(want),
          "memo_max": memo_max, "goal_cert": str(goal_cert),
          "selfcheck_depth": args.selfcheck_depth, "mutate": args.mutate})

    results: list[dict] = []
    selfcheck = {"levels": 0, "states": 0, "mismatch": 0}
    prev: set = set()
    cur = {start}
    d = 0
    ok_all = True
    goal_depth = None

    while True:
        if lv is not None:
            lv.write(f"{d}\t{len(cur)}\t{time.time() - t0:.1f}\n")
            lv.flush()
        if d in want:
            ts = time.time()
            mine = sorted(tr.top(k) for k in cur)
            if args.selfcheck_depth and d <= args.selfcheck_depth:
                naive = sorted(top_to_cert(q, k, h2p, h) for k in cur)
                selfcheck["levels"] += 1
                selfcheck["states"] += len(naive)
                if naive != mine:
                    selfcheck["mismatch"] += 1
                    ok_all = False
                    print(f"NG selfcheck depth={d}: 速い翻訳と素朴な翻訳が不一致",
                          file=sys.stderr, flush=True)
            if args.mutate is not None and d == args.mutate and mine:
                mine[0] ^= 1
                mine = sorted(mine)
            theirs = read_level(args.cert_dir, d)
            same = mine == theirs
            ok_all = ok_all and same
            rec = {"kind": "level", "depth": d, "mine": len(mine),
                   "cert": len(theirs), "identical": same,
                   "goal_in_cert": goal_cert in theirs,
                   "sec": round(time.time() - ts, 1),
                   "elapsed": round(time.time() - t0, 1)}
            if not same:
                sm, st = set(mine), set(theirs)
                rec["only_mine"] = len(sm - st)
                rec["only_cert"] = len(st - sm)
                print(f"NG depth={d}: 幅 {len(mine)} vs {len(theirs)}",
                      file=sys.stderr, flush=True)
            results.append(rec)
            emit(rec)
            print(json.dumps(rec, ensure_ascii=False), flush=True)
            del mine, theirs

        if d >= dmax:
            break
        nxt = set()
        for s in cur:
            for t in q.succ_top(s):
                if t not in cur and t not in prev:
                    nxt.add(t)
        if goal in nxt:
            goal_depth = d + 1
            print(f"goal を深さ {goal_depth} で踏んだ", file=sys.stderr, flush=True)
            break
        prev, cur = cur, nxt
        d += 1

    rec = {"kind": "summary", "h": h, "p": p,
           "levels_compared": len(results),
           "levels_identical": sum(1 for r in results if r["identical"]),
           "states_compared": sum(r["cert"] for r in results),
           "all_identical": ok_all,
           "goal_in_any_compared_cert_level":
               any(r["goal_in_cert"] for r in results),
           "goal_depth": goal_depth,
           "selfcheck": selfcheck,
           "seconds": round(time.time() - t0, 1),
           "mutated": args.mutate}
    emit(rec)
    print(json.dumps(rec, ensure_ascii=False), flush=True)
    if jl is not None:
        jl.close()
    if lv is not None:
        lv.close()
    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"summary": rec, "levels": results}, fh,
                      ensure_ascii=False, indent=2)
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
