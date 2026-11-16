#!/usr/bin/env python3
"""night80r3_content_cmp.py — レベル集合の**中身**を第76夜の証書と突き合わせる.

幅（`night80r3_level_profile_cmp.py`）が合うだけなら「同じ個数の別の集合」でも通る。
ここは **集合そのもの**を比べる。

2 つの実装は**符号化が違う**ので、比べるには翻訳が要る:

| | 今夜（night80r2_quotbfs） | 第76夜の証書 |
|---|---|---|
| 頂点番号 | heap（根=1、子=2v,2v+1） | preorder（根=0、`lch=idx+1`, `rch=idx+1+S(m-1)`） |
| 正準形 | 部分木ごとに hash-cons した整数 id・子は **id の大小**で整列 | 再帰的なビット詰め・子は **符号の大小**で整列（大きい方を左） |

翻訳は「今夜の id → 代表配置（heap のビットマスク）→ preorder のビットマスク →
§1.2 の `canon`」。両者が**同じ Aut 軌道の集合**を持っているなら、翻訳後は
バイト列まで一致するはずである（証書は 16 バイト LE の狭義単調増加列）。

使い方:
    python3 tools/night80r3_content_cmp.py --h 7 --p 10 --depth 25
    python3 tools/night80r3_content_cmp.py --h 7 --p 10 --depth 6 --mutate 5   # 検出力の確認
"""

from __future__ import annotations

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__))))
from night80r2_quotbfs import Quotient  # noqa: E402

CERT_DIR = "/work/tmp/night76_cert/h7p10"


# ---- 第76夜 §1.2 の canon をそのまま書き写したもの（preorder・ビット詰め） ----

def S(m: int) -> int:
    return (1 << m) - 1


def cert_canon(s: int, idx: int, m: int) -> int:
    if m == 0:
        return 0
    if (s & (((1 << S(m)) - 1) << idx)) == 0:
        return 0
    b = (s >> idx) & 1
    if m == 1:
        return b
    L = cert_canon(s, idx + 1, m - 1)
    R = cert_canon(s, idx + 1 + S(m - 1), m - 1)
    if L < R:
        L, R = R, L
    return b | (L << 1) | (R << (1 + S(m - 1)))


# ---- heap 番号 → preorder 番号 ----

def heap_to_pre(h: int) -> dict[int, int]:
    """内部頂点の heap 番号 → preorder 添字。"""
    out: dict[int, int] = {}

    def go(v: int, m: int, idx: int) -> None:
        out[v] = idx
        if m > 1:
            go(2 * v, m - 1, idx + 1)
            go(2 * v + 1, m - 1, idx + 1 + S(m - 1))

    go(1, h, 0)
    return out


# ---- 今夜の id → heap のビットマスク（代表を 1 つ取る） ----

def expand(q: Quotient, j: int, i: int, v: int, acc: list[int]) -> None:
    if j == 0:
        return
    b, L, R, _ = q.info[j][i]
    if b:
        acc.append(v)
    expand(q, j - 1, L, 2 * v, acc)
    expand(q, j - 1, R, 2 * v + 1, acc)


def top_to_cert(q: Quotient, key: int, h2p: dict[int, int], h: int) -> int:
    b = key & 1
    L = (key >> 1) & 0xFFFFFFFF
    R = key >> 33
    acc: list[int] = []
    if b:
        acc.append(1)
    expand(q, h - 1, L, 2, acc)
    expand(q, h - 1, R, 3, acc)
    s = 0
    for v in acc:
        s |= 1 << h2p[v]
    return cert_canon(s, 0, h)


def read_level(cert_dir: str, d: int) -> list[int]:
    path = os.path.join(cert_dir, f"L{d:05d}.bin")
    with open(path, "rb") as fh:
        raw = fh.read()
    return [int.from_bytes(raw[i:i + 16], "little") for i in range(0, len(raw), 16)]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--depth", type=int, required=True, help="比べる最大の深さ")
    ap.add_argument("--cert-dir", default=CERT_DIR)
    ap.add_argument("--mutate", type=int, default=None,
                    help="指定した深さで自分の集合を 1 状態だけ壊す（検出力の確認）")
    ap.add_argument("--json", type=str)
    args = ap.parse_args()

    h, p = args.h, args.p
    q = Quotient(h, p)
    h2p = heap_to_pre(h)
    e = q.empty[h - 1]
    start = q.top_key(0, e, e)
    goal = q.top_key(1, e, e)

    results = []
    prev: set = set()
    cur = {start}
    d = 0
    ok_all = True
    while d <= args.depth:
        mine = sorted(top_to_cert(q, k, h2p, h) for k in cur)
        if args.mutate is not None and d == args.mutate and mine:
            mine[0] ^= 1          # 1 bit 反転（根のビット）
            mine = sorted(mine)
        theirs = read_level(args.cert_dir, d)
        same = mine == theirs
        ok_all = ok_all and same
        results.append({"depth": d, "mine": len(mine), "cert": len(theirs),
                        "identical": same})
        if not same:
            diff_mine = set(mine) - set(theirs)
            diff_cert = set(theirs) - set(mine)
            results[-1]["only_mine"] = len(diff_mine)
            results[-1]["only_cert"] = len(diff_cert)
            print(f"NG depth={d}: 幅 {len(mine)} vs {len(theirs)}・"
                  f"こちらだけ {len(diff_mine)}・証書だけ {len(diff_cert)}",
                  file=sys.stderr)
        if d == args.depth:
            break
        nxt = set()
        for s in cur:
            for t in q.succ_top(s):
                if t not in cur and t not in prev:
                    nxt.add(t)
        if goal in nxt:
            print(f"goal を深さ {d + 1} で踏んだ（比較は打ち切り）", file=sys.stderr)
            break
        prev, cur = cur, nxt
        d += 1

    rec = {"h": h, "p": p, "depth_max": args.depth, "mutated": args.mutate,
           "levels_compared": len(results),
           "levels_identical": sum(1 for r in results if r["identical"]),
           "all_identical": ok_all,
           "states_compared": sum(r["cert"] for r in results),
           "levels": results}
    print(json.dumps(rec, ensure_ascii=False, indent=2)[:4000])
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(rec, fh, ensure_ascii=False, indent=2)
    return 0 if ok_all else 1


if __name__ == "__main__":
    sys.exit(main())
