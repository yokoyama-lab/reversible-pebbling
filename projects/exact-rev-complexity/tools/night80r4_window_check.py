#!/usr/bin/env python3
"""night80r4_window_check.py — 証書の**深い側**を、BFS を頭から回さずに検査する.

## なぜ別の筋か

周 3 は「頭から BFS を回して深さ 0..22 の中身を証書と突き合わせる」だった。
だが $M^*(T_7,10)\\ge 1001$ を担っているのは**深さ 1000 の側**である。
深い側へ伸ばすには毎回 44 分の BFS を頭から回すことになり、1 周で数レベルしか伸びない。

観察: レベル集合の証書は**局所的に検査できる**。無向な状態グラフでは

    L_{d+1} = succ(L_d) \\ (L_{d-1} ∪ L_d)

が成り立つ。したがって $L_{d-1}, L_d, L_{d+1}$ の 3 本だけを読めば、深さ $d$ の
1 歩を**それ単独で**検査できる。頭から回す必要はない。

ここでやること（すべて周 2 の独立実装 `night80r2_quotbfs.Quotient` の遷移関係で）:

1. **往復**: 証書の値 → こちらの id（`decode`）→ 証書の値（`FastTrans.top`）が
   元に戻るか。戻れば、その値は**こちらの正準化から見ても**正準な代表である。
   ついでにペブル数 $\\le p$ も `Quotient.canon` が機械的に見る（超過は -1）。
2. **単調増加**: 各ファイルが狭義単調増加（＝重複なし）。
3. **1 歩**: 上の等式を窓の各深さで検査する。
4. **goal 走査**: goal の証書値を全 1001 本から二分探索で探す（**不在**が主張）。
   対照として、実在する値（各ファイルの先頭）が**見つかる**ことも確かめる。
5. **上界側**: 深さ 1000 の 1 歩に goal が現れるか（現れれば $M^* \\le 1001$）。

使い方:
    python3 tools/night80r4_window_check.py --h 7 --p 10 --from 996 --to 1000 \\
        --goal-scan --jsonl autoresearch/results/night80r4_window.jsonl
    python3 tools/night80r4_window_check.py --h 7 --p 10 --from 20 --to 22 --mutate 21
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from night80r2_quotbfs import Quotient  # noqa: E402
from night80r4_content_deep import FastTrans  # noqa: E402

CERT_DIR = "/work/tmp/night76_cert/h7p10"
REC = 16  # 1 状態 = 16 バイト LE


def cert_path(cert_dir: str, d: int) -> str:
    return os.path.join(cert_dir, f"L{d:05d}.bin")


def read_level(cert_dir: str, d: int) -> list[int]:
    with open(cert_path(cert_dir, d), "rb") as fh:
        raw = fh.read()
    return [int.from_bytes(raw[i:i + REC], "little") for i in range(0, len(raw), REC)]


def level_size(cert_dir: str, d: int) -> int:
    return os.path.getsize(cert_path(cert_dir, d)) // REC


def find_in_level(cert_dir: str, d: int, v: int) -> bool:
    """狭義単調増加のファイルを二分探索する（読むのは O(log n) レコードだけ）."""
    n = level_size(cert_dir, d)
    lo, hi = 0, n - 1
    with open(cert_path(cert_dir, d), "rb") as fh:
        while lo <= hi:
            mid = (lo + hi) // 2
            fh.seek(mid * REC)
            x = int.from_bytes(fh.read(REC), "little")
            if x == v:
                return True
            if x < v:
                lo = mid + 1
            else:
                hi = mid - 1
    return False


class Decoder:
    """証書の canon 値 → こちらの正準 id（部分木ごとに memo 化）."""

    def __init__(self, q: Quotient, memo_max: int):
        self.q = q
        self.memo_max = memo_max
        self.memo = [dict() for _ in range(q.h + 1)]

    def dec(self, v: int, m: int) -> int:
        if m == 0:
            return 0
        memo = self.memo[m] if m <= self.memo_max else None
        if memo is not None:
            got = memo.get(v)
            if got is not None:
                return got
        s = (1 << (m - 1)) - 1          # S(m-1)
        mask = (1 << s) - 1
        L = self.dec((v >> 1) & mask, m - 1)
        R = self.dec((v >> (1 + s)) & mask, m - 1)
        out = -1 if (L < 0 or R < 0) else self.q.canon(m, v & 1, L, R)
        if memo is not None:
            memo[v] = out
        return out

    def top_key(self, v: int) -> int:
        """全体（高さ h）の証書値 → 最上段の鍵。-1 なら p 超過。"""
        h = self.q.h
        s = (1 << (h - 1)) - 1
        mask = (1 << s) - 1
        L = self.dec((v >> 1) & mask, h - 1)
        R = self.dec((v >> (1 + s)) & mask, h - 1)
        if L < 0 or R < 0:
            return -1
        return self.q.top_key(v & 1, L, R)


def load_keys(dec: Decoder, tr: FastTrans, cert_dir: str, d: int,
              roundtrip: bool, flip: bool = False) -> tuple[set, dict]:
    """深さ d の証書を読み、こちらの鍵の集合にする（往復と単調増加も見る）."""
    t0 = time.time()
    vals = read_level(cert_dir, d)
    if flip and vals:
        # ⚠ 検出力の確認用。1 状態の 1 ビットを反転する（根のビット）
        vals[len(vals) // 2] ^= 1
        vals.sort()
    mono = all(vals[i] < vals[i + 1] for i in range(len(vals) - 1))
    keys = set()
    bad_decode = 0
    bad_rt = 0
    for v in vals:
        k = dec.top_key(v)
        if k < 0:
            bad_decode += 1
            continue
        if roundtrip and tr.top(k) != v:
            bad_rt += 1
        keys.add(k)
    info = {"depth": d, "cert": len(vals), "keys": len(keys),
            "monotone": mono, "bad_decode": bad_decode,
            "bad_roundtrip": bad_rt, "sec": round(time.time() - t0, 1)}
    return keys, info


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--from", dest="d_from", type=int, required=True)
    ap.add_argument("--to", dest="d_to", type=int, required=True)
    ap.add_argument("--cert-dir", default=CERT_DIR)
    ap.add_argument("--memo-max", type=int, default=None)
    ap.add_argument("--no-roundtrip", action="store_true")
    ap.add_argument("--goal-scan", action="store_true",
                    help="全レベルを二分探索して goal の不在を確かめる")
    ap.add_argument("--goal-scan-max", type=int, default=1000)
    ap.add_argument("--mutate", type=int, default=None,
                    help="この深さの証書から 1 状態を落として読む（検出力の確認）")
    ap.add_argument("--mutate-flip", type=int, default=None,
                    help="この深さの証書の 1 状態を 1 ビット反転して読む（同上）")
    ap.add_argument("--jsonl", type=str)
    ap.add_argument("--json", type=str)
    args = ap.parse_args()

    h, p = args.h, args.p
    memo_max = args.memo_max if args.memo_max is not None else max(1, h - 2)
    q = Quotient(h, p)
    tr = FastTrans(q, memo_max)
    dec = Decoder(q, memo_max)
    e = q.empty[h - 1]
    goal_key = q.top_key(1, e, e)
    goal_cert = tr.top(goal_key)

    jl = open(args.jsonl, "w") if args.jsonl else None
    out: dict = {"h": h, "p": p, "from": args.d_from, "to": args.d_to,
                 "goal_cert": str(goal_cert), "mutate": args.mutate,
                 "mutate_flip": args.mutate_flip}
    t0 = time.time()

    def emit(rec: dict) -> None:
        print(json.dumps(rec, ensure_ascii=False), flush=True)
        if jl is not None:
            jl.write(json.dumps(rec, ensure_ascii=False) + "\n")
            jl.flush()

    emit({"kind": "meta", **out})
    ok = True

    # ---- 4. goal 走査（全レベル・二分探索） ----
    if args.goal_scan:
        ts = time.time()
        hits = [d for d in range(0, args.goal_scan_max + 1)
                if find_in_level(args.cert_dir, d, goal_cert)]
        # 対照: 各レベルの先頭の値は必ず見つかるはず（探索が動いていることの証拠）
        ctrl_bad = []
        for d in range(0, args.goal_scan_max + 1, 97):
            with open(cert_path(args.cert_dir, d), "rb") as fh:
                first = int.from_bytes(fh.read(REC), "little")
            if not find_in_level(args.cert_dir, d, first):
                ctrl_bad.append(d)
        rec = {"kind": "goal_scan", "levels": args.goal_scan_max + 1,
               "goal_found_at": hits, "control_levels": len(range(0, args.goal_scan_max + 1, 97)),
               "control_failed": ctrl_bad, "sec": round(time.time() - ts, 1)}
        ok = ok and not hits and not ctrl_bad
        out["goal_scan"] = rec
        emit(rec)

    # ---- 1〜3. 窓の 1 歩検査 ----
    steps = []
    cache: dict[int, set] = {}
    infos = []

    def level(d: int) -> set:
        if d not in cache:
            keys, info = load_keys(dec, tr, args.cert_dir, d,
                                   not args.no_roundtrip,
                                   flip=(args.mutate_flip == d))
            if args.mutate is not None and d == args.mutate and keys:
                keys.discard(sorted(keys)[0])    # 1 状態落とす
                info["mutated_drop"] = 1
            infos.append(info)
            emit({"kind": "load", **info})
            if not info["monotone"] or info["bad_decode"] or info["bad_roundtrip"]:
                nonlocal_ok[0] = False
            cache[d] = keys
            for k in list(cache):
                if k < d - 2:
                    del cache[k]
        return cache[d]

    nonlocal_ok = [True]
    nmax = args.goal_scan_max
    for d in range(args.d_from, args.d_to + 1):
        ts = time.time()
        prev = level(d - 1) if d >= 1 else set()
        curr = level(d)
        nxt = set()
        for s in curr:
            for t in q.succ_top(s):
                if t not in curr and t not in prev:
                    nxt.add(t)
        goal_here = goal_key in nxt
        rec = {"kind": "step", "depth": d, "computed_next": len(nxt),
               "goal_in_next": goal_here}
        if d == 0:
            # 連鎖の錨: 証書の L_0 がこちらの始状態（空配置）ちょうどか
            anchor = curr == {q.top_key(0, e, e)}
            rec["anchor_L0_is_start"] = anchor
            ok = ok and anchor
        if d + 1 <= nmax:
            want = level(d + 1)
            same = nxt == want
            rec.update({"cert_next": len(want), "identical": same,
                        "only_computed": len(nxt - want),
                        "only_cert": len(want - nxt)})
            ok = ok and same
        rec["sec"] = round(time.time() - ts, 1)
        rec["elapsed"] = round(time.time() - t0, 1)
        steps.append(rec)
        emit(rec)

    ok = ok and nonlocal_ok[0]
    summary = {"kind": "summary", **out,
               "steps": len(steps),
               "steps_identical": sum(1 for s in steps if s.get("identical")),
               "levels_loaded": len(infos),
               "states_loaded": sum(i["cert"] for i in infos),
               "bad_decode": sum(i["bad_decode"] for i in infos),
               "bad_roundtrip": sum(i["bad_roundtrip"] for i in infos),
               "all_monotone": all(i["monotone"] for i in infos),
               "goal_in_next_at": [s["depth"] for s in steps if s["goal_in_next"]],
               "ok": ok, "seconds": round(time.time() - t0, 1)}
    emit(summary)
    if jl is not None:
        jl.close()
    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"summary": summary, "steps": steps, "loads": infos},
                      fh, ensure_ascii=False, indent=2)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
