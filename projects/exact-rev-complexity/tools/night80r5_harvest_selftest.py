#!/usr/bin/env python3
"""night80r5_harvest_selftest.py — 収穫（harvest）の検出力を変異注入で測る.

周 4 の検査器（`night80r4_window_check.py`）は変異注入で検出力を確かめてある。
**今夜新しく書いたのは「帯の出力を鎖として繋ぐ」側**（`night80r5_chain_shard.harvest`）で、
ここが甘いと「帯が 1 つ落ちているのに緑」が起きる。**落ちる所を先に測る。**

やり方: 小さな**合成の**帯出力（深さ 0..3 の 4 歩を 2 帯に割ったもの）を作り、
無変異で `ok` が真になることを見てから、1 件ずつ壊して `ok` が偽になることを見る。
壊し方は、実際に起きうる事故に対応させた:

  drop_step      1 歩の記録が無い（worker が途中で死んだ）
  not_identical  1 歩が食い違っている（証書が違う）
  band_gone      帯のファイルごと無い（起動していない／消えた）
  truncated      summary 行が無い（打ち切り。歩の記録は途中まで在る）
  bad_roundtrip  往復に失敗した状態がある
  not_monotone   証書が狭義単調増加でない（重複）
  goal_misplaced goal が最深以外の深さで現れる（＝下界が壊れる）
  goal_absent    最深の歩に goal が現れない（＝上界が壊れる）
  anchor_false   深さ 0 の錨が偽（始状態が違う）

使い方: python3 -I tools/night80r5_harvest_selftest.py [--outdir DIR]
終了コード 0 = 無変異が緑かつ**全変異が検出された**。
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from night80r5_chain_shard import harvest  # noqa: E402

D_TO = 3
BANDS = [(0, 1), (2, 3)]


def load_rec(d: int, n: int, **kw) -> dict:
    rec = {"kind": "load", "depth": d, "cert": n, "keys": n, "monotone": True,
           "bad_decode": 0, "bad_roundtrip": 0, "sec": 0.0}
    rec.update(kw)
    return rec


def step_rec(d: int, n: int, goal: bool = False, identical: bool = True,
             last: bool = False) -> dict:
    rec = {"kind": "step", "depth": d, "computed_next": n, "goal_in_next": goal}
    if d == 0:
        rec["anchor_L0_is_start"] = True
    if not last:
        rec.update({"cert_next": n, "identical": identical,
                    "only_computed": 0, "only_cert": 0})
    rec["sec"] = 0.0
    return rec


def write_bands(outdir: str, mutation: str | None) -> None:
    """合成の帯出力を書く（mutation に応じて 1 箇所だけ壊す）."""
    if os.path.isdir(outdir):
        shutil.rmtree(outdir)
    os.makedirs(outdir)
    sizes = {0: 1, 1: 1, 2: 6, 3: 16, 4: 61}
    for (a, b) in BANDS:
        if mutation == "band_gone" and (a, b) == (2, 3):
            continue
        recs: list[dict] = [{"kind": "meta", "h": 7, "p": 10, "from": a, "to": b,
                             "goal_cert": "1", "mutate": None, "mutate_flip": None}]
        for d in range(a, b + 1):
            lo = max(0, a - 1) if d == a else d
            for dd in range(lo, min(d + 1, D_TO) + 1):
                if any(r.get("kind") == "load" and r["depth"] == dd for r in recs):
                    continue
                kw = {}
                if mutation == "bad_roundtrip" and dd == 2:
                    kw["bad_roundtrip"] = 1
                if mutation == "not_monotone" and dd == 2:
                    kw["monotone"] = False
                if mutation == "keys_lt_cert" and dd == 2:
                    kw["keys"] = sizes[dd] - 1
                recs.append(load_rec(dd, sizes[dd], **kw))
            last = (d == D_TO)
            goal = last
            ident = True
            if mutation == "not_identical" and d == 2:
                ident = False
            if mutation == "goal_misplaced" and d == 1:
                goal = True
            if mutation == "goal_absent" and last:
                goal = False
            rec = step_rec(d, sizes[min(d + 1, 4)], goal=goal, identical=ident, last=last)
            if mutation == "anchor_false" and d == 0:
                rec["anchor_L0_is_start"] = False
            if mutation == "drop_step" and d == 2:
                continue
            recs.append(rec)
        if not (mutation == "truncated" and (a, b) == (2, 3)):
            recs.append({"kind": "summary", "h": 7, "p": 10, "from": a, "to": b,
                         "ok": True})
        stem = os.path.join(outdir, "band_%04d_%04d" % (a, b))
        with open(stem + ".jsonl", "w") as fh:
            for r in recs:
                fh.write(json.dumps(r, ensure_ascii=False) + "\n")
        with open(stem + ".json", "w") as fh:
            json.dump({"summary": recs[-1]}, fh)


MUTATIONS = ["drop_step", "not_identical", "band_gone", "truncated",
             "bad_roundtrip", "not_monotone", "keys_lt_cert", "goal_misplaced",
             "goal_absent", "anchor_false"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", default="autoresearch/results/night80r5_selftest")
    ap.add_argument("--json", default=None)
    args = ap.parse_args()

    results = []
    write_bands(args.outdir, None)
    base = harvest(7, 10, args.outdir, 0, D_TO, BANDS)
    results.append({"mutation": None, "ok": base["ok"], "expected_ok": True})
    for m in MUTATIONS:
        write_bands(args.outdir, m)
        got = harvest(7, 10, args.outdir, 0, D_TO, BANDS)
        results.append({"mutation": m, "ok": got["ok"], "expected_ok": False,
                        "why": {k: got[k] for k in
                                ("steps_missing_n", "steps_not_identical_n",
                                 "bands_incomplete", "bad_loads_n", "all_monotone",
                                 "anchor_L0_is_start", "goal_in_next_at")}})
    write_bands(args.outdir, None)   # 片付け: 無変異の状態に戻す

    detected = sum(1 for r in results[1:] if r["ok"] is False)
    out = {"baseline_ok": base["ok"], "mutations": len(MUTATIONS),
           "detected": detected, "results": results,
           "ok": base["ok"] is True and detected == len(MUTATIONS)}
    print(json.dumps(out, ensure_ascii=False, indent=2))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(out, fh, ensure_ascii=False, indent=2)
    return 0 if out["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
