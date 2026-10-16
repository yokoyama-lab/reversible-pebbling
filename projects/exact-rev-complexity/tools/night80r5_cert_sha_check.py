#!/usr/bin/env python3
"""night80r5_cert_sha_check.py — 今夜検査した証書が、第76夜が記録した現物と同じかを確かめる.

今夜（第80夜 周 5）の鎖の検査は `/work/tmp/night76_cert/h7p10` の実体を読む。
リポジトリに在るのは `autoresearch/results/night76_cert_h7p10/SHA256SUMS`（1002 行）だけで、
**実体が途中で書き換わっていたら、今夜の一致は何も意味しない**。
そこで実体の SHA-256 を取り直し、記録と 1 行ずつ突き合わせる。

⚠ 検出力: `--mutate <d>` を付けると深さ d のファイルの 1 バイトを（読み込みの途中で）
   反転した上で計算する。**ファイルには書き戻さない**（証書は読み取り専用で扱う）。

使い方:
    python3 -I tools/night80r5_cert_sha_check.py --json autoresearch/results/night80r5_cert_sha.json
    python3 -I tools/night80r5_cert_sha_check.py --mutate 500   （検出力の確認）
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import time

CERT_DIR = "/work/tmp/night76_cert/h7p10"
SUMS = "autoresearch/results/night76_cert_h7p10/SHA256SUMS"
BLK = 1 << 22


def digest(path: str, mutate: bool) -> str:
    h = hashlib.sha256()
    first = True
    with open(path, "rb") as fh:
        while True:
            b = fh.read(BLK)
            if not b:
                break
            if mutate and first:
                b = bytes([b[0] ^ 1]) + b[1:]
                first = False
            h.update(b)
    return h.hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cert-dir", default=CERT_DIR)
    ap.add_argument("--sums", default=SUMS)
    ap.add_argument("--mutate", type=int, default=None)
    ap.add_argument("--json", type=str)
    args = ap.parse_args()

    want: dict[str, str] = {}
    for line in open(args.sums):
        line = line.strip()
        if not line:
            continue
        sha, name = line.split(None, 1)
        want[name.strip()] = sha

    t0 = time.time()
    checked = 0
    missing: list[str] = []
    mismatch: list[str] = []
    nbytes = 0
    mut_name = "L%05d.bin" % args.mutate if args.mutate is not None else None
    for name, sha in sorted(want.items()):
        if name == "meta.json":
            path = os.path.join(os.path.dirname(args.sums), name)
            if not os.path.exists(path):
                path = os.path.join(args.cert_dir, name)
        else:
            path = os.path.join(args.cert_dir, name)
        if not os.path.exists(path):
            missing.append(name)
            continue
        nbytes += os.path.getsize(path)
        got = digest(path, mutate=(name == mut_name))
        checked += 1
        if got != sha:
            mismatch.append(name)

    out = {"kind": "cert_sha_check", "cert_dir": args.cert_dir,
           "files_in_sums": len(want), "checked": checked,
           "missing": missing[:10], "missing_n": len(missing),
           "mismatch": mismatch[:10], "mismatch_n": len(mismatch),
           "bytes": nbytes, "mutate": args.mutate,
           "seconds": round(time.time() - t0, 1),
           "ok": not missing and not mismatch and checked == len(want)}
    print(json.dumps(out, ensure_ascii=False, indent=2))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(out, fh, ensure_ascii=False, indent=2)
    return 0 if out["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
