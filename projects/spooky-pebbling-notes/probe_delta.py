#!/usr/bin/env python3
"""T_UG(n,s) - T_UP(n,s) の符号が反転する n を実測する（KSS Thm 4.11 の「±1」の中身）。

KSS は Lemma 4.9/4.10 から |T_UG - T_UP| <= 1 しか言っていない。符号を決めれば
Cor 4.12 の系が閉じ、厳密値が計算できるようになる。

    python3 probe_delta.py 5 13 16     # s=5 を n=13..16 で測る
    python3 probe_delta.py --all       # 手元の範囲をまとめて

結果は `delta.json` に追記する（再開できるように。既測の点は飛ばす）。
"""
from __future__ import annotations

import json
import sys
import time
from pathlib import Path

import kss

OUT = Path(__file__).resolve().parent / "delta.json"


def load() -> dict:
    return json.loads(OUT.read_text()) if OUT.exists() else {}


def save(d: dict) -> None:
    OUT.write_text(json.dumps(d, indent=1, sort_keys=True))


def probe(s: int, n: int, d: dict) -> None:
    key = f"{n},{s}"
    if key in d:
        print(f"  skip n={n} s={s}（既測: {d[key]}）", flush=True)
        return
    t0 = time.time()
    up = kss.T_UP(n, s)
    ug = kss.T_UG(n, s)
    delta = None if (up is None or ug is None) else ug - up
    d[key] = {"T_UP": up, "T_UG": ug, "delta": delta,
              "sec": round(time.time() - t0, 1)}
    save(d)
    print(f"  n={n} s={s}: T_UP={up} T_UG={ug} delta={delta} "
          f"({d[key]['sec']}s)", flush=True)


def main(argv: list[str]) -> int:
    d = load()
    if argv and argv[0] == "--all":
        jobs = [(s, n) for s in (2, 3, 4, 5) for n in range(1, 13)]
    else:
        s = int(argv[0])
        lo, hi = int(argv[1]), int(argv[2])
        jobs = [(s, n) for n in range(lo, hi + 1)]
    print(f"閾値の予想: theta(s) = s(s+1)/2 → "
          f"{ {s: s * (s + 1) // 2 for s in (2, 3, 4, 5, 6)} }", flush=True)
    for s, n in jobs:
        probe(s, n, d)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
