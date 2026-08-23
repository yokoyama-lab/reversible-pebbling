#!/usr/bin/env python3
r"""Q13 の**下界側の証人**を取り出す（2026-08-24）。

`n*(p) >= n` は「鎖 n 頂点を p ペブル・T=2n-1 でペブリングできる」という**存在**の主張。
SAT の解（各時刻のペブル集合）をそのまま保存すれば、主張は証人だけで閉じる。

このファイルは生成器。検査は `q13_verify_nstar.py`（CNF も本ファイルも使わない）。
"""
from __future__ import annotations
import argparse
import json
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from q2_cnf import build, line  # noqa: E402

NSTAR = {2: 2, 3: 4, 4: 7, 5: 11, 6: 17, 7: 25, 8: 35, 9: 47, 10: 62}


def model_for(n, p, T, workdir):
    par, sk = line(n)
    c = build(par, sk, p, T)
    path = os.path.join(workdir, f"w_n{n}_p{p}.cnf")
    c.dump(path)
    r = subprocess.run(["cadical", path, "-q"], capture_output=True, text=True, timeout=7200)
    if "s SATISFIABLE" not in r.stdout:
        return None
    lits = set()
    for ln in r.stdout.splitlines():
        if ln.startswith("v "):
            lits.update(int(x) for x in ln[2:].split())
    # 変数の割り当ては build() の x = [[c.new() ...] for v] と同じ順（v 優先、次に t）
    sched = [[1 if (v * (T + 1) + t + 1) in lits else 0 for v in range(n)]
             for t in range(T + 1)]
    return sched


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-o", default="data/q13_nstar_witness.json")
    a = ap.parse_args()
    out = {"family": "line", "note": "schedule[t][v] = 時刻 t に頂点 v にペブルがあるか",
           "nstar": {}, "witness": {}}
    with tempfile.TemporaryDirectory(dir="/work/tmp") as wd:
        for p, n in sorted(NSTAR.items()):
            T = 2 * n - 1
            s = model_for(n, p, T, wd)
            if s is None:
                print(f"p={p} n={n}: SAT にならない（前提が崩れている）")
                return 1
            out["nstar"][str(p)] = n
            out["witness"][str(p)] = {"n": n, "T": T, "peak_claim": p, "schedule": s}
            print(f"p={p}: n*(p)={n} の証人を取得（T={T}、ピーク {max(sum(r) for r in s)}）")
    with open(a.o, "w", encoding="utf-8") as f:
        json.dump(out, f, separators=(",", ":"))
    print(f"→ {a.o}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
