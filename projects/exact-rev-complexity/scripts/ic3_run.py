#!/usr/bin/env python3
"""`ic3_pyramid.py` の遷移系を ABC の `pdr` と nuXmv の `check_invar_ic3` に掛け、
**PROVED / CEX / TIMEOUT を書き分けて**記録する（notes/ic3/REQUEST.md）。

判定の意味（有限状態系なので 3 通りしかない）:
  PROVED  … bad は到達不能。帰納的不変量が構成された ⇒ p_min(P_h) > p
  CEX     … bad へ到達する具体列がある ⇒ p_min(P_h) <= p
  TIMEOUT … 資源上限に当たった。**下界の根拠にならない**（打ち切り）
  ERROR   … 道具が異常終了

使い方:
  ic3_run.py --h 8 --p 19 --tool abc   --timeout 600 --mem 8
  ic3_run.py --h 8 --p 19 --tool nuxmv --timeout 600 --mem 8
  ic3_run.py --sweep 8,9,10 --tool abc --timeout 600     # p_min-1 と p_min の対
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ic3_pyramid import Model, build_aig, build_smv, PMIN  # noqa: E402

SCRATCH = os.environ.get(
    "IC3_SCRATCH",
    "/work/tmp/claude-1000/-work-a-dev-github-com-tetsuo-jp-exact-rev-complexity-"
    "notes-ic3/475e0dbf-41a6-49b8-baeb-071ae7ceb4c1/scratchpad/ic3")


def runcap(cmd: list[str], timeout: int, mem: int, name: str):
    """runcap を掛けて実行し、(stdout+stderr, 経過秒, runcap の報告行) を返す。"""
    full = ["runcap", "-m", str(mem), "-t", str(timeout), "-n", name, "--"] + cmd
    t0 = time.time()
    r = subprocess.run(full, capture_output=True, text=True)
    return r.stdout + r.stderr, time.time() - t0, r.returncode


def run_abc(h: int, p: int, timeout: int, mem: int) -> dict:
    os.makedirs(SCRATCH, exist_ok=True)
    m = Model(h, p)
    aig = f"{SCRATCH}/pyr_h{h}_p{p}.aig"
    inv = f"{SCRATCH}/pyr_h{h}_p{p}.inv"
    g, _ = build_aig(m)
    g.write_aig(aig)
    script = f"read_aiger {aig}; print_stats; pdr -v -d -I {inv} -T {timeout}"
    out, el, rc = runcap(["abc", "-q", script], timeout + 120, mem,
                         f"ic3-abc-h{h}p{p}")
    verdict = "TIMEOUT"
    if "Property proved" in out:
        verdict = "PROVED"
    elif "was asserted in frame" in out:
        verdict = "CEX"
    elif rc != 0 and "Reached timeout" not in out and "UNDECIDED" not in out:
        verdict = "TIMEOUT" if "runcap" in out.lower() else "ERROR"
    frames = [int(x) for x in re.findall(r"^ *(\d+) :", out, re.M)]
    ncl = None
    mo = re.search(r"Invariant F\[\d+\] : (\d+) clauses with (\d+) flops", out)
    if mo:
        ncl = (int(mo.group(1)), int(mo.group(2)))
    return {"tool": "abc", "h": h, "p": p, "verdict": verdict, "sec": round(el, 1),
            "max_frame": max(frames) if frames else None,
            "inv_clauses": ncl, "latches": g.nl, "ands": len(g.ands),
            "log": out[-4000:]}


def run_nuxmv(h: int, p: int, timeout: int, mem: int) -> dict:
    os.makedirs(SCRATCH, exist_ok=True)
    m = Model(h, p)
    smv = f"{SCRATCH}/pyr_h{h}_p{p}.smv"
    with open(smv, "w") as f:
        f.write(build_smv(m))
    cmds = f"{SCRATCH}/pyr_h{h}_p{p}.cmd"
    with open(cmds, "w") as f:
        f.write("go_msat\ncheck_invar_ic3\nquit\n")
    out, el, rc = runcap(["nuXmv", "-source", cmds, smv], timeout, mem,
                         f"ic3-nux-h{h}p{p}")
    verdict = "TIMEOUT"
    if re.search(r"invariant .* is true", out):
        verdict = "PROVED"
    elif re.search(r"invariant .* is false", out):
        verdict = "CEX"
    elif "error" in out.lower() and "no proof" not in out:
        verdict = "ERROR"
    bounds = [int(x) for x in re.findall(r"no proof or counterexample found with bound (\d+)", out)]
    return {"tool": "nuxmv", "h": h, "p": p, "verdict": verdict, "sec": round(el, 1),
            "max_frame": max(bounds) if bounds else None,
            "inv_clauses": None, "latches": None, "ands": None,
            "log": out[-4000:]}


RUN = {"abc": run_abc, "nuxmv": run_nuxmv}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int)
    ap.add_argument("--p", type=int)
    ap.add_argument("--sweep", help="h のコンマ区切り。各 h で p_min-1 と p_min を試す")
    ap.add_argument("--ps", help="p のコンマ区切り（--h と併用）")
    ap.add_argument("--tool", choices=list(RUN), required=True)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--mem", type=int, default=8)
    ap.add_argument("--jsonl", help="結果を追記する JSONL")
    a = ap.parse_args()

    jobs = []
    if a.sweep:
        for h in [int(x) for x in a.sweep.split(",")]:
            jobs += [(h, PMIN[h] - 1), (h, PMIN[h])]
    elif a.ps:
        jobs = [(a.h, int(x)) for x in a.ps.split(",")]
    else:
        jobs = [(a.h, a.p)]

    for h, p in jobs:
        r = RUN[a.tool](h, p, a.timeout, a.mem)
        line = (f"{r['tool']:6s} h={h:2d} p={p:3d}  {r['verdict']:8s} "
                f"{r['sec']:8.1f}s  frame={r['max_frame']}  inv={r['inv_clauses']}")
        print(line, flush=True)
        if a.jsonl:
            with open(a.jsonl, "a") as f:
                f.write(json.dumps(r, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    main()
