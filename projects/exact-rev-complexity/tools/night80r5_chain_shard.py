#!/usr/bin/env python3
"""night80r5_chain_shard.py — 証書 L_0..L_1000 の 1 歩検査を**帯に割って並列に**回す.

## なぜ

周 4 が立てた観察「L_{d+1} = succ(L_d) \\ (L_{d-1} ∪ L_d) は L_{d-1},L_d,L_{d+1} の
3 本だけで検査できる」は、**各深さの検査が互いに独立**であることを同時に意味する。
周 4 はそれを「好きな深さへ降りられる」ことにだけ使い、鎖は 1 本の直列 run に任せた。
その run は実測 14.9 μs/状態 ×  3.40 億状態 ＝ **約 85 分**かかり、夜の残りに収まらない。

ここでやること: 深さ 0..1000 を**仕事量（レベル幅の和）で均した帯**に割り、
各帯を**周 4 の検査器そのまま**（`night80r4_window_check.py`）で別プロセスとして回す。
検査の中身は 1 行も変えていない（変異注入で検出力を測ったのはあの検査器である）。

収穫（harvest）では各帯の出力を読み、

* 深さ 0..999 の 1 歩が**全部そろっているか**（重複・欠落を帯の境目で検査する）
* すべての歩で `identical` が真か
* `bad_decode` / `bad_roundtrip` が 0・`monotone` が全真か
* 深さ 0 の**錨**（証書の L_0 がこちらの始状態ちょうど）が真か
* `goal_in_next` が真になる深さが **1000 ちょうど**か（下界と上界の両側）

を機械で確かめ、1 つの summary にまとめる。**帯が 1 つでも欠けたら ok は偽**。

使い方:
    python3 -I tools/night80r5_chain_shard.py --h 7 --p 10 --workers 5 \\
        --outdir autoresearch/results/night80r5_bands \\
        --summary autoresearch/results/night80r5_chain_summary.json
    python3 -I tools/night80r5_chain_shard.py --harvest-only ...（走らせずに収穫だけ）

⚠ 途中で打ち切られても、済んだ帯の `.json` は残る。同じコマンドを再実行すると
   **済んだ帯は飛ばす**（resumable）。収穫は済んだ帯だけで行い、欠けを明示する。
"""

from __future__ import annotations

import argparse
import json
import os
import resource
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CERT_DIR = "/work/tmp/night76_cert/h7p10"
REC = 16
CHECKER = os.path.join(HERE, "night80r4_window_check.py")


def widths(cert_dir: str, dmax: int) -> list[int]:
    out = []
    for d in range(dmax + 1):
        p = os.path.join(cert_dir, "L%05d.bin" % d)
        out.append(os.path.getsize(p) // REC if os.path.exists(p) else 0)
    return out


def split_bands(w: list[int], d_from: int, d_to: int, cap: int) -> list[tuple[int, int]]:
    """仕事量（帯が触るレベル幅の和）が cap を超えないように [a,b] へ割る。"""
    bands = []
    a = d_from
    load = w[max(0, a - 1)] + w[a]
    for b in range(d_from, d_to + 1):
        nxt = w[b + 1] if b + 1 < len(w) else 0
        if b > a and load + nxt > cap:
            bands.append((a, b - 1))
            a = b
            load = w[max(0, a - 1)] + w[a] + (w[a + 1] if a + 1 < len(w) else 0)
        else:
            load += nxt
    bands.append((a, d_to))
    return bands


def bands_on_disk(outdir: str) -> list[tuple[int, int]]:
    """outdir に実在する帯を拾う（収穫は割り方の再計算ではなく現物に従う）.

    ⚠ ここを「割り方を計算し直す」で書くと、cap を変えただけで**全部欠落**に見える。
       2026-10-11 周 5 に実際にやった。
    """
    out = []
    if not os.path.isdir(outdir):
        return out
    for name in os.listdir(outdir):
        if name.startswith("band_") and name.endswith(".jsonl"):
            stem = name[len("band_"):-len(".jsonl")]
            try:
                a, b = (int(x) for x in stem.split("_"))
            except ValueError:
                continue
            out.append((a, b))
    return sorted(out)


def band_paths(outdir: str, a: int, b: int) -> tuple[str, str, str]:
    stem = os.path.join(outdir, "band_%04d_%04d" % (a, b))
    return stem + ".jsonl", stem + ".json", stem + ".log"


def band_done(outdir: str, a: int, b: int) -> dict | None:
    _, js, _ = band_paths(outdir, a, b)
    if not os.path.exists(js) or os.path.getsize(js) == 0:
        return None
    try:
        with open(js) as fh:
            return json.load(fh)
    except Exception:
        return None


def launch(h: int, p: int, a: int, b: int, outdir: str, cert_dir: str,
           as_gb: float) -> tuple[subprocess.Popen, object]:
    jl, js, lg = band_paths(outdir, a, b)
    cmd = [sys.executable, "-I", CHECKER, "--h", str(h), "--p", str(p),
           "--from", str(a), "--to", str(b), "--cert-dir", cert_dir,
           "--jsonl", jl, "--json", js]
    lim = int(as_gb * (1 << 30))

    def pre() -> None:
        resource.setrlimit(resource.RLIMIT_AS, (lim, lim))

    fh = open(lg, "w")
    proc = subprocess.Popen(cmd, stdout=fh, stderr=subprocess.STDOUT,
                            preexec_fn=pre, cwd=os.path.dirname(HERE))
    return proc, fh


def harvest(h: int, p: int, outdir: str, d_from: int, d_to: int,
            bands: list[tuple[int, int]]) -> dict:
    """帯の出力を読み、鎖として繋がっているかを機械で確かめる。"""
    steps: dict[int, dict] = {}
    dup: list[int] = []
    loads: dict[int, dict] = {}
    bad_load: list[dict] = []
    missing_bands: list[list[int]] = []
    goal_cert = None
    goal_cert_disagree = []

    for (a, b) in bands:
        jl, js, _ = band_paths(outdir, a, b)
        if not os.path.exists(jl):
            missing_bands.append([a, b])
            continue
        saw_summary = False
        with open(jl) as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    rec = json.loads(line)
                except Exception:
                    continue
                k = rec.get("kind")
                if k == "meta":
                    if goal_cert is None:
                        goal_cert = rec.get("goal_cert")
                    elif rec.get("goal_cert") != goal_cert:
                        goal_cert_disagree.append([a, b, rec.get("goal_cert")])
                elif k == "load":
                    d = rec["depth"]
                    # keys != cert なら復号が単射でない（別の証書値が同じ鍵に落ちた）。
                    # 往復検査が捕まえるはずだが、数でも独立に見ておく。
                    if (rec.get("bad_decode") or rec.get("bad_roundtrip")
                            or not rec.get("monotone")
                            or rec.get("keys") != rec.get("cert")):
                        bad_load.append(rec)
                    prev = loads.get(d)
                    if prev is None or rec["cert"] > prev.get("cert", -1):
                        loads[d] = rec
                elif k == "step":
                    d = rec["depth"]
                    if d in steps:
                        dup.append(d)
                    steps[d] = rec
                elif k == "summary":
                    saw_summary = True
        if not saw_summary:
            missing_bands.append([a, b])

    want = set(range(d_from, d_to + 1))
    have = set(steps)
    missing = sorted(want - have)
    # ⚠ 最深の歩（d = d_to）には比べる相手 L_{d_to+1} が無い（証書は L_0..L_1000）。
    #    そこで見るのは `identical` ではなく `goal_in_next` の側である。
    not_identical = sorted(d for d, r in steps.items()
                           if d < d_to and not r.get("identical"))
    goal_at = sorted(d for d, r in steps.items() if r.get("goal_in_next"))
    anchor = steps.get(0, {}).get("anchor_L0_is_start")
    states = sum(r.get("cert", 0) for r in loads.values())

    ok = (not missing and not not_identical and not bad_load and not missing_bands
          and not goal_cert_disagree and goal_at == [d_to] and anchor is True)
    return {
        "kind": "chain_summary", "h": h, "p": p, "from": d_from, "to": d_to,
        "bands": len(bands), "bands_incomplete": missing_bands,
        "steps_checked": len(steps), "steps_expected": len(want),
        "steps_identical_n": sum(1 for r in steps.values() if r.get("identical")),
        "steps_missing": missing[:20], "steps_missing_n": len(missing),
        "steps_duplicated_n": len(dup),
        "steps_not_identical": not_identical[:20],
        "steps_not_identical_n": len(not_identical),
        "levels_loaded": len(loads), "states_loaded": states,
        "bad_loads": bad_load[:5], "bad_loads_n": len(bad_load),
        "all_monotone": all(r.get("monotone") for r in loads.values()) if loads else False,
        "anchor_L0_is_start": anchor,
        "goal_cert": goal_cert, "goal_cert_disagree": goal_cert_disagree,
        "goal_in_next_at": goal_at,
        "ok": ok,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int, default=7)
    ap.add_argument("--p", type=int, default=10)
    ap.add_argument("--from", dest="d_from", type=int, default=0)
    ap.add_argument("--to", dest="d_to", type=int, default=1000)
    ap.add_argument("--cert-dir", default=CERT_DIR)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--summary", required=True)
    ap.add_argument("--workers", type=int, default=5)
    ap.add_argument("--cap", type=int, default=14_000_000,
                    help="1 帯が触る状態数の上限（記憶の上限を決める）")
    ap.add_argument("--as-gb", type=float, default=4.0)
    ap.add_argument("--deadline", type=float, default=0.0,
                    help="この秒数を過ぎたら新しい帯を起こさない（0 なら無制限）")
    ap.add_argument("--harvest-only", action="store_true")
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)
    w = widths(args.cert_dir, args.d_to + 1)
    bands = split_bands(w, args.d_from, args.d_to, args.cap)
    if args.harvest_only:
        disk = bands_on_disk(args.outdir)
        if disk:
            bands = disk

    if not args.harvest_only:
        todo = [bd for bd in bands if band_done(args.outdir, *bd) is None]
        print("bands %d (todo %d) workers %d" % (len(bands), len(todo), args.workers),
              flush=True)
        t0 = time.time()
        running: list[tuple[tuple[int, int], subprocess.Popen, object, float]] = []
        queue = list(todo)
        done = 0
        while queue or running:
            while queue and len(running) < args.workers:
                if args.deadline and time.time() - t0 > args.deadline:
                    print("deadline: %d bands left unstarted" % len(queue), flush=True)
                    queue = []
                    break
                bd = queue.pop(0)
                proc, fh = launch(args.h, args.p, bd[0], bd[1], args.outdir,
                                  args.cert_dir, args.as_gb)
                running.append((bd, proc, fh, time.time()))
                print("start %s pid=%d" % (bd, proc.pid), flush=True)
            time.sleep(2.0)
            still = []
            for bd, proc, fh, ts in running:
                rc = proc.poll()
                if rc is None:
                    still.append((bd, proc, fh, ts))
                    continue
                fh.close()
                done += 1
                print("done %s rc=%d %.1fs (%d/%d, elapsed %.1fs)"
                      % (bd, rc, time.time() - ts, done, len(todo), time.time() - t0),
                      flush=True)
            running = still
            with open(args.summary, "w") as sf:
                json.dump(harvest(args.h, args.p, args.outdir, args.d_from,
                                  args.d_to, bands), sf, ensure_ascii=False, indent=2)

    summary = harvest(args.h, args.p, args.outdir, args.d_from, args.d_to, bands)
    with open(args.summary, "w") as sf:
        json.dump(summary, sf, ensure_ascii=False, indent=2)
    print(json.dumps(summary, ensure_ascii=False, indent=2), flush=True)
    return 0 if summary["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
