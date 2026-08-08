"""アトラス Phase 4 — 未計測コーパスへの資源ベクトルの拡張（`docs/81_resource_atlas_plan.md` §2）。

Phase 0〜1 のアトラス（`data/atlas/atlas.csv`、111 本）は
**PyJanus fixtures ＋ jana ＋ メモ化**だけを対象にしていた。原稿 A のコーパス
`yokoyama-lab/reversible-algorithms`（131 本、うち可逆 120 本）は**一度も計測されていない**。
また PyJanus 側 fixtures は 2026-08 に**全件が改名**され（`*_c.ja` / `*_g.ja`）4 本増えたので、
`atlas.csv` の `name` 列は現在の木のどのファイルとも一致しない。ここを埋める。

**独立 2 実装での照合**（研究室の規約。exp52 の 245 倍水増しの教訓）:

- 実装 A: 本リポジトリの `scripts/atlas_measure.py`（`Runtime` を継承した自作トレーサ）。
- 実装 B: PyJanus 純正 `python3 -m jana_py.cli --profile`（`jana_py/pebble.py`）。
  共通に定義されている `steps`（実行文数）と `call_depth`（呼び出し深さのピーク）を突き合わせる。

2 実装が食い違った本数を必ず出力する（0 でないなら数値は報告しない）。

使い方:
    python3 scripts/atlas_extend.py --corpus revalgs   # reversible-algorithms
    python3 scripts/atlas_extend.py --corpus pyjanus   # 改名後の fixtures（再計測）
    python3 scripts/atlas_extend.py --corpus both
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
DEV = Path.home() / "dev/github.com"
PYJANUS = DEV / "yokoyama-lab/PyJanus"
CORPUS = DEV / "yokoyama-lab/reversible-algorithms"
MEASURE = REPO / "scripts/atlas_measure.py"
OUT = REPO / "data/atlas/atlas_corpus.csv"
OUT_ARR = REPO / "data/atlas/atlas_corpus_arrays.csv"

FIELDS = [
    "corpus", "category", "name", "path",
    "steps", "call_depth_peak", "stack_peak",
    "final_live_bits", "final_nonzero_cells", "arrays_tracked",
    "b_steps", "b_call_depth_peak", "b_peak_live_vars", "b_peak_live_bits",
    "agree_steps", "agree_call_depth", "error",
]

PROF_RE = {
    "b_steps": re.compile(r"Total steps:\s+(\d+)"),
    "b_peak_live_vars": re.compile(r"Peak live variables:\s+(\d+)"),
    "b_peak_live_bits": re.compile(r"Peak live bits:\s+(\d+)"),
    "b_call_depth_peak": re.compile(r"Max call depth:\s+(\d+)"),
}


def impl_a(path: Path, timeout: float) -> dict:
    res = subprocess.run([sys.executable, str(MEASURE), "--single", str(path)],
                         capture_output=True, text=True, timeout=timeout)
    if res.returncode != 0:
        raise RuntimeError((res.stderr.strip().splitlines() or [""])[-1][:100])
    return json.loads(res.stdout.strip().splitlines()[-1])


def impl_b(path: Path, timeout: float) -> dict:
    """PyJanus 純正プロファイラ。ここが第 2 実装。"""
    res = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", "jana2014",
                          "--profile", str(path)],
                         capture_output=True, text=True, timeout=timeout, cwd=str(PYJANUS))
    if res.returncode != 0:
        raise RuntimeError((res.stderr.strip().splitlines() or [""])[-1][:100])
    out = {}
    for k, rx in PROF_RE.items():
        m = rx.search(res.stdout)
        out[k] = int(m.group(1)) if m else None
    return out


def targets(which: str) -> list[tuple[str, str, Path]]:
    """(corpus, category, path) の一覧。"""
    out: list[tuple[str, str, Path]] = []
    if which in ("revalgs", "both"):
        cov = REPO / "data/atlas/coverage_l123.csv"
        cat = {}
        if cov.exists():
            cat = {r["file"]: r for r in csv.DictReader(cov.open())}
        for p in sorted(CORPUS.glob("**/*.j")):
            rel = p.relative_to(CORPUS).as_posix()
            r = cat.get(rel)
            if r and r["l1"] != "reversible":
                continue          # L1 を通らないものは計測対象外（理由は coverage 表に残る）
            out.append(("revalgs", (r or {}).get("category", ""), p))
    if which in ("pyjanus", "both"):
        for p in sorted((PYJANUS / "tests/jana2014/fixtures/examples").glob("*.ja")):
            kind = "structs" if p.stem.startswith("structs_") else (
                "garbage" if p.stem.endswith("_g") else "clean")
            out.append(("pyjanus2026-08", kind, p))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", choices=["revalgs", "pyjanus", "both"], default="both")
    ap.add_argument("--timeout", type=float, default=180.0)
    args = ap.parse_args()

    rows, arr_rows = [], []
    t0 = time.monotonic()
    tg = targets(args.corpus)
    for i, (corpus, category, path) in enumerate(tg, 1):
        name = path.name
        rec = {"corpus": corpus, "category": category, "name": name,
               "path": str(path), "error": ""}
        try:
            a = impl_a(path, args.timeout)
            rec.update({k: a[k] for k in ("steps", "call_depth_peak", "stack_peak",
                                          "final_live_bits", "final_nonzero_cells")})
            rec["arrays_tracked"] = len(a["arrays"])
            for aname, v in a["arrays"].items():
                arr_rows.append({"corpus": corpus, "name": name, "array": aname, **v})
        except Exception as exc:
            rec["error"] = f"A:{type(exc).__name__}: {str(exc)[:80]}"
        try:
            rec.update(impl_b(path, args.timeout))
        except Exception as exc:
            rec["error"] = (rec["error"] + " | " if rec["error"] else "") + \
                f"B:{type(exc).__name__}: {str(exc)[:80]}"
        for key, a_key, b_key in (("agree_steps", "steps", "b_steps"),
                                  ("agree_call_depth", "call_depth_peak", "b_call_depth_peak")):
            av, bv = rec.get(a_key), rec.get(b_key)
            rec[key] = "" if av is None or bv is None else str(av == bv)
        rows.append(rec)
        note = rec["error"] or "steps={}".format(rec.get("steps"))
        print(f"[{i}/{len(tg)}] {corpus}/{name}: {note} "
              f"agree={rec['agree_steps']}/{rec['agree_call_depth']}", flush=True)

    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)
    with OUT_ARR.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=["corpus", "name", "array", "puts", "takes",
                                          "peak_nonzero", "final_nonzero"],
                           extrasaction="ignore")
        w.writeheader()
        w.writerows(arr_rows)

    ok = sum(1 for r in rows if not r["error"])
    dis_s = sum(1 for r in rows if r["agree_steps"] == "False")
    dis_d = sum(1 for r in rows if r["agree_call_depth"] == "False")
    cmp_n = sum(1 for r in rows if r["agree_steps"] in ("True", "False"))
    print(f"\n計測 {ok}/{len(rows)} 本 ({time.monotonic() - t0:.0f} 秒)")
    print(f"2 実装照合: 比較できた {cmp_n} 本中 steps 不一致 {dis_s} 本 / call_depth 不一致 {dis_d} 本")
    return 0


if __name__ == "__main__":
    sys.exit(main())
