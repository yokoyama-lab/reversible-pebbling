"""資源アトラス Phase 1 — 全数計測（`docs/81_resource_atlas_plan.md` §3）。

exp51/exp52 のトレーサを一般化したもの。**全配列を自動追跡**する
（変数名決め打ちの罠＝exp51 §6 の恒久対応）。1 プログラムにつき:

- `steps` 実行文数 / `call_depth_peak` 呼び出し深さ
- `stack_peak` 全フレームのスタック総深さ（`Cell.kind == "stack"`）
- 配列ごとの `puts`/`takes`（セルの 0↔非0 遷移数）・`peak_nonzero`・`final_nonzero`
- `final_live_bits` 終端の非ゼロ状態量（ビット幅は PyJanus 純正 `_value_bits` を流用）

**設計上の要点 — セル同一性での重複排除**: Janus の手続き引数は参照渡しなので、
同じ配列セルが複数フレームから見える。フレーム横断で素朴に合計すると二重計上になる
（exp51 は root フレームだけを見ることで偶然回避していた）。本実装は `id(cell)` で
デデュープした「生きているセル集合」を各文ごとに取る。

ガベージの clean/dirty 判定は**しない**（先生の決定 2026-07-28: アトラス本体は
`final_live_bits` を値として報告するだけ。注釈つき部分集合の判定は別スクリプト）。

使い方:
    python3 scripts/atlas_measure.py --single <path>     # 1 本（JSON 出力）
    python3 scripts/atlas_measure.py                     # census で run_ok の全本（背景推奨）
"""

from __future__ import annotations

import argparse
import csv
import json
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
PYJANUS = Path.home() / "dev/github.com/yokoyama-lab/PyJanus"
sys.path.insert(0, str(PYJANUS))

from jana_py.cli import parse_for_std  # noqa: E402
from jana_py.pebble import _value_bits  # noqa: E402  # ビット幅の定義は純正を流用
from jana_py.runtime import Frame, Runtime  # noqa: E402


class AtlasTracer(Runtime):
    """全配列・全スタック・歩数・呼び出し深さを文単位で追跡する Runtime。"""

    def __init__(self, program, **kwargs):
        super().__init__(program, **kwargs)
        self.steps = 0
        self.call_depth = 0
        self.call_depth_peak = 0
        self.stack_peak = 0
        self._frames: list[Frame] = []
        # 配列名 → {puts, takes, peak_nonzero, prev: set[int]}  （cell id でデデュープ）
        self.arrays: dict[str, dict] = {}
        self._seen_cells: dict[int, str] = {}  # id(cell) → 配列名（初出名で固定）

    # -- 計測 -----------------------------------------------------------------

    def _scan(self) -> None:
        stack_depth = 0
        nonzero_now: dict[str, set[int]] = {}
        seen_ids: set[int] = set()
        for fr in self._frames:
            for name, cell in list(fr.vars.items()):
                cid = id(cell)
                if getattr(cell, "kind", None) == "stack":
                    if cid not in seen_ids:
                        seen_ids.add(cid)
                        val = getattr(cell, "value", None)
                        if hasattr(val, "__len__"):
                            stack_depth += len(val)
                    continue
                val = getattr(cell, "value", None)
                if not isinstance(val, list):
                    continue
                if cid in seen_ids:
                    continue
                seen_ids.add(cid)
                aname = self._seen_cells.setdefault(cid, name)
                cur = {i for i, v in enumerate(val) if v}
                nonzero_now.setdefault(aname, set()).update(cur)
        self.stack_peak = max(self.stack_peak, stack_depth)
        for aname, cur in nonzero_now.items():
            rec = self.arrays.setdefault(
                aname, {"puts": 0, "takes": 0, "peak_nonzero": 0, "prev": set()}
            )
            rec["puts"] += len(cur - rec["prev"])
            rec["takes"] += len(rec["prev"] - cur)
            rec["peak_nonzero"] = max(rec["peak_nonzero"], len(cur))
            rec["prev"] = cur
        # 消えた配列（フレームが pop された local 配列）は終端扱いにしない:
        # prev を保持したままにする（final は run() 終了時の root 走査で確定する）

    def _final_bits(self) -> tuple[int, int]:
        bits = 0
        cells = 0
        seen: set[int] = set()
        for fr in self._frames:
            for _name, cell in list(fr.vars.items()):
                cid = id(cell)
                if cid in seen:
                    continue
                seen.add(cid)
                val = getattr(cell, "value", None)
                if isinstance(val, list):
                    for v in val:
                        if v:
                            bits += _value_bits(v)
                            cells += 1
                elif val:
                    bits += _value_bits(val)
                    cells += 1
        return bits, cells

    # -- Runtime hooks ---------------------------------------------------------

    def run(self) -> str:
        if self.program.main is None:
            raise RuntimeError("main 手続きが無い")
        frame = Frame(vars={})
        self._frames = [frame]
        self.main_vdecls = list(self.program.main.vdecls)
        self._init_vdecls(frame, self.program.main.vdecls)
        self._scan()
        self._exec_block(frame, self.program.main.stmts)
        self._frames = [frame]  # 終端は root のみで確定
        self._scan()
        self.final_live_bits, self.final_nonzero_cells = self._final_bits()
        return ""

    def _exec_stmt_impl(self, frame, stmt, allow_break, record_stmt, record_nested=False):
        if frame not in self._frames:
            self._frames.append(frame)
        super()._exec_stmt_impl(
            frame, stmt, allow_break=False,
            record_stmt=record_stmt, record_nested=record_nested,
        )
        self.steps += 1
        self._scan()

    def _call_proc(self, caller, name, args, pos, record_stmt=True, record_nested=False):
        self.call_depth += 1
        self.call_depth_peak = max(self.call_depth_peak, self.call_depth)
        try:
            super()._call_proc(caller, name, args, pos,
                               record_stmt=record_stmt, record_nested=record_nested)
        finally:
            self.call_depth -= 1

    def _uncall_proc(self, caller, name, args, pos, record_stmt=True, record_nested=False):
        self.call_depth += 1
        self.call_depth_peak = max(self.call_depth_peak, self.call_depth)
        try:
            super()._uncall_proc(caller, name, args, pos,
                                 record_stmt=record_stmt, record_nested=record_nested)
        finally:
            self.call_depth -= 1


def measure(path: Path) -> dict:
    src = path.read_text()
    prog = parse_for_std("jana2014", str(path), src, None)
    tr = AtlasTracer(prog)
    tr.run()
    return {
        "steps": tr.steps,
        "call_depth_peak": tr.call_depth_peak,
        "stack_peak": tr.stack_peak,
        "final_live_bits": tr.final_live_bits,
        "final_nonzero_cells": tr.final_nonzero_cells,
        "arrays": {
            k: {"puts": v["puts"], "takes": v["takes"],
                "peak_nonzero": v["peak_nonzero"],
                "final_nonzero": len(v["prev"])}
            for k, v in tr.arrays.items()
        },
    }


def sweep(timeout: float) -> None:
    census = REPO / "data/atlas/census.csv"
    rows = [r for r in csv.DictReader(census.open()) if r["run_ok"] == "True"]
    out_main = REPO / "data/atlas/atlas.csv"
    out_arr = REPO / "data/atlas/atlas_arrays.csv"
    main_rows: list[dict] = []
    arr_rows: list[dict] = []
    t0 = time.monotonic()
    for i, r in enumerate(rows, 1):
        rec = {"corpus": r["corpus"], "category": r["category"], "name": r["name"]}
        try:
            out = subprocess.run(
                [sys.executable, __file__, "--single", r["path"]],
                capture_output=True, text=True, timeout=timeout,
            )
            m = json.loads(out.stdout.strip().splitlines()[-1])
            rec.update({k: m[k] for k in (
                "steps", "call_depth_peak", "stack_peak",
                "final_live_bits", "final_nonzero_cells")})
            rec["arrays_tracked"] = len(m["arrays"])
            rec["error"] = ""
            for aname, a in m["arrays"].items():
                arr_rows.append({
                    "name": r["name"], "array": aname, **a,
                })
        except subprocess.TimeoutExpired:
            rec["error"] = f"timeout>{timeout}s"
        except Exception as exc:
            rec["error"] = f"{type(exc).__name__}: {str(exc)[:80]}"
        main_rows.append(rec)
        # 逐次書き出し
        with out_main.open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=[
                "corpus", "category", "name", "steps", "call_depth_peak",
                "stack_peak", "final_live_bits", "final_nonzero_cells",
                "arrays_tracked", "error"], extrasaction="ignore")
            w.writeheader(); w.writerows(main_rows)
        with out_arr.open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=[
                "name", "array", "puts", "takes", "peak_nonzero", "final_nonzero"],
                extrasaction="ignore")
            w.writeheader(); w.writerows(arr_rows)
        status = rec.get("error") or f"steps={rec.get('steps')}"
        print(f"[{i}/{len(rows)}] {r['name']}: {status}", flush=True)
    ok = sum(1 for r in main_rows if not r.get("error"))
    print(f"\n完了: {ok}/{len(main_rows)} 本を計測 ({time.monotonic()-t0:.0f} 秒)", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--single", type=Path, default=None)
    ap.add_argument("--timeout", type=float, default=300.0)
    args = ap.parse_args()
    if args.single:
        print(json.dumps(measure(args.single)))
        return
    sweep(args.timeout)


if __name__ == "__main__":
    main()
