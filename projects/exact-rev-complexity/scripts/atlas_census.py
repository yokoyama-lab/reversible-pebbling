"""資源アトラス Phase 0 — 実行センサス（`docs/81_resource_atlas_plan.md`）。

コーパス全体について「パースできるか／実行できるか／何秒か」だけを調べ、
`data/atlas/census.csv` に 1 プログラム 1 行で記録する。**資源計測はまだしない**（Phase 1）。

運用（docs/81 §3 Phase 0 のとおり）:
- 各プログラムは**サブプロセスで隔離実行**する（クラッシュ・無限ループ・stdin 待ちが
  センサス全体を殺さないように）。タイムアウト既定 120 秒。
- **失敗は 1 回で確定させず再試行 1 回**（資源競合の教訓、exp04 §13）。
- 失敗も列として記録する（error 列）。判定不能を成功と書かない。
- 対象リポジトリは**読み取り専用**。

使い方:
    python3 scripts/atlas_census.py            # 全コーパス（長い。バックグラウンド推奨）
    python3 scripts/atlas_census.py --single <path>   # 1 本だけ（内部利用・JSON を出力）
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

CORPORA: list[tuple[str, Path, str]] = [
    ("pyjanus", PYJANUS / "tests/jana2014/fixtures/examples", "*.ja"),
    ("jana", Path.home() / "dev/github.com/tetsuo-jp/jana/examples", "*.ja"),
    ("oracle", Path.home() / "dev/github.com/tetsuo-jp/janus-oracle/examples", "*.jns"),
    ("memoization", Path.home() / "dev/overleaf/2017_rev_memoization/program", "*.janus"),
    ("memoization", Path.home() / "dev/overleaf/2021_rev_memoization2/programs", "*.janus"),
]


def categorize(corpus: str, stem: str) -> str:
    """区分列。先生の決定（2026-07-28）: injective 系は含めて区分で分ける。"""
    if corpus != "pyjanus":
        return corpus
    if stem.startswith("injective_"):
        return "injective"
    if stem.startswith("structs_"):
        return "structs"
    return "algorithm"


def discover() -> list[tuple[str, Path]]:
    out: list[tuple[str, Path]] = []
    for corpus, d, pat in CORPORA:
        if d.is_dir():
            out += [(corpus, f) for f in sorted(d.glob(pat))]
    return out


def run_single(path: Path, *, timeout: float = 120.0) -> dict:
    """1 本をこのプロセス内で parse → run する（`--single` モードの実体）。

    センサス親からはサブプロセス経由で呼ばれるので、ここで落ちても親は死なない。
    """
    res = {"parse_ok": False, "run_ok": False, "seconds": None, "error": ""}
    try:
        src = path.read_text()
    except OSError as exc:
        res["error"] = f"read: {exc}"
        return res
    sys.path.insert(0, str(PYJANUS))
    try:
        from jana_py.cli import parse_for_std

        prog = parse_for_std("jana2014", str(path), src, None)
        res["parse_ok"] = True
    except Exception as exc:
        res["error"] = f"parse: {type(exc).__name__}: {str(exc)[:120]}"
        return res
    try:
        from jana_py.runtime import Runtime

        t0 = time.monotonic()
        Runtime(prog).run()
        res["seconds"] = round(time.monotonic() - t0, 3)
        res["run_ok"] = True
    except Exception as exc:
        res["error"] = f"run: {type(exc).__name__}: {str(exc)[:120]}"
    return res


def census(timeout: float, out_path: Path) -> None:
    files = discover()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    t_start = time.monotonic()
    for i, (corpus, f) in enumerate(files, 1):
        row = {
            "corpus": corpus,
            "category": categorize(corpus, f.stem),
            "name": f.stem,
            "path": str(f),
        }
        verdict: dict | None = None
        for attempt in (1, 2):  # 失敗は1回で確定させない
            try:
                out = subprocess.run(
                    [sys.executable, __file__, "--single", str(f), "--timeout", str(timeout)],
                    capture_output=True,
                    text=True,
                    timeout=timeout + 10,
                )
                verdict = json.loads(out.stdout.strip().splitlines()[-1])
            except subprocess.TimeoutExpired:
                verdict = {
                    "parse_ok": None, "run_ok": False, "seconds": None,
                    "error": f"timeout>{timeout}s",
                }
            except Exception as exc:
                verdict = {
                    "parse_ok": None, "run_ok": False, "seconds": None,
                    "error": f"harness: {type(exc).__name__}",
                }
            if verdict.get("run_ok"):
                break  # 成功なら再試行不要
        row.update(verdict or {})
        row["attempts"] = attempt
        rows.append(row)
        # 逐次書き出し（途中で殺されてもデータが残る）
        with out_path.open("w", newline="") as fh:
            w = csv.DictWriter(
                fh,
                fieldnames=[
                    "corpus", "category", "name", "parse_ok", "run_ok",
                    "seconds", "attempts", "error", "path",
                ],
                extrasaction="ignore",
            )
            w.writeheader()
            w.writerows(rows)
        print(
            f"[{i}/{len(files)}] {corpus}/{f.stem}: "
            f"{'OK' if row.get('run_ok') else row.get('error', '?')[:60]}",
            flush=True,
        )
    ok = sum(1 for r in rows if r.get("run_ok"))
    print(
        f"\n完了: {ok}/{len(rows)} 本が実行成功 "
        f"({time.monotonic() - t_start:.0f} 秒) → {out_path}",
        flush=True,
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--single", type=Path, default=None)
    ap.add_argument("--timeout", type=float, default=120.0)
    ap.add_argument("--out", type=Path, default=REPO / "data/atlas/census.csv")
    args = ap.parse_args()
    if args.single:
        print(json.dumps(run_single(args.single, timeout=args.timeout)))
        return
    census(args.timeout, args.out)


if __name__ == "__main__":
    main()
