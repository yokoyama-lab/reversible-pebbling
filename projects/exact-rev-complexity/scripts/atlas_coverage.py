"""アトラス Phase 4 — 3 層検証の被覆マトリクス（`docs/81_resource_atlas_plan.md` の続き）。

対象は **`yokoyama-lab/reversible-algorithms` の全 `*.j`**（原稿 A のコーパス）。
PyJanus 側 fixtures については既に `PyJanus/docs/corpus-coverage.md` に被覆表があるが、
**reversible-algorithms 側には L1 しか無い**（`CATALOG.md` は可逆性のみ）。ここを埋める。

層の定義（`~/dev/overleaf/2027_reversible_corpus/paper-outline.md` §5）:

- **L1 可逆性**: `main` の本体 + その逆 = 恒等（PyJanus `invert_stmts`）。
- **L2 正答性**: Python 参照実装との乱択差分（`reversible-algorithms/tools/reftest.py`）。
  ここでは *登録の有無* を見る（実行結果は別途 reftest を回して突き合わせる）。
- **L3 処理系横断**: PyJanus インタプリタ vs (a) Rocq 抽出の検証済みインタプリタ
  （`coq/harness/differentialar.py` + `driverar`）、(b) C++ コード生成
  （`coq/harness/codegen_diff.py`）。

**「走らなかった検査」は必ず可視化する**（skip 理由を列に残す。沈黙を成功と書かない）。
対象リポジトリは読み取り専用。1 本ずつサブプロセスに隔離して走らせる。

使い方:
    python3 scripts/atlas_coverage.py                    # 全層・全ファイル（数分）
    python3 scripts/atlas_coverage.py --single <path> --check l1|vjanus|codegen
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
DEV = Path.home() / "dev/github.com"
PYJANUS = DEV / "yokoyama-lab/PyJanus"
CORPUS = DEV / "yokoyama-lab/reversible-algorithms"
DRIVERAR = PYJANUS / "coq/harness/driverar"
OUT = REPO / "data/atlas/coverage_l123.csv"

FIELDS = [
    "file", "category", "in_pyjanus_corpus",
    "l1", "l1_detail",
    "l2_algos", "l2",
    "l3_vjanus", "l3_vjanus_detail",
    "l3_codegen", "l3_codegen_detail",
]


# ---- L1: 可逆性（body + invert(body) = id） --------------------------------

def check_l1(path: Path) -> tuple[str, str]:
    """`tools/build_catalog.py` の判定を独立に再実装したもの（＝台帳の鮮度検査を兼ねる）。"""
    import contextlib
    import copy
    import io

    sys.path.insert(0, str(PYJANUS))
    from jana_py.ast import Program, ProcMain
    from jana_py.invert import invert_stmts
    from jana_py.parser_jana2014 import parse_program
    from jana_py.runtime import Runtime
    from jana_py.validate import validate_program

    def store(program):
        rt = Runtime(program)
        rt.run()
        return {k: copy.deepcopy(c.value) for k, c in rt._root_frame.vars.items()}

    try:
        prog = parse_program(str(path), path.read_text())
    except Exception as exc:
        return "parse_err", str(exc).splitlines()[0][:80]
    try:
        validate_program(prog)
    except Exception as exc:
        msg = str(exc)
        if "no main" in msg.lower():
            return "library", "no main procedure"
        return "validate_err", msg.splitlines()[0][:80]
    if prog.main is None:
        return "library", "no main procedure"
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            init = ProcMain(prog.main.vdecls, [], prog.main.pos)
            s0 = store(Program(init, prog.procs, prog.struct_defs))
            body = list(prog.main.stmts) + invert_stmts(prog.main.stmts, global_mode=False)
            s1 = store(Program(ProcMain(prog.main.vdecls, body, prog.main.pos),
                               prog.procs, prog.struct_defs))
        return ("reversible", "") if s0 == s1 else ("not_identity", "")
    except Exception as exc:
        return "run_err", str(exc).splitlines()[0][:80]


# ---- L3: 処理系横断 ---------------------------------------------------------

def _pyjanus_on_path() -> None:
    """ハーネスは `python3 -m jana_py.cli` に shell out する。見えないと
    「PyJanus runtime error」＝ skip に化けるので、**必ず PYTHONPATH を通す**
    （2026-08-09 に、通し忘れで L3 が全数 skip になる偽陰性を実際に踏んだ）。"""
    cur = os.environ.get("PYTHONPATH", "")
    if str(PYJANUS) not in cur.split(os.pathsep):
        os.environ["PYTHONPATH"] = f"{PYJANUS}{os.pathsep}{cur}" if cur else str(PYJANUS)


def check_vjanus(path: Path) -> tuple[str, str]:
    """Rocq 抽出インタプリタ（`RevExtractAr.run`）と PyJanus の store 差分。"""
    _pyjanus_on_path()
    sys.path.insert(0, str(PYJANUS / "coq/harness"))
    import differentialar

    if not DRIVERAR.exists():
        return "no_driver", "driverar が未ビルド（rocq/ocamlc が要る）"
    try:
        diffs = differentialar.check(str(DRIVERAR), str(path))
    except differentialar.Unsupported as exc:
        return "skip", str(exc)[:80]
    except Exception as exc:
        return "harness_err", f"{type(exc).__name__}: {exc}"[:80]
    if diffs:
        return "WRONG", "; ".join(f"{n}: v={a} py={b}" for n, a, b in diffs)[:120]
    return "PASS", ""


def check_codegen(path: Path) -> tuple[str, str]:
    """C++ バックエンドとインタプリタの store 差分。"""
    _pyjanus_on_path()
    sys.path.insert(0, str(PYJANUS))
    sys.path.insert(0, str(PYJANUS / "coq/harness"))
    import codegen_diff

    try:
        tag, msg = codegen_diff.check(str(path))
    except Exception as exc:
        return "harness_err", f"{type(exc).__name__}: {exc}"[:80]
    return tag, msg[:120]


CHECKS = {"l1": check_l1, "vjanus": check_vjanus, "codegen": check_codegen}


# ---- L2: reftest の登録状況 -------------------------------------------------

def l2_map() -> dict[str, list[str]]:
    """`tools/reftest.py` の ALGOS から「.j ファイル → 登録アルゴリズム名」を得る。

    `_procs` を持つ合成エントリ（AVL 系）はソースを読んで `procs_of("…")` の
    引数を拾う。実行はしない（import だけ）。
    """
    import ast as pyast

    src = (CORPUS / "tools/reftest.py").read_text()
    tree = pyast.parse(src)

    # 関数名 → その本体に現れる procs_of("…") の引数（`_procs=` 合成エントリ用）
    helper_files: dict[str, list[str]] = {}
    for node in pyast.walk(tree):
        if isinstance(node, pyast.FunctionDef):
            fs = [c.args[0].value for c in pyast.walk(node)
                  if isinstance(c, pyast.Call)
                  and isinstance(c.func, pyast.Name) and c.func.id == "procs_of"
                  and c.args and isinstance(c.args[0], pyast.Constant)]
            if fs:
                helper_files[node.name] = fs

    out: dict[str, list[str]] = {}
    for node in pyast.walk(tree):
        if not (isinstance(node, pyast.Call) and isinstance(node.func, pyast.Name)
                and node.func.id == "register" and node.args):
            continue
        name = node.args[0].value
        files: list[str] = []
        for kw in node.keywords:
            if kw.arg not in ("procs", "_procs"):
                continue
            if isinstance(kw.value, pyast.Constant):
                files.append(kw.value.value)
            elif isinstance(kw.value, pyast.Name):
                files += helper_files.get(kw.value.id, [])
        for f in files:
            out.setdefault(f, []).append(name)
    return out


# ---- 駆動 -------------------------------------------------------------------

def run_isolated(path: Path, check: str, timeout: float) -> tuple[str, str]:
    cmd = [sys.executable, str(Path(__file__).resolve()),
           "--single", str(path), "--check", check]
    env = dict(os.environ, PYTHONPATH=f"{PYJANUS}:{os.environ.get('PYTHONPATH', '')}")
    try:
        res = subprocess.run(cmd, capture_output=True, text=True,
                             timeout=timeout, env=env)
    except subprocess.TimeoutExpired:
        return "timeout", f"{timeout:g}s"
    if res.returncode != 0:
        return "crash", (res.stderr.strip().splitlines() or [""])[-1][:80]
    try:
        d = json.loads(res.stdout.strip().splitlines()[-1])
    except Exception:
        return "crash", "出力が JSON でない"
    return d["status"], d["detail"]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--single")
    ap.add_argument("--check", choices=sorted(CHECKS))
    ap.add_argument("--timeout", type=float, default=180.0)
    ap.add_argument("--limit", type=int, default=0)
    args = ap.parse_args()

    if args.single:
        status, detail = CHECKS[args.check](Path(args.single))
        print(json.dumps({"status": status, "detail": detail}))
        return 0

    catalog = json.loads((CORPUS / "catalog.json").read_text())["records"]
    cat = {r["file"]: r for r in catalog}
    l2 = l2_map()

    files = sorted(p.relative_to(CORPUS).as_posix()
                   for p in CORPUS.glob("**/*.j"))
    if args.limit:
        files = files[: args.limit]

    rows = []
    t0 = time.time()
    for i, rel in enumerate(files, 1):
        path = CORPUS / rel
        rec = cat.get(rel, {})
        row = {
            "file": rel,
            "category": rec.get("category", ""),
            "in_pyjanus_corpus": rec.get("in_pyjanus_corpus", ""),
            "l2_algos": ";".join(l2.get(rel, [])),
            "l2": "registered" if rel in l2 else "unregistered",
        }
        row["l1"], row["l1_detail"] = run_isolated(path, "l1", args.timeout)
        if row["l1"] == "reversible":
            row["l3_vjanus"], row["l3_vjanus_detail"] = run_isolated(path, "vjanus", args.timeout)
            row["l3_codegen"], row["l3_codegen_detail"] = run_isolated(path, "codegen", args.timeout)
        else:
            row["l3_vjanus"] = row["l3_codegen"] = "not_attempted"
            row["l3_vjanus_detail"] = row["l3_codegen_detail"] = f"L1={row['l1']}"
        rows.append(row)
        print(f"[{i}/{len(files)}] {rel}: L1={row['l1']} "
              f"vjanus={row['l3_vjanus']} codegen={row['l3_codegen']}", flush=True)

    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(rows)
    print(f"\n{len(rows)} 行を {OUT} に書いた（{time.time() - t0:.0f} 秒）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
