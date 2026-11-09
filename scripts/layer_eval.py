#!/usr/bin/env python3
"""層判定の eval — 正解は proof-manifest.json（カーネルが受理した事実）。

台帳 Q20（arXiv 本文と Lean の対応が独立検算されていない）を、
**正解付きの機械採点タスク**に落としたもの。

## なぜ eval が要るか

Anthropic の Fable 5.1 のドキュメントは使用条件をこう書いている:

  > Use Claude Fable 5.1 for demanding reasoning and long-horizon agentic
  > work, **or when your evals on Claude Opus 5 at higher effort still
  > fall short.**

「Opus 5 を高い effort で回した eval が不足したとき」が条件なので、
eval が無い状態でモデルを替える判断はできない。これはその eval。

## タスクと正解

各定理について「その定理は層 1（無条件の機械証明）と呼んでよいか」を答える。
正解は manifest から機械的に決まる:

  - `native_decide_theorems` に載る  -> 層1にしてはいけない（有界全数検査）
    （台帳の R-CBT-01「有界事例の機械検証は層 1 にしない」）
  - stage の status が `proved_general` かつ native_decide でない -> 層1でよい
  - それ以外（carried 仮説に依存など） -> 層1にしてはいけない

正解が人間の判断を経ていないのが要点で、採点は再現する。

## 使い方

  ./layer_eval.py --build      # タスク集合を書き出す（tasks.jsonl）
  ./layer_eval.py --score answers.jsonl
  ./layer_eval.py --baseline   # 常に「層1でない」と答える下駄を測る

`answers.jsonl` は 1 行 1 件で `{"id": ..., "layer1": true|false}`。
"""
from __future__ import annotations

import argparse
import json
import random
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "proof-manifest.json"
TASKS = ROOT / "data" / "layer_eval_tasks.jsonl"


def ground_truth() -> list[dict]:
    """manifest から (定理, 正解) を組み立てる。判断は一切入れない。"""
    m = json.loads(MANIFEST.read_text(encoding="utf-8"))
    stages = m.get("proved_stages", {})
    if not stages:
        raise SystemExit("proof-manifest.json に proved_stages が無い")

    # 無条件の一般証明とみなせる stage の status
    GENERAL = {"proved_general", "proved_unbounded"}

    rows: list[dict] = []
    for sname, s in stages.items():
        nd = set(s.get("native_decide_theorems", []))
        status = s.get("status", "")
        # carried_hypotheses は {仮説名: [その仮説を担ぐ定理名, ...]} の dict。
        # 定理単位で判定できるので stage 単位より精度が高い。
        carried_map = s.get("carried_hypotheses", {}) or {}
        carried_of: dict[str, list[str]] = {}
        for hyp, ths in carried_map.items():
            for t in (ths or []):
                carried_of.setdefault(t, []).append(hyp)

        for th in s.get("theorems", []):
            hyps = carried_of.get(th, [])
            if th in nd:
                truth, why = False, "native_decide（有界全数検査）は層1にしない"
            elif hyps:
                truth, why = False, f"未証明の仮説を担ぐ: {sorted(hyps)[:2]}"
            elif status in GENERAL:
                truth, why = True, f"status={status} の無条件証明で担ぐ仮説なし"
            else:
                truth, why = False, f"status={status} が一般証明でない"
            rows.append({
                "id": th,
                "stage": sname,
                "stage_status": status,
                "uses_native_decide": th in nd,
                "carries_hypotheses": sorted(hyps),
                "scope": (s.get("scope") or "")[:300],
                "layer1": truth,
                "rationale": why,
            })
    return rows


# 出題に出してはいけないフィールド。ここに正解を導く入力が全部入っている。
# 2026-09-03: これらを出題に含めていたため、5 行の規則スクリプトが 100% を
# 取った。出題が正解の入力を持っていたら、それは eval ではなく写経である。
LEAKY = {"layer1", "rationale", "uses_native_decide", "carries_hypotheses",
         "stage_status", "scope"}


def locate(theorem: str) -> dict:
    """定理名から Lean のソース位置と証明本体を引く。"""
    short = theorem.split(".")[-1]
    p = subprocess.run(
        ["rg", "-n", "--pcre2", "-g", "*.lean",
         rf"^\s*(theorem|lemma)\s+{re.escape(short)}\b", "."],
        cwd=ROOT, capture_output=True, text=True)
    hits = [ln for ln in p.stdout.splitlines() if ln.strip()]
    if len(hits) != 1:
        return {"source_file": None, "source": None,
                "locate_note": f"{len(hits)} 箇所に一致（一意でない）"}
    path, lineno, _ = hits[0].split(":", 2)
    src = (ROOT / path).read_text(encoding="utf-8", errors="replace").splitlines()
    i = int(lineno) - 1
    # 次の宣言までを証明本体とみなす
    j = i + 1
    while j < len(src) and not re.match(
            r"^\s*(theorem|lemma|def|instance|structure|end|namespace|@\[)", src[j]):
        j += 1
    body = "\n".join(src[i:min(j, i + 60)])
    whole = "\n".join(src)
    return {"source_file": path, "source": body,
            "source_file_text": whole, "locate_note": None}


def ground_truth_bounded() -> list[dict]:
    """絞った eval: 「この定理は有界全数検査(native_decide)に依存するか」。

    層判定そのものは stage 単位・manifest 単位の性質（carried 仮説、status）に
    依存し、定理のソースからは原理的に判定できない（169 件中 96 件がこれ）。
    誰も解けない問いを出しても測定にならないので、**artifact から判定できる
    問いに絞る**。これは台帳の R-CBT-01「有界事例の機械検証は層 1 にしない」の
    核心であり、過大主張を防ぐ最重要の判定でもある。

    正解は manifest の native_decide_theorems（カーネルが受理した事実）。
    """
    m = json.loads(MANIFEST.read_text(encoding="utf-8"))
    rows = []
    for sname, s in m.get("proved_stages", {}).items():
        nd = set(s.get("native_decide_theorems", []))
        for th in s.get("theorems", []):
            rows.append({
                "id": th, "stage": sname,
                "layer1": th not in nd,   # True = 有界検査に依存しない
                "rationale": ("native_decide に依存する（層1にしない）"
                              if th in nd else "有界検査に依存しない"),
                "uses_native_decide": th in nd,
                "carries_hypotheses": [], "stage_status": "", "scope": "",
            })
    return rows


def cmd_build(args) -> int:
    rows = ground_truth_bounded() if args.bounded_only else ground_truth()
    if args.sample:
        rnd = random.Random(args.seed)
        # 正解の偏りを保ったまま抽出する（層1でない側が 169 しかない）
        pos = [r for r in rows if r["layer1"]]
        neg = [r for r in rows if not r["layer1"]]
        k = args.sample
        take_neg = min(len(neg), k // 2)
        take_pos = min(len(pos), k - take_neg)
        rows = rnd.sample(neg, take_neg) + rnd.sample(pos, take_pos)
        rnd.shuffle(rows)

    TASKS.parent.mkdir(parents=True, exist_ok=True)
    unlocated = 0
    with TASKS.open("w", encoding="utf-8") as f:
        for r in rows:
            q = {k: v for k, v in r.items() if k not in LEAKY}
            q.update(locate(r["id"]))
            if q.get("source") is None:
                unlocated += 1
            f.write(json.dumps(q, ensure_ascii=False) + "\n")

    pos = sum(1 for r in rows if r["layer1"])
    print(f"タスク {len(rows)} 件 -> {TASKS}")
    print(f"  層1でよい: {pos}  層1にしない: {len(rows) - pos}")
    print(f"  多数派に張るだけの正答率: {max(pos, len(rows) - pos) / len(rows):.1%}")
    print(f"  出題フィールド: {sorted(set(rows[0]) - LEAKY) + ['source_file', 'source']}")
    if unlocated:
        print(f"  ⚠ ソースを一意に引けなかった: {unlocated} 件（source=null で出題）")
    print("  ※ 正解を導く入力（native_decide / carried / status / scope）は伏せてある")
    return 0


def score(answers: dict[str, bool], rows: list[dict]) -> dict:
    truth = {r["id"]: r["layer1"] for r in rows}
    seen = [i for i in answers if i in truth]
    missing = [i for i in truth if i not in answers]
    unknown = [i for i in answers if i not in truth]

    tp = sum(1 for i in seen if answers[i] and truth[i])
    tn = sum(1 for i in seen if not answers[i] and not truth[i])
    fp = sum(1 for i in seen if answers[i] and not truth[i])
    fn = sum(1 for i in seen if not answers[i] and truth[i])
    return {
        "answered": len(seen), "missing": len(missing), "unknown": len(unknown),
        "tp": tp, "tn": tn, "fp": fp, "fn": fn,
        "accuracy": (tp + tn) / len(seen) if seen else 0.0,
        # 危険な誤り: 層1でないものを層1と言う（過大主張）
        "overclaim": fp,
        "overclaim_examples": [i for i in seen if answers[i] and not truth[i]][:5],
    }


def report(s: dict, total: int, label: str) -> str:
    lines = [f"=== {label}",
             f"  回答 {s['answered']}/{total}"
             + (f"  未回答 {s['missing']}" if s["missing"] else "")
             + (f"  未知ID {s['unknown']}" if s["unknown"] else ""),
             f"  正答率 {s['accuracy']:.1%}  (tp={s['tp']} tn={s['tn']} "
             f"fp={s['fp']} fn={s['fn']})",
             f"  ⚠ 過大主張（層1でないものを層1と言った）: {s['overclaim']} 件"]
    for e in s["overclaim_examples"]:
        lines.append(f"      {e}")
    return "\n".join(lines)


def cmd_score(args) -> int:
    rows = ground_truth_bounded() if args.bounded_only else ground_truth()
    p = Path(args.answers)
    if not p.exists():
        print(f"回答ファイルが無い: {p}", file=sys.stderr)
        return 2
    answers: dict[str, bool] = {}
    for ln in p.read_text(encoding="utf-8").splitlines():
        ln = ln.strip()
        if not ln:
            continue
        try:
            d = json.loads(ln)
            answers[d["id"]] = bool(d["layer1"])
        except (json.JSONDecodeError, KeyError) as e:
            print(f"読めない行: {e}", file=sys.stderr)
            return 2
    # 抽出して出題したときは、出題した分だけを分母にする。
    # 全件を分母にすると「未回答 825」が出て正答率が読めなくなる。
    if TASKS.exists() and not args.full:
        asked = {json.loads(x)["id"] for x in TASKS.read_text(
            encoding="utf-8").splitlines() if x.strip()}
        if asked and len(asked) < len(rows):
            rows = [r for r in rows if r["id"] in asked]
            print(f"（出題した {len(rows)} 件を分母にする。全件で見るなら --full）")
    s = score(answers, rows)
    print(report(s, len(rows), p.name))

    # 未回答が多いと正答率は意味を失う（成功した実行の本数を併記する規則）
    if s["missing"] > len(rows) * 0.1:
        print(f"\n⚠ 未回答が {s['missing']}/{len(rows)} 件。"
              "この正答率は回答できた分にしか掛かっていない。")
    # 過大主張が 1 件でもあれば fail-closed
    return 1 if s["overclaim"] else 0


def cmd_baseline(args) -> int:
    """下駄を測る。これを超えない結果は測定になっていない。"""
    rows = ground_truth_bounded() if args.bounded_only else ground_truth()
    ids = [r["id"] for r in rows]
    print(f"タスク {len(rows)} 件\n")
    for label, fn in (
            ("常に『層1でない』", lambda i: False),
            ("常に『層1でよい』", lambda i: True),
            ("硬貨投げ(seed=42)", None)):
        if fn is None:
            rnd = random.Random(42)
            ans = {i: rnd.random() < 0.5 for i in ids}
        else:
            ans = {i: fn(i) for i in ids}
        print(report(score(ans, rows), len(rows), label))
        print()
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--build", action="store_true")
    g.add_argument("--score", dest="answers")
    g.add_argument("--baseline", action="store_true")
    ap.add_argument("--sample", type=int, help="件数を絞る（正負を均す）")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--full", action="store_true",
                    help="抽出でなく manifest 全件を分母にする")
    ap.add_argument("--bounded-only", action="store_true",
                    help="artifact から判定できる問い（native_decide 依存）に絞る")
    args = ap.parse_args()
    if args.build:
        return cmd_build(args)
    if args.baseline:
        return cmd_baseline(args)
    return cmd_score(args)


if __name__ == "__main__":
    sys.exit(main())
