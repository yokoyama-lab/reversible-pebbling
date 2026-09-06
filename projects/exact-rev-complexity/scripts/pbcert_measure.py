#!/usr/bin/env python3
"""**DRAT と VeriPB を対で測る**（2026-09-05）。

問い: 「ピラミッドのピーク制約は基数制約そのものなので、VeriPB の擬似ブール証明に
すれば DRAT より証明が小さくなるはずだ」——これは本当か。

同じ抽象（`pbcert_pyr_opb.build`。CNF は `q2_pyr_lower_cert.build` と節単位で一致することを
`--check` で確認済み）を 2 経路に流す:

* **DRAT 経路**: CNF（ピークは Sinz 逐次カウンタ）→ `cadical` → `drat-trim`
* **PB 経路**  : OPB（ピークは基数制約 1 本）→ `Exact 2.2.1` → 1.1→2.0 変換 → `veripb`

**測る前に決めた「終わったら何が言えるか」**:

* UNSAT 側（`B = L(h) - 1`）で両経路が検証に成功したときだけ、証明サイズを比べてよい。
  片方が打ち切られたら「未確定」であって「大きい」ではない。
* SAT 側（`B = L(h)`）は**充足解が出るだけで証明は出ない**。ここで測れるのは
  「両経路が同じ結論を出すか」だけで、サイズの比較はできない（片側しか結論が出ない測定）。
* 「小さくなる」の判定は**証明ファイルのバイト数**で行う。式（CNF/OPB）のサイズは
  別欄に出す（符号化の差であって証明の差ではない）。

**健全性の担保**: Exact は式を自分で書き直す（実測: 自明な制約を落とす）。VeriPB が
検証するのは Exact の式なので、**Exact の式が我々の OPB の部分集合であること**を毎回
確かめる（`_check_subset`）。部分集合なら「Exact の式が実行不能 ⟹ 我々の系も実行不能」。
**確かめられなければ止まる**（fail-closed）。
"""
from __future__ import annotations

import argparse
import collections
import os
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pbcert_pyr_opb as enc  # noqa: E402

# 抽象の最適値 L(h)。2026-09-05 に `q2_pyr_lower.py --hmax 16 --limit 240` で
# **すべて「最適」として再計算した**（打ち切りは 1 件も無い）。h<=12 では実測 p_min と一致し、
# h>=13 では実測より小さい（緩和なので当然）。
L_ABSTRACT = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16, 8: 20, 9: 23, 10: 26,
              11: 29, 12: 32, 13: 35, 14: 38, 15: 41, 16: 44}

RUN_EXACT = r'''
import sys, time
from exact import Exact
def parse_opb(path):
    cons = []; maxv = 0
    for ln in open(path):
        ln = ln.strip()
        if not ln or ln.startswith("*") or ln.startswith("min:"): continue
        body, rhs = ln.split(">=")
        deg = int(rhs.replace(";", "").strip())
        toks = body.split(); terms = []; i = 0
        while i < len(toks):
            coef = int(toks[i]); lit = toks[i+1]; i += 2
            neg = lit.startswith("~")
            v = int(lit.lstrip("~").lstrip("x")); maxv = max(maxv, v)
            if neg: terms.append((-coef, "x%d" % v)); deg -= coef
            else:   terms.append((coef, "x%d" % v))
        cons.append((terms, deg))
    return cons, maxv
opb, prefix = sys.argv[1], sys.argv[2]
cons, maxv = parse_opb(opb)
s = Exact([("proof-log", prefix), ("verbosity", "0")])
for v in range(1, maxv + 1):
    s.addVariable("x%d" % v, 0, 1)
for terms, deg in cons:
    s.addConstraint(terms, True, deg, False, 0)
t0 = time.time()
st = s.runFull(False, 0)
print("EXACT_RESULT %s %.3f" % (st, time.time() - t0))
'''


def _norm_opb(path: str) -> collections.Counter:
    """OPB を「正規化した制約の多重集合」にする（比較用）。"""
    out: collections.Counter = collections.Counter()
    for ln in open(path):
        s = ln.strip()
        if not s or s.startswith("*") or s.startswith("min:"):
            continue
        body, _, rhs = s.partition(">=")
        deg = int(rhs.replace(";", "").strip())
        toks = body.split()
        terms = []
        i = 0
        while i < len(toks):
            c = int(toks[i])
            lit = toks[i + 1]
            i += 2
            v = int(lit.lstrip("~").lstrip("x"))
            terms.append((c, -v if lit.startswith("~") else v))
        out[(tuple(sorted(terms)), deg)] += 1
    return out


def _check_subset(exact_formula: str, ours: str) -> tuple[bool, str]:
    a, b = _norm_opb(ours), _norm_opb(exact_formula)
    extra = b - a
    if extra:
        k, v = next(iter(extra.items()))
        return False, f"Exact の式に我々の OPB に無い制約が {sum(extra.values())} 本ある（例 {k}×{v}）"
    dropped = sum((a - b).values())
    return True, f"部分集合 OK（Exact が落とした制約 {dropped} 本 / 我々 {sum(a.values())} 本）"


def _size(path: str) -> tuple[int, int]:
    """(バイト数, 行数)。**バイト数は実測**（0.0MB 表示に騙されないため）。"""
    data = open(path, "rb").read()
    return len(data), data.count(b"\n")


def run_drat(h: int, B: int, d: str, timeout: int):
    cnf = os.path.join(d, f"h{h}B{B}.cnf")
    drat = cnf + ".drat"
    nv, nc = enc.build(h, B).dump_cnf(cnf)
    t0 = time.time()
    try:
        r = subprocess.run(["cadical", cnf, drat, "--binary=false"],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return dict(status="打ち切り(cadical)", nv=nv, nc=nc, formula_bytes=_size(cnf)[0])
    solve_s = time.time() - t0
    st = next((ln for ln in r.stdout.splitlines() if ln.startswith("s ")), "(s 行なし)")
    res = dict(status=st, nv=nv, nc=nc, formula_bytes=_size(cnf)[0], solve_s=solve_s)
    if st != "s UNSATISFIABLE":
        return res
    pb, pl = _size(drat)
    res.update(proof_bytes=pb, proof_lines=pl)
    t0 = time.time()
    try:
        v = subprocess.run(["drat-trim", cnf, drat],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        res.update(check="打ち切り(drat-trim)", check_s=float(timeout))
        return res
    res.update(check_s=time.time() - t0,
               check=next((ln.strip() for ln in v.stdout.replace("\r", "").splitlines()
                           if ln.strip() in ("s VERIFIED", "s NOT VERIFIED")), "(判定行なし)"))
    return res


def run_pb(h: int, B: int, d: str, timeout: int, exact_python: str):
    opb = os.path.join(d, f"h{h}B{B}.opb")
    nv, nc = enc.build(h, B).dump_opb(opb)
    prefix = os.path.join(d, f"h{h}B{B}")
    runner = os.path.join(d, "_run_exact.py")
    open(runner, "w").write(RUN_EXACT)
    t0 = time.time()
    try:
        r = subprocess.run([exact_python, runner, opb, prefix],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return dict(status="打ち切り(Exact)", nv=nv, nc=nc, formula_bytes=_size(opb)[0])
    solve_s = time.time() - t0
    line = next((ln for ln in r.stdout.splitlines() if ln.startswith("EXACT_RESULT")), "")
    st = line.split()[1] if line else f"(結果行なし rc={r.returncode})"
    res = dict(status=st, nv=nv, nc=nc, formula_bytes=_size(opb)[0], solve_s=solve_s)
    if st != "UNSAT":
        return res

    raw_proof, raw_formula = prefix + ".proof", prefix + ".formula"
    ok, msg = _check_subset(raw_formula, opb)
    res["subset"] = msg
    if not ok:
        res["status"] = "**健全性検査で停止**: " + msg
        return res

    # VeriPB は空の目的関数 `min: ;` があると最適化問題として扱うので落とす
    clean = prefix + ".clean.opb"
    body = [ln for ln in open(raw_formula).read().splitlines()
            if ln.strip() and not ln.startswith("min:") and not ln.startswith("*")]
    with open(clean, "w") as f:
        f.write(f"* #variable= {nv} #constraint= {len(body)}\n")
        f.write("\n".join(body) + "\n")
    if _norm_opb(clean) != _norm_opb(raw_formula):
        res["status"] = "**健全性検査で停止**: 目的関数を落とす際に制約が変わった"
        return res

    import pbcert_pbp11to20 as tr
    pbp = prefix + ".pbp"
    try:
        open(pbp, "w").write(tr.translate(open(raw_proof).read(), len(body)))
    except tr.TranslationError as e:
        res["status"] = f"**変換できない**: {e}"
        res["raw_proof_bytes"] = _size(raw_proof)[0]
        return res

    res["raw_proof_bytes"], res["raw_proof_lines"] = _size(raw_proof)
    pb, pl = _size(pbp)
    res.update(proof_bytes=pb, proof_lines=pl)
    t0 = time.time()
    try:
        v = subprocess.run(["veripb", "--opb", clean, pbp],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        res.update(check="打ち切り(veripb)", check_s=float(timeout))
        return res
    out = (v.stdout + v.stderr)
    res.update(check_s=time.time() - t0,
               check=("s VERIFIED" if "s VERIFIED UNSATISFIABLE" in out else "s NOT VERIFIED"))
    return res


def fmt(r: dict) -> str:
    if "proof_bytes" not in r:
        return f"{r['status']:<24} 式 {r.get('formula_bytes', 0):>10,} B"
    return (f"{r['status']:<18} 式 {r['formula_bytes']:>9,} B / {r['nv']:>6} 変数 "
            f"| 証明 {r['proof_bytes']:>10,} B / {r['proof_lines']:>7,} 行 "
            f"| 解 {r.get('solve_s', 0):7.2f}s 検 {r.get('check_s', 0):7.2f}s "
            f"| {r.get('check', '-')}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--hs", default="3,4,5,6,7", help="カンマ区切りの h")
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--dir", required=True, help="中間ファイルの置き場（scratchpad）")
    ap.add_argument("--exact-python", default=os.environ.get("PBCERT_EXACT_PYTHON", ""),
                    help="Exact 2.2.1 が入った python")
    ap.add_argument("--sat-side", action="store_true", help="B = L(h) 側（充足）も測る")
    a = ap.parse_args()
    if not a.exact_python:
        print("--exact-python か PBCERT_EXACT_PYTHON が要る", file=sys.stderr)
        return 2
    os.makedirs(a.dir, exist_ok=True)

    for h in [int(x) for x in a.hs.split(",")]:
        L = L_ABSTRACT.get(h)
        if L is None:
            print(f"h={h}: L(h) 未算出。飛ばす")
            continue
        for B, tag in ([(L - 1, "UNSAT 側")] + ([(L, "SAT 側")] if a.sat_side else [])):
            print(f"\n=== h={h}  B={B}  ({tag}; L({h})={L}) ===", flush=True)
            rd = run_drat(h, B, a.dir, a.timeout)
            print(f"  DRAT  : {fmt(rd)}", flush=True)
            rp = run_pb(h, B, a.dir, a.timeout, a.exact_python)
            print(f"  VeriPB: {fmt(rp)}", flush=True)
            if "subset" in rp:
                print(f"          健全性: {rp['subset']}")
            if "raw_proof_bytes" in rp:
                print(f"          Exact 生証明 {rp['raw_proof_bytes']:,} B / "
                      f"{rp.get('raw_proof_lines', 0):,} 行（1.1 形式）")
            if "proof_bytes" in rd and "proof_bytes" in rp:
                ratio = rd["proof_bytes"] / rp["proof_bytes"]
                print(f"  ⇒ 証明サイズ DRAT/VeriPB = {ratio:.2f}×"
                      f"（{'VeriPB が小さい' if ratio > 1 else 'DRAT が小さい'}）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
