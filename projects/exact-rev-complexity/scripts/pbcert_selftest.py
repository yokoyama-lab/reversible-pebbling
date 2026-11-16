#!/usr/bin/env python3
"""**道具が効いていることの自己試験**（2026-09-05）。

`~/dev/TOOLS.md` に入っている **VeriPB 3.0.2** と **dpr-trim** は、
`topic-mining/exp/toolcombo/FINDINGS.md` §1 の実測でコードからの使用実績が 0 だった。
数字を出す前に「**正しい証明を受理し、壊した証明を拒否する**」を対で確かめる。

⚠ **エラーが出ないことは道具が働いた証拠にならない。** 陰性対照を必ず通すこと。

各ケースは (入力, 証明, 期待) の三つ組。期待は `accept` か `reject`。
`accept` を期待したものが reject されたら道具の設置が壊れている。
`reject` を期待したものが accept されたら**その道具の判定は信用できない**。

実行:  python3 scripts/pbcert_selftest.py
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile

DPR_TRIM_EXAMPLES = "<local>/opt/tools/dpr-trim"

# ---------------------------------------------------------------- VeriPB ----

# (A) 明らかに実行不能: x1+x2+x3 >= 2 かつ x1+x2+x3 <= 1
OPB_A = """* #variable= 3 #constraint= 2
1 x1 1 x2 1 x3 >= 2 ;
1 ~x1 1 ~x2 1 ~x3 >= 2 ;
"""

# (B) 基数制約の伝播が要る実行不能: x1+x2+x3+x4>=3, x1+x2<=1, x3+x4<=1
OPB_B = """* #variable= 4 #constraint= 3
1 x1 1 x2 1 x3 1 x4 >= 3 ;
1 ~x1 1 ~x2 >= 1 ;
1 ~x3 1 ~x4 >= 1 ;
"""

# (C) (B) から 1 本落とした**充足可能**な系: x1=x2=0, x3=x4=1 が解
OPB_C = """* #variable= 4 #constraint= 2
1 x1 1 x2 1 x3 1 x4 >= 2 ;
1 ~x1 1 ~x2 >= 1 ;
"""

PBP_A_OK = """pseudo-Boolean proof version 3.0
f 2;
pol 1 2 +;
output NONE;
conclusion UNSAT;
end pseudo-Boolean proof;
"""

# 陰性対照: 足す相手を間違えた（1+1 では矛盾にならない）。1 行だけ違う。
PBP_A_BAD = PBP_A_OK.replace("pol 1 2 +;", "pol 1 1 +;")

PBP_B_OK = """pseudo-Boolean proof version 3.0
f 3;
rup 1 ~x1 >= 1;
rup 1 ~x2 >= 1;
rup >= 1;
output NONE;
conclusion UNSAT;
end pseudo-Boolean proof;
"""

# 陰性対照: 充足可能な系 (C) に対して「x1 は必ず 0」を RUP と称する。
# 実際には x1=1, x2=0, x3=1, x4=0 が解なので RUP ではない。
PBP_C_BAD_RUP = """pseudo-Boolean proof version 3.0
f 2;
rup 1 ~x1 >= 1;
output NONE;
conclusion NONE;
end pseudo-Boolean proof;
"""

# 陰性対照: 充足可能な系 (C) に対して矛盾を導かずに UNSAT と結論する。
PBP_C_BAD_CONCL = """pseudo-Boolean proof version 3.0
f 2;
output NONE;
conclusion UNSAT;
end pseudo-Boolean proof;
"""

VERIPB_CASES = [
    ("veripb/pol_pos          正しい pol 証明（実行不能な系 A）", OPB_A, PBP_A_OK, "accept"),
    ("veripb/pol_neg_arith    pol の足し算を 1 行壊した", OPB_A, PBP_A_BAD, "reject"),
    ("veripb/rup_pos          基数伝播を使う u 証明（実行不能な系 B）", OPB_B, PBP_B_OK, "accept"),
    ("veripb/rup_neg_unimplied 充足可能な系 C で成り立たない rup を主張", OPB_C, PBP_C_BAD_RUP, "reject"),
    ("veripb/concl_neg        充足可能な系 C を矛盾なしに UNSAT と結論", OPB_C, PBP_C_BAD_CONCL, "reject"),
]


def run_veripb(opb: str, pbp: str, timeout: int = 120):
    d = tempfile.mkdtemp(prefix="pbcert_selftest_")
    try:
        f_opb, f_pbp = os.path.join(d, "f.opb"), os.path.join(d, "f.pbp")
        open(f_opb, "w").write(opb)
        open(f_pbp, "w").write(pbp)
        r = subprocess.run(["veripb", "--opb", f_opb, f_pbp],
                           capture_output=True, text=True, timeout=timeout)
        out = (r.stdout + r.stderr).strip()
        return r.returncode, out
    finally:
        shutil.rmtree(d, ignore_errors=True)


def veripb_verdict(rc: int, out: str) -> str:
    """VeriPB の受理/拒否。終了コードだけで読まない（実行失敗と区別する）。"""
    low = out.lower()
    if rc == 0 and ("succeeded" in low or "verified" in low):
        return "accept"
    return "reject"


# -------------------------------------------------------------- dpr-trim ----

def php(pigeons: int, holes: int) -> str:
    """鳩の巣 PHP(p,h)。p > h なら UNSAT。変数 v(i,j) = 鳩 i が穴 j。"""
    def v(i, j):
        return i * holes + j + 1
    cls = []
    for i in range(pigeons):                       # 各鳩はどこかに入る
        cls.append([v(i, j) for j in range(holes)])
    for j in range(holes):                         # 各穴は高々 1 羽
        for i1 in range(pigeons):
            for i2 in range(i1 + 1, pigeons):
                cls.append([-v(i1, j), -v(i2, j)])
    head = f"p cnf {pigeons * holes} {len(cls)}\n"
    return head + "".join(" ".join(map(str, c)) + " 0\n" for c in cls)


def check_proof(tool: str, cnf_path: str, proof_path: str, timeout: int = 900):
    r = subprocess.run([tool, cnf_path, proof_path],
                       capture_output=True, text=True, timeout=timeout)
    out = (r.stdout + r.stderr).replace("\r", "")
    verdict = "reject"
    for ln in out.splitlines():
        if ln.strip() == "s VERIFIED":
            verdict = "accept"
        if ln.strip() in ("s NOT VERIFIED", "s TRIVIAL UNSAT"):
            verdict = "reject"
    return verdict, r.returncode, out


def corrupt_line(text: str, idx: int) -> str:
    """証明の idx 行目の**先頭リテラルの符号を反転**する（1 行だけ壊す）。"""
    lines = text.splitlines()
    toks = lines[idx].split()
    for i, t in enumerate(toks):
        if t not in ("0", "d") and (t.lstrip("-").isdigit()):
            toks[i] = str(-int(t))
            break
    lines[idx] = " ".join(toks)
    return "\n".join(lines) + "\n"


def main() -> int:
    fails = 0
    print("=" * 78)
    print("VeriPB 3.0.2 自己試験（陽性・陰性の対）")
    print("=" * 78)
    for name, opb, pbp, want in VERIPB_CASES:
        rc, out = run_veripb(opb, pbp)
        got = veripb_verdict(rc, out)
        ok = got == want
        fails += 0 if ok else 1
        first = out.splitlines()[-1] if out.splitlines() else "(出力なし)"
        print(f"  [{'OK ' if ok else '**NG**'}] {name}")
        print(f"          期待={want:6s} 実際={got:6s} rc={rc}  << {first[:90]}")

    print()
    print("=" * 78)
    print("dpr-trim 自己試験（陽性・陰性の対）")
    print("=" * 78)
    d = tempfile.mkdtemp(prefix="pbcert_dpr_")
    try:
        # --- (1)(2) 素の DRAT: 自作 PHP(4,3) を cadical に解かせる ---
        cnf = os.path.join(d, "php43.cnf")
        open(cnf, "w").write(php(4, 3))
        drat = os.path.join(d, "php43.drat")
        subprocess.run(["cadical", cnf, drat, "--binary=false"],
                       capture_output=True, text=True, timeout=300)
        n_drat = len(open(drat).read().splitlines())
        got, rc, _ = check_proof("dpr-trim", cnf, drat)
        ok = got == "accept"
        fails += 0 if ok else 1
        print(f"  [{'OK ' if ok else '**NG**'}] dpr/drat_pos  PHP(4,3) の cadical DRAT（{n_drat} 行）"
              f" 期待=accept 実際={got} rc={rc}")

        # 陰性対照は「充足可能な系を反駁できないこと」で取る。
        # ⚠ 実測（2026-09-05）: UNSAT な系の DRAT はリテラルを 1 つ反転しても
        #    **たいてい別の妥当な証明になる**（単位が溜まった文脈では何でも RUP／RAT
        #    になり、dpr-trim は既定で PR として読むのでさらに通りやすい）。
        #    php43.drat の 1 行目・14 行目を反転しても forward/backward の両方で
        #    `s VERIFIED` だった。**これは検査器の失敗ではない。**
        #    したがって「1 行壊す」型の陰性対照は、証明が本当に無効になる壊し方
        #    ——充足可能な系を反駁する——で取る。
        sat_cnf = os.path.join(d, "php44.cnf")
        open(sat_cnf, "w").write(php(4, 4))          # 鳩 4・穴 4 = 充足可能
        bogus = os.path.join(d, "php44_bogus.drat")
        open(bogus, "w").write("1 0\n-1 0\n0\n")     # 含意されない単位から矛盾を主張
        got, rc, _ = check_proof("dpr-trim", sat_cnf, bogus)
        ok = got == "reject"
        fails += 0 if ok else 1
        print(f"  [{'OK ' if ok else '**NG**'}] dpr/drat_neg  充足可能な PHP(4,4) を反駁したと主張"
              f"     期待=reject 実際={got} rc={rc}")

        # --- (3)(4) DPR 固有: 同梱の hole20（PR 証明つき） ---
        h20 = os.path.join(DPR_TRIM_EXAMPLES, "cnf", "hole20.cnf")
        p20 = os.path.join(DPR_TRIM_EXAMPLES, "proof", "hole20.pr")
        if os.path.exists(h20) and os.path.exists(p20):
            n_pr = len(open(p20).read().splitlines())
            got, rc, _ = check_proof("dpr-trim", h20, p20)
            ok = got == "accept"
            fails += 0 if ok else 1
            print(f"  [{'OK ' if ok else '**NG**'}] dpr/dpr_pos   hole20 の PR 証明（{n_pr} 行）"
                  f"        期待=accept 実際={got} rc={rc}")

            badp = os.path.join(d, "hole20_bad.pr")
            open(badp, "w").write(corrupt_line(open(p20).read(), 0))
            got, rc, _ = check_proof("dpr-trim", h20, badp)
            ok = got == "reject"
            fails += 0 if ok else 1
            print(f"  [{'OK ' if ok else '**NG**'}] dpr/dpr_neg   同じ PR 証明の 1 行目を壊した"
                  f"           期待=reject 実際={got} rc={rc}")

            # --- (5) 「DPR は DRAT より強い」の対照: drat-trim は同じ証明を通さない ---
            got, rc, out = check_proof("drat-trim", h20, p20, timeout=900)
            ok = got == "reject"
            fails += 0 if ok else 1
            print(f"  [{'OK ' if ok else '**NG**'}] dpr/drat_cannot drat-trim に同じ PR 証明を渡す"
                  f"          期待=reject 実際={got} rc={rc}")
        else:
            print("  [SKIP] hole20 の同梱例が見つからない")
    finally:
        shutil.rmtree(d, ignore_errors=True)

    print()
    if fails:
        print(f"**自己試験 NG: {fails} 件。この道具で出した数字を使ってはいけない。**")
        return 1
    print("自己試験 すべて OK（陽性は受理・陰性は拒否）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
