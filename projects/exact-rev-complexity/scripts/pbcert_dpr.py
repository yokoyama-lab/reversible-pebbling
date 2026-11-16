#!/usr/bin/env python3
"""**dpr-trim（DPR/PR 証明）を DRAT と対で測る**（2026-09-06）。

副題: 「ピラミッドの UNSAT は対称性が巨大なので DPR なら短くなる見込み」——本当か。

⚠ **その前提は `pbcert_symmetry2.py` で棄却された**（抽象 CNF の実効的な自己同型群は
**位数 1**。7.46e46 は全部「どの節にも現れない変数」の見かけ）。そこで本スクリプトは
次の 3 つを**測って**、副題に決着をつける:

1. **道具が我々の系で効くか**: ピラミッドの DRAT 証明を `dpr-trim` に通し、`drat-trim`
   と検査時間・判定を対で測る（DRAT ⊂ DPR なので受理されるはず）。
   **陰性対照は我々の系で取る**（証明の打ち切り・充足可能側の偽反駁・別インスタンス）。
2. **PR が効く系での基準点**: 鳩の巣 PHP(n+1,n) は対称群 S_{n+1}×S_n をもつ。
   Heule–Kiesl–Biere の PR 証明を**生成し**、同じ式の cadical DRAT と対で測る。
   ⇒「対称性が本物ならこれだけ縮む」という物差しが得られる。
3. **我々の系で同じことができるか**: できない。理由は 2 つとも機械で確かめた（下記）。

**測る前に決めた「終わったら何が言えるか」**:

* ピラミッド側で `dpr-trim` が受理しても、それは **DRAT 証明を DPR 検査器に通しただけ**で
  「DPR が短い」証拠にはならない（同じファイルなのでサイズは同一）。**サイズの主張は
  PR 固有の推論を含む証明を作れたときにだけしてよい。**
* PHP 側で PR が DRAT より小さくても、それは PHP の話であってピラミッドの話ではない。
  **対称性の位数（測定済み）を介してしか繋がらない。**
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
import time

DPR_DIR = "<local>/opt/tools/dpr-trim"


# ------------------------------------------------------------------ PHP ----

def php_cnf(pigeons: int, holes: int) -> tuple[int, list[list[int]]]:
    """変数番号は hole20.cnf と同じ v(i,j) = (i-1)*holes + j（1 始まり）。"""
    def v(i, j):
        return (i - 1) * holes + j
    cls = [[v(i, j) for j in range(1, holes + 1)] for i in range(1, pigeons + 1)]
    for j in range(1, holes + 1):
        for i1 in range(1, pigeons + 1):
            for i2 in range(i1 + 1, pigeons + 1):
                cls.append([-v(i1, j), -v(i2, j)])
    return pigeons * holes, cls


def php_pr_proof(N: int, explicit_empty: bool = True) -> str:
    """PHP(N+1, N) の PR 証明（Heule–Kiesl–Biere）。

    穴 n を 1 つずつ落として PHP(n, n-1) に帰着する。各段で、鳩 i (1..n) と
    「余った鳩」m=n+1 を入れ替える PR 節を並べ、最後に単位節 ¬x_{i,n} を出す:

        節 (¬x_{i,n} ∨ ¬x_{m,j})  witness {¬x_{i,n}, ¬x_{m,j}, x_{i,j}, x_{m,n}}
        節 (¬x_{i,n})                                        （ここは RUP）

    ⚠ 変数番号は**元の式の列幅 N のまま**（hole20.pr と同じ規約）。
    `--selftest` で同梱の `hole20.pr` を**行単位で完全に再現**できることを確かめてある。

    ⚠ **同梱の hole20.pr には空節の行が無い**（2026-09-06 実測）。最後の単位節まで来ると
    単位伝播だけで矛盾が出るので、検査器はそれで受理する。`explicit_empty=False` で
    同梱と同じ形、`True` で空節を 1 行足した形になる（どちらも受理される）。
    **だから「空節の行を落とす」は破壊にならない＝陰性対照に使えない。**
    """
    def v(i, j):
        return (i - 1) * N + j
    out = []
    for n in range(N, 1, -1):
        m = n + 1
        for i in range(1, n + 1):
            for j in range(1, n):
                c = [-v(i, n), -v(m, j)]
                w = [-v(i, n), -v(m, j), v(i, j), v(m, n)]
                out.append(" ".join(map(str, c + w)) + " 0")
            out.append(f"{-v(i, n)} 0")
    if explicit_empty:
        out.append("0")
    return "\n".join(out) + "\n"


def write_cnf(path: str, nv: int, cls: list[list[int]]) -> None:
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")


# ------------------------------------------------------------ 検査の実行 ----

def size(path: str) -> tuple[int, int]:
    d = open(path, "rb").read()
    return len(d), d.count(b"\n")


def check(tool: str, cnf: str, proof: str, timeout: int, extra: list[str] | None = None):
    """(判定, 秒, 生出力の末尾)。**打ち切りは「拒否」と区別する。**"""
    t0 = time.time()
    try:
        r = subprocess.run([tool, cnf, proof] + (extra or []),
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "打ち切り", float(timeout), ""
    el = time.time() - t0
    out = (r.stdout + r.stderr).replace("\r", "")
    verdict = "reject"
    for ln in out.splitlines():
        if ln.strip() == "s VERIFIED":
            verdict = "accept"
        if ln.strip() in ("s NOT VERIFIED", "s TRIVIAL UNSAT"):
            verdict = "reject"
    return verdict, el, out.strip().splitlines()[-1][:80] if out.strip() else ""


def solve_drat(cnf: str, drat: str, timeout: int):
    t0 = time.time()
    try:
        r = subprocess.run(["cadical", cnf, drat, "--binary=false"],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "打ち切り", float(timeout)
    st = next((ln for ln in r.stdout.splitlines() if ln.startswith("s ")), "(s 行なし)")
    return st, time.time() - t0


# -------------------------------------------------------------- 自己試験 ----

def selftest(timeout: int) -> int:
    bad = 0
    print("=" * 92)
    print("dpr-trim 自己試験その 2: **PR 証明を自分で生成できることを、同梱例との一致で示す**")
    print("=" * 92)
    ref = os.path.join(DPR_DIR, "proof", "hole20.pr")
    ref_lines = open(ref).read().strip().splitlines()
    gen_lines = php_pr_proof(20, explicit_empty=False).strip().splitlines()
    same = ref_lines == gen_lines
    bad += 0 if same else 1
    print(f"  [{'OK ' if same else '**NG**'}] 生成した PR 証明が同梱 hole20.pr と"
          f"{'**行単位で完全一致**' if same else '**不一致**'}（{len(gen_lines):,} 行）")
    print(f"        ⚠ 同梱 hole20.pr には**空節の行が無い**（単位伝播で矛盾が出るため）。"
          f"以降は空節を 1 行足した版を使う")
    gen = php_pr_proof(20)

    d = tempfile.mkdtemp(prefix="pbcert_dpr_")
    try:
        cnf = os.path.join(d, "hole20.cnf")
        nv, cls = php_cnf(21, 20)
        write_cnf(cnf, nv, cls)
        with open(os.path.join(DPR_DIR, "cnf", "hole20.cnf")) as f:
            ref_cnf = f.read()
        ok = open(cnf).read().split() == ref_cnf.split()
        bad += 0 if ok else 1
        print(f"  [{'OK ' if ok else '**NG**'}] 生成した CNF が同梱 hole20.cnf と"
              f"{'一致' if ok else '**不一致**'}")

        pr = os.path.join(d, "gen.pr")
        open(pr, "w").write(gen)
        v, s, _ = check("dpr-trim", cnf, pr, timeout)
        bad += 0 if v == "accept" else 1
        print(f"  [{'OK ' if v == 'accept' else '**NG**'}] 陽性: 生成した PR 証明を dpr-trim が"
              f" {v}（{s:.2f}s）")

        # 陰性 1: witness を 1 個だけ壊す（入れ替え先を間違える）
        lines = gen.splitlines()
        t = lines[0].split()
        t[-2] = str(-int(t[-2]))
        bad_pr = os.path.join(d, "bad_witness.pr")
        open(bad_pr, "w").write("\n".join([" ".join(t)] + lines[1:]) + "\n")
        v, s, msg = check("dpr-trim", cnf, bad_pr, timeout)
        bad += 0 if v == "reject" else 1
        print(f"  [{'OK ' if v == 'reject' else '**NG**'}] 陰性: witness を 1 個壊すと"
              f" {v}（{s:.2f}s）<< {msg}")

        # 陰性 2: 証明を半分に切る（穴の消去が途中までなので矛盾は出ないはず）
        cut = os.path.join(d, "cut.pr")
        open(cut, "w").write("\n".join(lines[:len(lines) // 2]) + "\n0\n")
        v, s, msg = check("dpr-trim", cnf, cut, timeout)
        bad += 0 if v == "reject" else 1
        print(f"  [{'OK ' if v == 'reject' else '**NG**'}] 陰性: 証明を半分で切って空節を主張"
              f" → {v}（{s:.2f}s）<< {msg}")

        # 参考: 空節の行を落としても受理される（＝破壊になっていない）。控えておく
        cut2 = os.path.join(d, "noempty.pr")
        open(cut2, "w").write("\n".join(lines[:-1]) + "\n")
        v, s, _ = check("dpr-trim", cnf, cut2, timeout)
        print(f"  [参考] 空節の行を落とす → {v}（{s:.2f}s）。"
              f"**受理される＝陰性対照にはならない**（単位伝播が矛盾を出す）")

        # 陰性 3: 充足可能な PHP(20,20) を同じ証明で反駁したと主張
        sat = os.path.join(d, "php2020.cnf")
        nv2, cls2 = php_cnf(20, 20)
        write_cnf(sat, nv2, cls2)
        v, s, msg = check("dpr-trim", sat, pr, timeout)
        bad += 0 if v == "reject" else 1
        print(f"  [{'OK ' if v == 'reject' else '**NG**'}] 陰性: 充足可能な PHP(20,20) に"
              f"同じ証明を渡すと {v}（{s:.2f}s）<< {msg}")
    finally:
        import shutil
        shutil.rmtree(d, ignore_errors=True)

    print()
    print("自己試験その 2 すべて OK" if bad == 0 else f"**NG: {bad} 件。数字を使ってはいけない**")
    return bad


# ---------------------------------------------------------------- 本番 ----

def run_php(ns: list[int], d: str, timeout: int) -> None:
    print("\n" + "=" * 108)
    print("A. **対称性が本物のとき**: PHP(n+1,n)（対称群 S_{n+1}×S_n）で PR と DRAT を対で測る")
    print("=" * 108)
    print(f"  {'n':>3} {'変数':>6} {'節':>7} | {'DRAT 証明':>14} {'行':>9} {'解 s':>7} "
          f"{'drat-trim':>10} | {'PR 証明':>12} {'行':>8} {'dpr-trim':>10} | {'DRAT/PR':>9}")
    for n in ns:
        cnf = os.path.join(d, f"php{n+1}_{n}.cnf")
        nv, cls = php_cnf(n + 1, n)
        write_cnf(cnf, nv, cls)
        drat = cnf + ".drat"
        st, solve_s = solve_drat(cnf, drat, timeout)
        if st == "s UNSATISFIABLE":
            db, dl = size(drat)
            dv, ds, _ = check("drat-trim", cnf, drat, timeout)
        else:
            db = dl = 0
            dv, ds = st, 0.0
        pr = os.path.join(d, f"php{n+1}_{n}.pr")
        open(pr, "w").write(php_pr_proof(n))
        pb, pl = size(pr)
        pv, ps, _ = check("dpr-trim", cnf, pr, timeout)
        ratio = f"{db / pb:.1f}x" if db and pb else "—"
        print(f"  {n:>3} {nv:>6} {len(cls):>7} | {db:>14,} {dl:>9,} {solve_s:>7.2f} "
              f"{dv+'/'+format(ds,'.2f')+'s':>10} | {pb:>12,} {pl:>8,} "
              f"{pv+'/'+format(ps,'.2f')+'s':>10} | {ratio:>9}")


def up_refutable(cls: list[list[int]]) -> bool:
    """式が**単位伝播だけで**反駁できるか（素朴実装）。

    ⚠ これを見ずに陰性対照を作ると嘘をつく。2026-09-06 に実際に踏んだ:
    抽象 CNF **h=5 B=9 は UP だけで矛盾する**ので、`0` だけの空の証明さえ
    `s VERIFIED` になる。そこで作った「証明を半分に切る」陰性対照は**無意味**だった
    （検査器は壊れていない）。以降、陰性対照に使う系は必ずここで篩う。
    """
    val: dict[int, bool] = {}
    for c in cls:
        if len(c) == 1:
            l = c[0]
            if val.get(abs(l)) is not None and val[abs(l)] != (l > 0):
                return True
            val[abs(l)] = l > 0
    changed = True
    while changed:
        changed = False
        for c in cls:
            un, sat = [], False
            for l in c:
                v = val.get(abs(l))
                if v is None:
                    un.append(l)
                elif v == (l > 0):
                    sat = True
                    break
            if sat:
                continue
            if not un:
                return True
            if len(un) == 1:
                l = un[0]
                val[abs(l)] = l > 0
                changed = True
    return False


def run_pyramid(hs: list[int], d: str, timeout: int, veripb_dir: str = "") -> None:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import pbcert_pyr_opb as enc
    from pbcert_measure import L_ABSTRACT

    print("\n" + "=" * 116)
    print("B. **我々の系**: ピラミッドの抽象 CNF。DRAT 証明を drat-trim と dpr-trim の両方に通す")
    print("   ⚠ DRAT ⊂ DPR なので受理は当然。**証明ファイルは同一なのでサイズは同じ**＝")
    print("      これは「DPR が短い」証拠ではない。PR 固有の推論を含む証明を作れて初めて言える。")
    print("   ⚠ `UP` 欄が「可」の系は**単位伝播だけで矛盾する**＝空の証明でも受理される。")
    print("      サイズの比較にも陰性対照にも使ってはいけない。")
    print("=" * 116)
    print(f"  {'h':>3} {'B':>3} {'変数':>8} {'UP':>4} | {'DRAT 生':>13} {'行':>9} | "
          f"{'DRAT 芯(-l)':>13} {'行':>8} {'生/芯':>7} | {'drat-trim':>16} | {'dpr-trim':>16}")
    keep: dict = {}
    rows: list = []
    for h in hs:
        B = L_ABSTRACT[h] - 1
        cnf = os.path.join(d, f"pyr_h{h}B{B}.cnf")
        pb = enc.build(h, B)
        nv, nc = pb.dump_cnf(cnf)
        upr = up_refutable(pb.to_cnf()[1])
        drat = cnf + ".drat"
        st, solve_s = solve_drat(cnf, drat, timeout)
        if st != "s UNSATISFIABLE":
            print(f"  {h:>3} {B:>3} {nv:>8} {'可' if upr else '不可':>4} | cadical: {st}")
            continue
        db, dl = size(drat)
        core = drat + ".core"
        v1, s1, _ = check("drat-trim", cnf, drat, timeout, ["-l", core])
        cb, cl_ = size(core) if os.path.exists(core) else (0, 0)
        v2, s2, _ = check("dpr-trim", cnf, drat, timeout)
        print(f"  {h:>3} {B:>3} {nv:>8} {'**可**' if upr else '不可':>4} | {db:>13,} {dl:>9,} | "
              f"{cb:>13,} {cl_:>8,} {(db / cb if cb else 0):>6.1f}x | "
              f"{v1 + ' / ' + format(s1, '.2f') + 's':>16} | "
              f"{v2 + ' / ' + format(s2, '.2f') + 's':>16}")
        if not upr:
            keep[h] = (cnf, drat, B)
        rows.append((h, B, cnf, drat, core, db, cb, upr))

    if veripb_dir:
        print("\n" + "=" * 116)
        print("C. **トリムを揃えると結論が変わる**: drat-trim には証明を芯まで削る機能があるが、")
        print("   VeriPB 3.0.2 には無い（`--elaborate` は逆に展開する）。**片側だけ削った比較**に")
        print("   なるので、生・芯・芯(-O) の 3 通りを並べる。⚠ 芯は独立に再検査して s VERIFIED。")
        print("=" * 116)
        print(f"  {'h':>3} | {'CNF':>10} {'DRAT 生':>11} {'芯(-l)':>9} {'芯(-O)':>9} 再検査 | "
              f"{'OPB':>10} {'VeriPB':>9} | {'生/PB':>7} {'PB/芯O':>7} | {'式+証明 DRAT':>13}"
              f" {'式+証明 PB':>11} {'比':>6}")
        for h, B, cnf, drat, core, db, cb, upr in rows:
            if upr:
                continue
            pbp = os.path.join(veripb_dir, f"h{h}B{B}.pbp")
            opb = os.path.join(veripb_dir, f"h{h}B{B}.clean.opb")
            if not (os.path.exists(pbp) and os.path.exists(opb)):
                continue
            coreO = drat + ".coreO"
            check("drat-trim", cnf, drat, timeout, ["-l", coreO, "-O"])
            ob = size(coreO)[0] if os.path.exists(coreO) else 0
            rv, _, _ = check("drat-trim", cnf, coreO, timeout)
            vb = size(pbp)[0]
            fb, fo = size(cnf)[0], size(opb)[0]
            print(f"  {h:>3} | {fb:>10,} {db:>11,} {cb:>9,} {ob:>9,} {rv:>6} | "
                  f"{fo:>10,} {vb:>9,} | {db / vb:>6.1f}x {vb / ob if ob else 0:>6.1f}x | "
                  f"{fb + ob:>13,} {fo + vb:>11,} {(fb + ob) / (fo + vb):>5.1f}x")

    if not keep:
        print("\n  **陰性対照に使える系が無い**（すべて UP で反駁できてしまう）。ここで止める。")
        return
    h = sorted(keep)[-1]                     # UP で落ちない中で一番大きい h
    cnf, drat, B = keep[h]
    print(f"\n  --- 陰性対照（**我々の系で**取る。h={h} B={B}。UP だけでは反駁できない系）---")

    # 門: 空の証明が拒否されることを先に確かめる（ここが accept なら以降は無意味）
    empty = drat + ".empty"
    open(empty, "w").write("0\n")
    okgate = True
    for tool in ("drat-trim", "dpr-trim"):
        v, s, msg = check(tool, cnf, empty, timeout)
        okgate &= (v == "reject")
        print(f"  [{'OK ' if v == 'reject' else '**NG**'}] {tool:<9} **門**: 空の証明だけ"
              f" → {v}（{s:.2f}s）<< {msg}")
    if not okgate:
        print("  **門で落ちた。この系では陰性対照が成立しないので、以降の判定は書かない。**")
        return

    lines = open(drat).read().splitlines()
    cut = drat + ".cut"
    open(cut, "w").write("\n".join(lines[:len(lines) // 2]) + "\n0\n")
    for tool in ("drat-trim", "dpr-trim"):
        v, s, msg = check(tool, cnf, cut, timeout)
        print(f"  [{'OK ' if v == 'reject' else '**NG**'}] {tool:<9} 証明を半分で切って空節を主張"
              f" → {v}（{s:.2f}s）<< {msg}")

    sat_cnf = os.path.join(os.path.dirname(cnf), f"pyr_h{h}B{B+1}.cnf")
    enc.build(h, B + 1).dump_cnf(sat_cnf)
    bogus = os.path.join(os.path.dirname(cnf), "bogus.drat")
    open(bogus, "w").write("1 0\n-1 0\n0\n")
    for tool in ("drat-trim", "dpr-trim"):
        v, s, msg = check(tool, sat_cnf, bogus, timeout)
        print(f"  [{'OK ' if v == 'reject' else '**NG**'}] {tool:<9} 充足可能側（B={B+1}）を"
              f"偽の証明で反駁 → {v}（{s:.2f}s）<< {msg}")
    for tool in ("drat-trim", "dpr-trim"):
        v, s, msg = check(tool, sat_cnf, drat, timeout)
        print(f"  [{'OK ' if v == 'reject' else '**NG**'}] {tool:<9} 充足可能側（B={B+1}）に"
              f"UNSAT 側の証明 → {v}（{s:.2f}s）<< {msg}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--php", default="", help="カンマ区切りの n（PHP(n+1,n)）")
    ap.add_argument("--pyramid", default="", help="カンマ区切りの h")
    ap.add_argument("--dir", default="")
    ap.add_argument("--veripb-dir", default="",
                    help="pbcert_measure.py が .pbp を書いたディレクトリ（トリム後比較用）")
    ap.add_argument("--timeout", type=int, default=600)
    a = ap.parse_args()
    if a.selftest:
        return 1 if selftest(a.timeout) else 0
    if not a.dir:
        print("--dir が要る", file=sys.stderr)
        return 2
    os.makedirs(a.dir, exist_ok=True)
    if a.php:
        run_php([int(x) for x in a.php.split(",")], a.dir, a.timeout)
    if a.pyramid:
        run_pyramid([int(x) for x in a.pyramid.split(",")], a.dir, a.timeout,
                    a.veripb_dir)
    return 0


if __name__ == "__main__":
    sys.exit(main())
