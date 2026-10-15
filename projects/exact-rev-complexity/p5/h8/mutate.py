#!/usr/bin/env python3
"""変異注入: fbfs.c（A）・fbfs_b.c（B）・check_seq.py の検出力を測る.

元のファイルはリポジトリの外（作業ディレクトリ WORK）へコピーしてから 1 か所ずつ書き換える。
リポジトリ内のファイルには触れない。各変異は「元の文字列がちょうど 1 回現れる」ことを
確かめてから置換する（置換が空振りした変異を「検出」と数えない）。

検出の判定:
  A・B: 校正の組 CASES の各 (h, p) で層ごとの状態数のファイルを出させ、無変異の対照と
        比べる。1 つでも違えば（またはコンパイル失敗・異常終了・時間切れなら）検出。
  check_seq: 合法な手順（F の証人）を受理し、不合法な手順 3 種をすべて棄却するのが対照。
        変異がどれか 1 つでも判定を変えたら検出。
対照（無変異のコピー）が CASES で既知の値を再現し、リポジトリ内の版と同じ出力になることも確かめる。

    python3 mutate.py <WORK ディレクトリ>   # 例: scratchpad の下
"""
from __future__ import annotations

import filecmp
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CASES = [(3, 5), (3, 4), (4, 6), (4, 5), (5, 7), (5, 6), (6, 8), (6, 7), (6, 9)]
KNOWN = {(3, 5): 17, (3, 4): -1, (4, 6): 53, (4, 5): -1, (5, 7): 155, (5, 6): -1,
         (6, 8): 429, (6, 7): -1, (6, 9): 339}
MAXDEPTH = 1500
TIMEOUT = 120

MUT_A = {
    "A1_freeremove_level": ("    int ok = avail(j - 1, L) && avail(j - 1, R);\n",
                            "    int ok = (avail(j - 1, L) && avail(j - 1, R)) || b;\n"),
    "A2_budget_half1": ("                        if (c + s1[k].d > budget) continue;\n",
                        "                        if (c + s1[k].d > budget + 1) continue;\n"),
    "A3_never_B_moves": ("        if (B != A) {", "        if (B != A && 0) {"),
    "A4_never_half2": ("                    if (h2 != h1) {\n", "                    if (0) {\n"),
    "A5_root_or": ("                    int rok = half_b(h1) && half_b(h2);\n",
                   "                    int rok = half_b(h1) || half_b(h2);\n"),
    "A6_node_unsorted": ("    if (L > R) { uint32_t t = L; L = R; R = t; }\n    int c = b",
                         "    int c = b"),
    "A7_no_prev_check": ("                        if (set_contains(prev, y, hh)) continue;\n                        if (set_insert(next, y, hh) && y.lo == goal.lo && y.hi == goal.hi) found = 1;\n                    }\n                    /* 半分 2",
                         "                        if (set_insert(next, y, hh) && y.lo == goal.lo && y.hi == goal.hi) found = 1;\n                    }\n                    /* 半分 2"),
    "A8_cnt_drops_b": ("    int c = b + (j >= 2 ?", "    int c = 0 + (j >= 2 ?"),
    "A9_half_unsorted": ("    if (h1 > h2) { uint64_t t = h1; h1 = h2; h2 = t; }\n", ""),
    "A10_half_cnt_no_b": ("static inline int half_cnt(uint64_t h) { return half_b(h) + ",
                          "static inline int half_cnt(uint64_t h) { return 0 + "),
}

MUT_B = {
    "B1_cands_children_or": ("    if (b[l] && b[r] && (b[a] || pc < P)) out[n++] = a;",
                             "    if ((b[l] || b[r]) && (b[a] || pc < P)) out[n++] = a;"),
    "B2_cands_budget": ("    if (sc[a] == 0) { if (pc < P) out[n++] = leftleaf[a]; return n; }",
                        "    if (sc[a] == 0) { if (pc <= P) out[n++] = leftleaf[a]; return n; }"),
    "B3_no_fix": ("for (int a = par[v]; a >= 0; a = par[a]) fix(c, a);",
                  "for (int a = par[v]; a >= 0 && 0; a = par[a]) fix(c, a);"),
    "B4_fix_parent_only": ("for (int a = par[v]; a >= 0; a = par[a]) fix(c, a);",
                           "for (int a = par[v]; a >= 0; a = -1) fix(c, a);"),
    "B5_never_right": ("    if (!same) n = cands(b, sc, r, pc, out, n);",
                       "    if (0) n = cands(b, sc, r, pc, out, n);"),
    "B6_same_by_count": ("    int same = sc[l] == sc[r] && memcmp(b + l, b + r, (size_t)blen[l]) == 0;",
                         "    int same = sc[l] == sc[r];"),
    "B7_no_prev_check": ("                        if (hs_has(prev, &nb[j], h)) continue;\n", ""),
    "B8_remove_without_children": ("    if (b[l] && b[r] && (b[a] || pc < P)) out[n++] = a;",
                                   "    if ((b[a] || (b[l] && b[r])) && (b[a] || pc < P)) out[n++] = a;"),
    "B9_goal_wrong": ("b[0] = 1; pack(b, &goal);", "b[1] = 1; pack(b, &goal);"),
    "B10_sc_self_only": ("for (int a = pt->k[i].p[t]; a >= 0; a = par[a]) sc[a]++;",
                         "for (int a = pt->k[i].p[t]; a >= 0; a = -1) sc[a]++;"),
    "B11_put_on_subtree_root": ("    if (sc[a] == 0) { if (pc < P) out[n++] = leftleaf[a]; return n; }",
                                "    if (sc[a] == 0) { if (pc < P) out[n++] = a; return n; }"),
    "B12_pack_skips_nonzero": ("        if (!w) continue;", "        if (w) continue;"),
    "B13_key_eq_8bytes": ("static inline int steq(const St *a, const St *b) { return memcmp(a, b, sizeof *a) == 0; }",
                          "static inline int steq(const St *a, const St *b) { return memcmp(a, b, 8) == 0; }"),
    "B14_fix_wrong_dir": ("    if (memcmp(b + l, b + r, (size_t)m) > 0) {", "    if (memcmp(b + l, b + r, (size_t)m) < 0) {"),
    # 打つ直前の合法性の再検査は cands と重複する保険なので、単独の変異は検出されなくて正しい（等価変異の対照）
    "B15_recheck_or_EXPECTED_EQUIV": ("                        if (lch[v] >= 0 && !(b[lch[v]] && b[rch[v]])) { err |= 16; continue; }",
                                      "                        if (lch[v] >= 0 && !(b[lch[v]] || b[rch[v]])) { err |= 16; continue; }"),
}

MUT_C = {
    "C1_children_or": ("        if lc < n and not (peb[lc] and peb[rc]):",
                       "        if lc < n and not (peb[lc] or peb[rc]):"),
    "C2_budget_plus1": ("        if count > S:", "        if count > S + 1:"),
    "C3_no_final_check": ("    if final != [0]:", "    if False:"),
    "C4_put_only_check": ("        if lc < n and not (peb[lc] and peb[rc]):",
                          "        if not peb[v] and lc < n and not (peb[lc] and peb[rc]):"),
}


def apply(src: str, old: str, new: str) -> str:
    k = src.count(old)
    if k != 1:
        raise SystemExit(f"変異の置換元が {k} 回現れる（1 回でなければならない）: {old[:60]!r}")
    return src.replace(old, new)


def build(c_path: Path, exe: Path) -> bool:
    r = subprocess.run(["gcc", "-O2", "-fopenmp", "-o", str(exe), str(c_path)], capture_output=True)
    return r.returncode == 0


def run_cases(exe: Path, outdir: Path) -> tuple[str, dict]:
    """全 CASES を走らせ、層ファイルを outdir に置く。(異常の理由 or "", {case: goal_depth})"""
    outdir.mkdir(parents=True, exist_ok=True)
    got = {}
    for h, p in CASES:
        lf = outdir / f"h{h}_p{p}.txt"
        try:
            r = subprocess.run([str(exe), str(h), str(p), "--threads", "2", "--stop-at-goal", "0",
                                "--maxdepth", str(MAXDEPTH), "--layers", str(lf)],
                               capture_output=True, text=True, timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            return f"時間切れ {TIMEOUT}s（h={h} p={p}）", got
        if r.returncode != 0:
            msg = (r.stderr.strip().splitlines() or ["(stderr 無し)"])[-1]
            return f"rc={r.returncode}（h={h} p={p}: {msg}）", got
        line = [x for x in r.stdout.splitlines() if x.startswith("RESULT")]
        if not line:
            return f"RESULT 行が無い（h={h} p={p}）", got
        gd = int(line[0].split("goal_depth=")[1].split()[0])
        got[(h, p)] = gd
        if gd != KNOWN[(h, p)]:  # 既知と違えば以降の組は走らせない（時間の節約）
            return "", got
    return "", got


def same_layers(a: Path, b: Path) -> bool:
    return all(filecmp.cmp(a / f"h{h}_p{p}.txt", b / f"h{h}_p{p}.txt", shallow=False) for h, p in CASES)


def c_family(name: str, fname: str, muts: dict, work: Path) -> list[str]:
    lines = []
    src = (HERE / fname).read_text()
    fam = work / name
    if fam.exists():
        shutil.rmtree(fam)
    fam.mkdir(parents=True)
    # 対照
    (fam / "control.c").write_text(src)
    assert build(fam / "control.c", fam / "control"), "対照がコンパイルできない"
    why0, got = run_cases(fam / "control", fam / "control_out")
    assert not why0, f"対照が異常終了: {why0}"
    assert got == KNOWN, f"対照が既知の値を再現しない: {got}"
    lines.append(f"{name} 対照（無変異）: 既知の値 {len(KNOWN)} 点を再現 ○")
    det = 0
    for mname, (old, new) in muts.items():
        m = apply(src, old, new)
        (fam / f"{mname}.c").write_text(m)
        if not build(fam / f"{mname}.c", fam / mname):
            verdict, why = True, "コンパイル失敗"
        else:
            whym, gotm = run_cases(fam / mname, fam / f"{mname}_out")
            if whym:
                verdict, why = True, f"異常終了: {whym}"
            elif gotm != KNOWN:
                diff = {k: (KNOWN[k], gotm[k]) for k in KNOWN if k in gotm and gotm[k] != KNOWN[k]}
                verdict, why = True, f"M が既知と不一致 {diff}"
            elif not same_layers(fam / "control_out", fam / f"{mname}_out"):
                verdict, why = True, "M は一致、層ごとの状態数が対照と不一致"
            else:
                verdict, why = False, "対照と完全一致"
        det += verdict
        lines.append(f"  {mname}: {'検出' if verdict else '**未検出**'}（{why}）")
    lines.append(f"  {name}: {det}/{len(muts)} 検出")
    return lines


def checker_family(work: Path) -> list[str]:
    lines = []
    src = (HERE / "check_seq.py").read_text()
    fam = work / "C"
    if fam.exists():
        shutil.rmtree(fam)
    fam.mkdir(parents=True)
    wit = HERE / "logs" / "witness_h6_p8.txt"
    moves = [x for x in wit.read_text().splitlines() if not x.startswith("#")]
    bad_illegal = fam / "bad_illegal.txt"     # 先頭で根を置く（子がそろっていない）
    bad_illegal.write_text("\n".join(["0"] + moves) + "\n")
    bad_final = fam / "bad_final.txt"          # 最後の手を落とす（終端に余分なペブル）
    bad_final.write_text("\n".join(moves[:-1]) + "\n")
    tests = [(6, 8, wit, 0), (6, 7, wit, 1), (6, 8, bad_illegal, 1), (6, 8, bad_final, 1)]
    # bad_remove: 子のない状態で外す手（葉以外を、子がそろわない時点で外す）
    # F の証人では内部頂点を外すとき子がそろっているので、子の一方を先に外してから親を外す列を作る。
    # 証人の最初の内部頂点の置く手の直後に、その左の子を外し、続けてその頂点を外す
    n = 63
    seq = [int(x) for x in moves]
    for i, v in enumerate(seq):
        if 2 * v + 1 < n:
            lc = 2 * v + 1
            bad_rm = seq[: i + 1] + [lc, v]
            break
    bad_remove = fam / "bad_remove.txt"
    bad_remove.write_text("\n".join(map(str, bad_rm)) + "\n")
    tests.append((6, 8, bad_remove, 1))
    # 子の条件「だけ」を破る手順（他の条件は満たし、終端は根のみ）。T_3（根 0、1 の子 3,4）、S=5。
    w3 = [x for x in (HERE / "logs" / "witness_h3_p5.txt").read_text().splitlines() if not x.startswith("#")]
    rm1 = fam / "bad_remove_onechild.txt"   # 3,4 を置き 1 を置き、3 を外してから 1 を外す（子 3 が無い）
    rm1.write_text("\n".join(["3", "4", "1", "3", "1", "4"] + w3) + "\n")
    put1 = fam / "bad_put_onechild.txt"      # 3 だけ置いて 1 を置く（子 4 が無い）、1 と 3 を戻す
    put1.write_text("\n".join(["3", "1", "1", "3"] + w3) + "\n")
    ok3 = fam / "ok_h3.txt"                  # 合法な前置き（3,4,1 を置き 1,3,4 を外す）＋証人
    ok3.write_text("\n".join(["3", "4", "1", "1", "3", "4"] + w3) + "\n")
    tests += [(3, 5, rm1, 1), (3, 5, put1, 1), (3, 5, ok3, 0)]

    def judge(script: Path) -> list[int]:
        return [subprocess.run([sys.executable, "-I", str(script), str(h), str(s), str(f)],
                               capture_output=True).returncode for h, s, f, _ in tests]
    (fam / "control.py").write_text(src)
    ctrl = judge(fam / "control.py")
    want = [t[3] for t in tests]
    assert ctrl == want, f"対照の判定が期待と違う: {ctrl} != {want}"
    lines.append(f"C 対照（無変異）: 合法 {want.count(0)} 件を受理・不合法 {want.count(1)} 件を棄却 ○")
    det = 0
    for mname, (old, new) in MUT_C.items():
        (fam / f"{mname}.py").write_text(apply(src, old, new))
        got = judge(fam / f"{mname}.py")
        verdict = got != want
        det += verdict
        lines.append(f"  {mname}: {'検出' if verdict else '**未検出**'}（判定 {got}、対照 {want}）")
    lines.append(f"  C: {det}/{len(MUT_C)} 検出")
    return lines


def main() -> None:
    work = Path(sys.argv[1]).resolve()
    repo = HERE.parent.parent  # exact-rev-complexity
    if repo in work.parents or work == repo:
        raise SystemExit("WORK はリポジトリの外に置くこと")
    work.mkdir(parents=True, exist_ok=True)
    out = []
    out += c_family("A", "fbfs.c", MUT_A, work)
    out += c_family("B", "fbfs_b.c", MUT_B, work)
    out += checker_family(work)
    print("\n".join(out))


if __name__ == "__main__":
    main()
