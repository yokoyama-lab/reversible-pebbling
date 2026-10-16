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
# (5, 9) は 9 個以上のペブルが乗る状態を含む小さい組（鍵の後半バイトに効く変異を速く判定するため。F(T_5,9)=105）
CASES = [(3, 5), (3, 4), (4, 6), (4, 5), (5, 7), (5, 6), (5, 9), (6, 8), (6, 7), (6, 9)]
KNOWN = {(3, 5): 17, (3, 4): -1, (4, 6): 53, (4, 5): -1, (5, 7): 155, (5, 6): -1, (5, 9): 105,
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


def run_one(exe: Path, h: int, p: int, lf: Path) -> tuple[str, int | None]:
    """1 組を走らせる。(異常の種類 "" / "timeout" / "rc=..", goal_depth)"""
    try:
        r = subprocess.run([str(exe), str(h), str(p), "--threads", "2", "--stop-at-goal", "0",
                            "--maxdepth", str(MAXDEPTH), "--layers", str(lf)],
                           capture_output=True, text=True, timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        return "timeout", None
    if r.returncode != 0:
        msg = (r.stderr.strip().splitlines() or ["(stderr 無し)"])[-1]
        return f"rc={r.returncode}: {msg}", None
    line = [x for x in r.stdout.splitlines() if x.startswith("RESULT")]
    if not line:
        return "RESULT 行が無い", None
    return "", int(line[0].split("goal_depth=")[1].split()[0])


def run_cases(exe: Path, outdir: Path, ctrl: Path | None = None) -> tuple[str, str]:
    """全 CASES を走らせる。対照 ctrl があれば各組の層ファイルをその場で比べる。
    戻り値 (判定, 詳細)。判定は "ok"（対照と全組一致）/ "M" / "layers" / "abort" / "timeout_only"。
    時間切れの組は飛ばして次の組へ進み、他の組で差が出なければ "timeout_only"（未判定）とする。"""
    outdir.mkdir(parents=True, exist_ok=True)
    timeouts = []
    for h, p in CASES:
        lf = outdir / f"h{h}_p{p}.txt"
        err, gd = run_one(exe, h, p, lf)
        if err == "timeout":
            # 打ち切った時点までに書かれた層が、対照の同じ深さの層とすでに食い違っていれば検出とする
            if ctrl is not None and lf.exists():
                part = lf.read_text().splitlines()
                ref = (ctrl / f"h{h}_p{p}.txt").read_text().splitlines()
                diff = [i for i in range(min(len(part), len(ref))) if part[i] != ref[i]]
                if diff:
                    return "layers", (f"h={h} p={p}: 時間切れ {TIMEOUT}s までに書かれた層の深さ {diff[0]} で対照と不一致"
                                      f"（{ref[diff[0]].split()[1]} 対 {part[diff[0]].split()[1]}）")
                if len(part) > len(ref):
                    return "layers", f"h={h} p={p}: 対照は {len(ref)} 行で終わるが、時間切れまでに {len(part)} 行を書いた"
            timeouts.append((h, p))
            continue
        if err:
            return "abort", f"h={h} p={p}: {err}"
        if gd != KNOWN[(h, p)]:
            return "M", f"h={h} p={p}: 既知 {KNOWN[(h, p)]} に対し {gd}"
        if ctrl is not None and not filecmp.cmp(lf, ctrl / f"h{h}_p{p}.txt", shallow=False):
            return "layers", f"h={h} p={p}: M は既知と同じ、層ごとの状態数が対照と不一致"
    if timeouts:
        return "timeout_only", f"時間切れ {TIMEOUT}s の組 {timeouts}（他の組は対照と一致）"
    return "ok", "対照と完全一致"


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
    v0, why0 = run_cases(fam / "control", fam / "control_out")
    assert v0 == "ok", f"対照が既知の値を再現しない: {why0}"
    lines.append(f"{name} 対照（無変異）: 既知の値 {len(KNOWN)} 点を再現 ○")
    det = undecided = 0
    label = {"M": "検出（M が既知と不一致）", "layers": "検出（層ごとの状態数が対照と不一致）",
             "abort": "検出（異常終了。不変条件の検査で停止を含む）", "timeout_only": "**未判定**（時間切れのみ）",
             "ok": "**未検出**"}
    for mname, (old, new) in muts.items():
        m = apply(src, old, new)
        (fam / f"{mname}.c").write_text(m)
        if not build(fam / f"{mname}.c", fam / mname):
            v, why = "abort", "コンパイル失敗"
        else:
            v, why = run_cases(fam / mname, fam / f"{mname}_out", fam / "control_out")
        det += v in ("M", "layers", "abort")
        undecided += v == "timeout_only"
        lines.append(f"  {mname}: {label[v]}（{why}）")
    lines.append(f"  {name}: {det}/{len(muts)} 検出" + (f"、未判定 {undecided}" if undecided else ""))
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
