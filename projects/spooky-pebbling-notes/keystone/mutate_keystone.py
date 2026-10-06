#!/usr/bin/env python3
"""Keystone.lean の変異注入（検出力と誤検出を対で測る）。

    python3 mutate_keystone.py <出力ディレクトリ（リポジトリの外）>

リポジトリの `SpookyPebblingExtra/Keystone.lean` は**読むだけ**。変異はすべて出力ディレクトリに
作ったコピーに対して行い、`lake env lean --root=<コピーの置き場> -o <olean> <コピー>` で検査する
（リポジトリには何も書かない）。

* 言明の変異（F*）: 定理の言明を**偽**にする。証明が通ったら検出漏れ。
* 証明の変異（P*）: 言明は真のまま、証明が頼っている補題を弱いものに差し替える。
  通ったら「その補題は要らなかった」ことになる。
* 対照（C*）: 無変異と、意味を変えない書き換え。落ちたら誤検出。
* 反証（R*）: F1..F10 の言明それぞれの**否定**を Lean で証明する（R0）。変異体が落ちたのは
  「偽の言明だから」であって、証明の台本が合わなかっただけではないことを示す。
  R1 は反証ファイル自体の変異（真の言明の否定を 1 本混ぜる）で、落ちることを期待する。

判定（**終了コードと沈黙だけを根拠にしない**）:

* 「通った」= rc=0 かつ error 行なし かつ **olean が今回の実行で生成された**
* 「落ちた」= rc=1 かつ error 行あり
* それ以外（124/137/143、olean が無いのに rc=0 など）は**未確定**。検出にも合格にも数えない
"""
from __future__ import annotations

import hashlib
import os
import re
import subprocess
import sys

REPO = "<local>/dev/github.com/yokoyama-lab/spooky-pebbling-lean"
SRC = os.path.join(REPO, "SpookyPebblingExtra", "Keystone.lean")

MAIN = "    ∀ n, theta s ≤ n → TUG n s ≤ TUP n s := by"
MAIN_HEAD = "theorem TUG_le_TUP_of_theta_le {s : ℕ} (hs : 2 ≤ s) :"

# (id, 種別, 説明, 置換前, 置換後, 期待)  期待: "fail" | "pass"
MUTANTS = [
    ("C0", "対照", "無変異", None, None, "pass"),
    ("C1", "対照", "本体の仮定を n ≥ θ(s) と書く（意味は同じ）",
     MAIN, "    ∀ n, n ≥ theta s → TUG n s ≤ TUP n s := by", "pass"),
    ("C2", "対照", "keystone の仮定を 4 ≤ s に強める（真のまま）",
     "theorem keystone {s n : ℕ} (hs : 3 ≤ s) (hn : B4 s ≤ n) : TUG n s ≤ TUP n s := by",
     "theorem keystone {s n : ℕ} (hs : 4 ≤ s) (hn : B4 s ≤ n) : TUG n s ≤ TUP n s := by", "pass"),
    ("F1", "言明", "本体の不等号を逆向きに（T_UP ≤ T_UG）",
     MAIN, "    ∀ n, theta s ≤ n → TUP n s ≤ TUG n s := by", "fail"),
    ("F2", "言明", "本体の n の下限を θ(s)-1 に広げる",
     MAIN, "    ∀ n, theta s ≤ n + 1 → TUG n s ≤ TUP n s := by", "fail"),
    ("F3", "言明", "本体の s の下限を 1 に広げる",
     MAIN_HEAD, "theorem TUG_le_TUP_of_theta_le {s : ℕ} (hs : 1 ≤ s) :", "fail"),
    ("F4", "言明", "本体の結論を T_UG + 2 ≤ T_UP に強める",
     MAIN, "    ∀ n, theta s ≤ n → TUG n s + 2 ≤ TUP n s := by", "fail"),
    ("F5", "言明", "keystone の n の下限を B4(s) から s に広げる",
     "theorem keystone {s n : ℕ} (hs : 3 ≤ s) (hn : B4 s ≤ n) : TUG n s ≤ TUP n s := by",
     "theorem keystone {s n : ℕ} (hs : 3 ≤ s) (hn : s ≤ n) : TUG n s ≤ TUP n s := by", "fail"),
    ("F6", "言明", "keystone_delta の符号を逆に（T_UG = T_UP + 1）",
     "theorem keystone_delta {s n : ℕ} (hs : 3 ≤ s) (hn : B4 s ≤ n) : TUP n s = TUG n s + 1 := by",
     "theorem keystone_delta {s n : ℕ} (hs : 3 ≤ s) (hn : B4 s ≤ n) : TUG n s = TUP n s + 1 := by",
     "fail"),
    ("F7", "言明", "補題2 の範囲を m ≥ s-1 に広げる",
     "    ∀ m, s ≤ m → TUP m s + 4 ≤ TUP (m + 1) s := by",
     "    ∀ m, s ≤ m + 1 → TUP m s + 4 ≤ TUP (m + 1) s := by", "fail"),
    ("F8", "言明", "補題1 の定数を 3 に強める",
     "    ∀ m, 1 ≤ m → TUP m s + 2 ≤ TUP (m + 1) s := by",
     "    ∀ m, 1 ≤ m → TUP m s + 3 ≤ TUP (m + 1) s := by", "fail"),
    ("F9", "言明", "尻尾の代価の定数を 4 に強める",
     "    (hqθ : q + 1 ≤ theta s) : TUG (q + 1) s ≤ TUP q s + 5 := by",
     "    (hqθ : q + 1 ≤ theta s) : TUG (q + 1) s ≤ TUP q s + 4 := by", "fail"),
    ("F10", "言明", "delta_sign の +1 側の範囲を n ≤ θ(s) に広げる",
     "    (n + 1 ≤ theta s → TUG n s = TUP n s + 1) ∧ (theta s ≤ n → TUP n s = TUG n s + 1) := by",
     "    (n ≤ theta s → TUG n s = TUP n s + 1) ∧ (theta s ≤ n → TUP n s = TUG n s + 1) := by",
     "fail"),
    ("P1", "証明", "場合B で補題2（+4）の代わりに補題1（+2）を使う",
     "        have h4 := TUP_succ_ge_four (s := s + 1) (by omega) i hi",
     "        have h4 := TUP_succ_ge_two (s := s + 1) (by omega) i (by omega)", "fail"),
    ("P2", "証明", "場合A で帰納法の仮定を使わない",
     "        have hih := ih q hA", "        have hih := le_refl (TUG q s)", "fail"),
    ("P3", "証明", "場合B で尻尾の代価の補題を使わない",
     "        have h5 := TUG_succ_le_TUP_add_five hs hq (by omega)",
     "        have h5 := le_refl (TUG (q + 1) s)", "fail"),
]

# F1..F10 の言明の否定を証明する Lean ソース。ビルド済みの SpookyPebblingExtra.Keystone を import する。
REFUTE = r'''/-
変異注入（`mutate_keystone.py`）で言明を書き換えた 10 本（F1..F10）が**本当に偽**であることの反証。
各 `example` は変異後の言明を仮定して矛盾を出す。反例の値は Lean 済みの閉形式から取る。
このソースは `mutate_keystone.py` が出力ディレクトリ（リポジトリの外）に書き出して検査する。
-/
import SpookyPebblingExtra.Keystone
open Spooky

theorem v_TUP_1_1 : TUP 1 1 = 1 := by
  have := TUP_eq_of_le' (k := 1) (s := 1) (by omega) (by omega); omega
theorem v_TUG_1_1 : TUG 1 1 = 2 := by
  have := TUG_eq_of_le' (n := 1) (s := 1) (by omega) (by omega); omega
theorem v_TUP_1_2 : TUP 1 2 = 1 := by
  have := TUP_eq_of_le' (k := 1) (s := 2) (by omega) (by omega); omega
theorem v_TUP_2_2 : TUP 2 2 = 3 := by
  have := TUP_eq_of_le' (k := 2) (s := 2) (by omega) (by omega); omega
theorem v_TUG_2_2 : TUG 2 2 = 4 := by
  have := TUG_eq_of_le' (n := 2) (s := 2) (by omega) (by omega); omega
theorem v_TUP_3_2 : TUP 3 2 = 9 := by
  have := TUP_cap2 (n := 3) (by omega); omega
theorem v_TUG_3_2 : TUG 3 2 = 8 := by
  have := TUG_cap2 (n := 3) (by omega); omega
theorem v_TUP_3_3 : TUP 3 3 = 5 := by
  have := TUP_eq_of_le' (k := 3) (s := 3) (by omega) (by omega); omega
theorem v_TUG_3_3 : TUG 3 3 = 6 := by
  have := TUG_eq_of_le' (n := 3) (s := 3) (by omega) (by omega); omega

/-- F1: 不等号を逆向きに。反例 `(n,s) = (3,2)`: `T_UP = 9 > 8 = T_UG`。 -/
example : ¬ (∀ s : ℕ, 2 ≤ s → ∀ n, theta s ≤ n → TUP n s ≤ TUG n s) := by
  intro h
  have h1 := h 2 le_rfl 3 (by decide)
  have := v_TUP_3_2; have := v_TUG_3_2
  omega

/-- F2: `n` の下限を `θ(s)-1` に。反例 `(2,2)`: `T_UG = 4 > 3 = T_UP`。 -/
example : ¬ (∀ s : ℕ, 2 ≤ s → ∀ n, theta s ≤ n + 1 → TUG n s ≤ TUP n s) := by
  intro h
  have h1 := h 2 le_rfl 2 (by decide)
  have := v_TUP_2_2; have := v_TUG_2_2
  omega

/-- F3: `s` の下限を 1 に。反例 `(1,1)`: `T_UG = 2 > 1 = T_UP`。 -/
example : ¬ (∀ s : ℕ, 1 ≤ s → ∀ n, theta s ≤ n → TUG n s ≤ TUP n s) := by
  intro h
  have h1 := h 1 le_rfl 1 (by decide)
  have := v_TUP_1_1; have := v_TUG_1_1
  omega

/-- F4: 結論を `T_UG + 2 ≤ T_UP` に。反例 `(3,2)`: `8 + 2 > 9`。 -/
example : ¬ (∀ s : ℕ, 2 ≤ s → ∀ n, theta s ≤ n → TUG n s + 2 ≤ TUP n s) := by
  intro h
  have h1 := h 2 le_rfl 3 (by decide)
  have := v_TUP_3_2; have := v_TUG_3_2
  omega

/-- F5: `keystone` の下限を `s ≤ n` に。反例 `(3,3)`: `T_UG = 6 > 5 = T_UP`。 -/
example : ¬ (∀ s n : ℕ, 3 ≤ s → s ≤ n → TUG n s ≤ TUP n s) := by
  intro h
  have h1 := h 3 3 le_rfl le_rfl
  have := v_TUP_3_3; have := v_TUG_3_3
  omega

/-- F6: 符号を逆に。反例 `(9,3)`: 要石から `T_UP = T_UG + 1`。 -/
example : ¬ (∀ s n : ℕ, 3 ≤ s → B4 s ≤ n → TUG n s = TUP n s + 1) := by
  intro h
  have h1 := h 3 9 le_rfl (by decide)
  have h2 := keystone_delta (s := 3) (n := 9) le_rfl (by decide)
  omega

/-- F7: 補題2 の範囲を `m ≥ s-1` に。反例 `s = 2`・`m = 1`: `1 + 4 > 3`。 -/
example : ¬ (∀ s : ℕ, 2 ≤ s → ∀ m, s ≤ m + 1 → TUP m s + 4 ≤ TUP (m + 1) s) := by
  intro h
  have h1 := h 2 le_rfl 1 (by omega)
  have h2 : TUP (1 + 1) 2 = 3 := v_TUP_2_2
  have := v_TUP_1_2
  omega

/-- F8: 補題1 の定数を 3 に。反例 `s = 2`・`m = 1`: `1 + 3 > 3`。 -/
example : ¬ (∀ s : ℕ, 2 ≤ s → ∀ m, 1 ≤ m → TUP m s + 3 ≤ TUP (m + 1) s) := by
  intro h
  have h1 := h 2 le_rfl 1 le_rfl
  have h2 : TUP (1 + 1) 2 = 3 := v_TUP_2_2
  have := v_TUP_1_2
  omega

/-- F9: 尻尾の代価の定数を 4 に。反例 `s = 2`・`q = 2`: `T_UG(3,2) = 8 > 3 + 4`。 -/
example : ¬ (∀ s q : ℕ, 2 ≤ s → 1 ≤ q → q + 1 ≤ theta s → TUG (q + 1) s ≤ TUP q s + 4) := by
  intro h
  have h1 := h 2 2 le_rfl (by omega) (by decide)
  have h2 : TUG (2 + 1) 2 = 8 := v_TUG_3_2
  have := v_TUP_2_2
  omega

/-- F10: `δ = +1` の範囲を `n ≤ θ(s)` に。反例 `(3,2)`: `T_UG = 8 ≠ 9 + 1`。 -/
example : ¬ (∀ s n : ℕ, 2 ≤ s → 1 ≤ n → n ≤ theta s → TUG n s = TUP n s + 1) := by
  intro h
  have h1 := h 2 3 le_rfl (by omega) (by decide)
  have := v_TUP_3_2; have := v_TUG_3_2
  omega
'''

REFUTE_OLD = "example : ¬ (∀ s : ℕ, 2 ≤ s → ∀ n, theta s ≤ n → TUP n s ≤ TUG n s) := by"
REFUTE_NEW = "example : ¬ (∀ s : ℕ, 2 ≤ s → ∀ n, theta s ≤ n → TUG n s ≤ TUP n s) := by"


def sha(path: str) -> str:
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def decl_at(lines: list[str], lineno: int) -> str:
    for i in range(min(lineno, len(lines)) - 1, -1, -1):
        m = re.match(r"(theorem|example|lemma|def)\s*([A-Za-z_0-9']*)", lines[i])
        if m:
            return m.group(2) or m.group(1)
    return "?"


def replace_once(mid: str, src: str, old: str, new: str) -> str:
    cnt = src.count(old)
    if cnt != 1:
        raise RuntimeError(f"{mid}: 置換前の文字列が {cnt} 回現れる（1 回であるべき）")
    text = src.replace(old, new)
    if text == src:
        raise RuntimeError(f"{mid}: 置換しても変わらなかった")
    return text


def check(out: str, mid: str, fname: str, text: str):
    """コピーを書き、lean に掛け、(判定, rc, error 行, warning 数, olean の有無) を返す。"""
    d = os.path.join(out, mid)
    os.makedirs(d, exist_ok=True)
    path = os.path.join(d, fname)
    olean = os.path.splitext(path)[0] + ".olean"
    if os.path.exists(olean):  # 前回の成果物を今回の合格と数えない
        os.remove(olean)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    cmd = ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=24G",
           "-p", "MemorySwapMax=0", "timeout", "600", "lake", "env", "lean",
           f"--root={d}", "-o", olean, path]  # -o は入力が --root の下に在ることを要求する
    r = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True)
    log = r.stdout + r.stderr
    with open(os.path.join(d, "lean.log"), "w", encoding="utf-8") as f:
        f.write(log + f"\nrc={r.returncode}\n")
    errs = re.findall(re.escape(fname) + r":(\d+):(\d+): error", log)
    warns = len(re.findall(re.escape(fname) + r":\d+:\d+: warning", log))
    made = os.path.isfile(olean) and os.path.getmtime(olean) >= os.path.getmtime(path)
    if r.returncode == 0 and not errs and made:
        got = "pass"
    elif r.returncode == 1 and errs:
        got = "fail"
    else:
        got = f"未確定(rc={r.returncode},olean={'有' if made else '無'})"
    return got, r.returncode, errs, warns, made


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    out = os.path.realpath(sys.argv[1])
    repo = os.path.realpath(REPO)
    if out == repo or out.startswith(repo + os.sep):
        raise RuntimeError("出力ディレクトリがリポジトリの中にある。変異はリポジトリの外で行う")
    os.makedirs(out, exist_ok=True)
    src = open(SRC, encoding="utf-8").read()
    before = sha(SRC)
    print(f"原本 sha256 = {before}")

    jobs = []
    for mid, kind, desc, old, new, expect in MUTANTS:
        text = src if old is None else replace_once(mid, src, old, new)
        jobs.append((mid, kind, desc, "Keystone.lean", text, expect))
    jobs.append(("R0", "反証", "F1..F10 の言明の否定を証明する", "MutantsAreFalse.lean",
                 REFUTE, "pass"))
    jobs.append(("R1", "反証", "反証ファイルの変異（F1 の代わりに真の言明の否定）",
                 "MutantsAreFalse.lean", replace_once("R1", REFUTE, REFUTE_OLD, REFUTE_NEW),
                 "fail"))

    rows = []
    for mid, kind, desc, fname, text, expect in jobs:
        got, rc, errs, warns, made = check(out, mid, fname, text)
        lines = text.split("\n")
        where = sorted({decl_at(lines, int(ln)) for ln, _ in errs})
        verdict = "期待どおり" if got == expect else "⚠ 期待と違う"
        rows.append((mid, kind, expect, got, verdict))
        print(f"{mid:<4} {kind} 期待={expect:<4} 実際={got:<4} rc={rc} error={len(errs)} "
              f"warning={warns} olean={'有' if made else '無'} {verdict}  {desc}"
              + (f"  ［error の場所: {', '.join(where)}］" if where else ""), flush=True)

    after = sha(SRC)
    print(f"原本 sha256 = {after}（{'不変' if after == before else '⚠ 変わった'}）")

    def tally(kind: str, want: str) -> str:
        sel = [r for r in rows if r[1] == kind and r[2] == want]
        return f"{sum(r[3] == want for r in sel)}/{len(sel)}"

    print(f"\n言明の変異: {tally('言明', 'fail')} 検出")
    print(f"証明の変異: {tally('証明', 'fail')} 検出")
    ctl = [r for r in rows if r[1] == "対照"]
    print(f"対照: {tally('対照', 'pass')} 通過（誤検出 {sum(r[3] == 'fail' for r in ctl)}）")
    print(f"反証: 本体 {tally('反証', 'pass')} 通過、反証の変異 {tally('反証', 'fail')} 検出")
    print(f"未確定: {sum(r[3].startswith('未確定') for r in rows)}")
    bad = [r for r in rows if r[4] != "期待どおり"]
    return 1 if (bad or after != before) else 0


if __name__ == "__main__":
    raise SystemExit(main())
