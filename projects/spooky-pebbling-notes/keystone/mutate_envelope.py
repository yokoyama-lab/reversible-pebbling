#!/usr/bin/env python3
"""Envelope.lean の変異注入（検出力と誤検出を対で測る）。道具立ては mutate_keystone.py と同じ。

    python3 mutate_envelope.py <出力ディレクトリ（リポジトリの外）>

* 言明の変異（G*）: 定理の言明を**偽**にする。G5 だけは定義 `brk` の底を変える
  （偽であることの根拠は `check_envelope.py` の変異 N3 の数値）。
* 証明の変異（PE*）: 言明は真のまま、証明が頼っている仮定を自明なものに差し替える。
* 対照（CE*）: 無変異と、意味を変えない書き換え。
* 反証（RE0）: G1〜G4・G6〜G10 の言明の否定を Lean で証明する。RE1 は反証ファイルの変異。

判定は mutate_keystone.py と同じ 3 値（通った＝rc=0・error なし・olean 生成／落ちた＝rc=1・error あり／未確定）。
"""
from __future__ import annotations

import os
import sys

from mutate_keystone import REPO, check, decl_at, replace_once, sha

SRC = os.path.join(REPO, "SpookyPebblingExtra", "Envelope.lean")

RANGE = "theorem TUP_le_envelope : ∀ m s, 2 ≤ s → ∀ n, brk m s ≤ n → n ≤ brk (m + 1) s →"
CONC = "    TUP n s + bb (m + 1) s ≤ 2 * (m + 1) * n := by\n  intro m\n  induction m with"

MUTANTS = [
    ("CE0", "対照", "無変異", None, None, "pass"),
    ("CE1", "対照", "上界の仮定を brk (m+1) s ≥ n と書く（意味は同じ）",
     RANGE, "theorem TUP_le_envelope : ∀ m s, 2 ≤ s → ∀ n, brk m s ≤ n → brk (m + 1) s ≥ n →",
     "pass"),
    ("CE2", "対照", "brk_two の等式の左右を入れ替える（意味は同じ）",
     "theorem brk_two {s : ℕ} (hs : 2 ≤ s) : brk 2 s + 1 = theta s := by",
     "theorem brk_two {s : ℕ} (hs : 2 ≤ s) : theta s = brk 2 s + 1 := by", "pass"),
    ("G1", "言明", "区間の右端を brk (m+1) s + 1 に広げる",
     RANGE, "theorem TUP_le_envelope : ∀ m s, 2 ≤ s → ∀ n, brk m s ≤ n → n ≤ brk (m + 1) s + 1 →",
     "fail"),
    ("G2", "言明", "区間の左端を brk m s - 1 に広げる",
     RANGE, "theorem TUP_le_envelope : ∀ m s, 2 ≤ s → ∀ n, brk m s ≤ n + 1 → n ≤ brk (m + 1) s →",
     "fail"),
    ("G3", "言明", "上界の s の下限を 1 に広げる",
     RANGE, "theorem TUP_le_envelope : ∀ m s, 1 ≤ s → ∀ n, brk m s ≤ n → n ≤ brk (m + 1) s →",
     "fail"),
    ("G4", "言明", "上界の傾きを 2m にずらす",
     CONC, "    TUP n s + bb (m + 1) s ≤ 2 * m * n := by\n  intro m\n  induction m with", "fail"),
    ("G5", "言明", "定義 brk の底を brk m 2 = m + 1 に変える",
     "  | (t + 2), 2 => t + 2", "  | (t + 2), 2 => t + 3", "fail"),
    ("G6", "言明", "折れ目の式の係数 2 を落とす",
     "theorem bb_succ_eq_add_brk : ∀ m, 1 ≤ m → ∀ s, 2 ≤ s → bb (m + 1) s = bb m s + 2 * brk m s := by",
     "theorem bb_succ_eq_add_brk : ∀ m, 1 ≤ m → ∀ s, 2 ≤ s → bb (m + 1) s = bb m s + brk m s := by",
     "fail"),
    ("G7", "言明", "上包絡の等号を 1 ずらす",
     "    (∃ m, 1 ≤ m ∧ TUP n s + bb m s = 2 * m * n) ∧",
     "    (∃ m, 1 ≤ m ∧ TUP n s + bb m s + 1 = 2 * m * n) ∧", "fail"),
    ("G8", "言明", "T_UG の θ(s) ≤ n 側の符号を逆に",
     "      (theta s ≤ n → TUG n s + bb (m + 1) s + 1 = 2 * (m + 1) * n) := by",
     "      (theta s ≤ n → TUG n s + bb (m + 1) s = 2 * (m + 1) * n + 1) := by", "fail"),
    ("G9", "言明", "被覆の左端を真の不等号にする",
     "    ∃ m, brk m s ≤ n ∧ n ≤ brk (m + 1) s := by",
     "    ∃ m, brk m s < n ∧ n ≤ brk (m + 1) s := by", "fail"),
    ("G10", "言明", "brk 3 s = B4 s（1 ずれ）",
     "theorem brk_three {s : ℕ} (hs : 2 ≤ s) : brk 3 s + 1 = B4 s := by",
     "theorem brk_three {s : ℕ} (hs : 2 ≤ s) : brk 3 s = B4 s := by", "fail"),
    ("PE1", "証明", "小さい側で頭の帰納法の仮定を使わない",
     "            have hhead := ihm (s + 1) (by omega) (brk m (s + 1)) le_rfl (by omega)",
     "            have hhead := le_refl (brk m (s + 1))", "fail"),
    ("PE2", "証明", "大きい側で尻尾の帰納法の仮定を使わない",
     "            have htail := ihs (brk (m + 1 + 1) s) hmonoT le_rfl",
     "            have htail := le_refl (brk (m + 1 + 1) s)", "fail"),
    ("PE3", "証明", "底 s=2 で閉形式 T_UP(n,2) を使わない",
     "          have hc := TUP_cap2 (n := n) (by omega)",
     "          have hc := le_refl (TUP n 2)", "fail"),
]

REFUTE = r'''/-
変異注入（`mutate_envelope.py`）で言明を書き換えた G1〜G4・G6〜G10 が**本当に偽**であることの反証。
各 `example` は変異後の言明を仮定して矛盾を出す。
このソースは `mutate_envelope.py` が出力ディレクトリ（リポジトリの外）に書き出して検査する。
-/
import SpookyPebblingExtra.Envelope
open Spooky

theorem w_TUP_1_1 : TUP 1 1 = 1 := by
  have := TUP_eq_of_le' (k := 1) (s := 1) (by omega) (by omega); omega
theorem w_TUP_1_2 : TUP 1 2 = 1 := by
  have := TUP_eq_of_le' (k := 1) (s := 2) (by omega) (by omega); omega
theorem w_TUP_3_2 : TUP 3 2 = 9 := by
  have := TUP_cap2 (n := 3) (by omega); omega
theorem w_TUG_3_2 : TUG 3 2 = 8 := by
  have := TUG_cap2 (n := 3) (by omega); omega
theorem w_bb_2_1 : bb 2 1 = 5 := by simp [bb]
theorem w_bb_2_2 : bb 2 2 = 5 := by simp [bb]
theorem w_bb_3_2 : bb 3 2 = 9 := by simp [bb]
theorem w_brk_3_2 : brk 3 2 = 3 := by simp [brk]

/-- G1: 右端を 1 広げる。反例 `m = 0`・`s = 2`・`n = 3`: `T_UP(3,2) + β_1 = 10 > 6`。 -/
example : ¬ (∀ m s, 2 ≤ s → ∀ n, brk m s ≤ n → n ≤ brk (m + 1) s + 1 →
    TUP n s + bb (m + 1) s ≤ 2 * (m + 1) * n) := by
  intro h
  have h1 := h 0 2 le_rfl 3 (by simp) (by simp)
  have hb : bb (0 + 1) 2 = 1 := bb_one 2
  have := w_TUP_3_2
  omega

/-- G2: 左端を 1 広げる。反例 `m = 1`・`s = 2`・`n = 1`: `T_UP(1,2) + β_2(2) = 6 > 4`。 -/
example : ¬ (∀ m s, 2 ≤ s → ∀ n, brk m s ≤ n + 1 → n ≤ brk (m + 1) s →
    TUP n s + bb (m + 1) s ≤ 2 * (m + 1) * n) := by
  intro h
  have h1 := h 1 2 le_rfl 1 (by simp) (by simp [brk])
  have hb : bb (1 + 1) 2 = 5 := w_bb_2_2
  have := w_TUP_1_2
  omega

/-- G3: `s` の下限を 1 に。反例 `m = 1`・`s = 1`・`n = 1`: `T_UP(1,1) + 5 = 6 > 4`。 -/
example : ¬ (∀ m s, 1 ≤ s → ∀ n, brk m s ≤ n → n ≤ brk (m + 1) s →
    TUP n s + bb (m + 1) s ≤ 2 * (m + 1) * n) := by
  intro h
  have h1 := h 1 1 le_rfl 1 (by simp) (by simp [brk])
  have hb : bb (1 + 1) 1 = 5 := w_bb_2_1
  have := w_TUP_1_1
  omega

/-- G4: 傾きを `2m` に。反例 `m = 0`: 右辺が 0 になる。 -/
example : ¬ (∀ m s, 2 ≤ s → ∀ n, brk m s ≤ n → n ≤ brk (m + 1) s →
    TUP n s + bb (m + 1) s ≤ 2 * m * n) := by
  intro h
  have h1 := h 0 2 le_rfl 1 (by simp) (by simp)
  have hb : bb (0 + 1) 2 = 1 := bb_one 2
  omega

/-- G6: 係数 2 を落とす。反例 `m = 1`・`s = 2`: `β_2(2) = 5 ≠ 1 + 2`。 -/
example : ¬ (∀ m, 1 ≤ m → ∀ s, 2 ≤ s → bb (m + 1) s = bb m s + brk m s) := by
  intro h
  have h1 := h 1 le_rfl 2 le_rfl
  have hb : bb (1 + 1) 2 = 5 := w_bb_2_2
  have h2 : bb 1 2 = 1 := bb_one 2
  have h3 : brk 1 2 = 2 := brk_one 2
  omega

/-- G7: 等号を 1 ずらす。下界（定理E'）と矛盾する。 -/
example : ¬ (∀ s n : ℕ, 2 ≤ s → 1 ≤ n →
    (∃ m, 1 ≤ m ∧ TUP n s + bb m s + 1 = 2 * m * n) ∧
      (∀ m, 1 ≤ m → 2 * m * n ≤ TUP n s + bb m s)) := by
  intro h
  obtain ⟨⟨m, hm, he⟩, _⟩ := h 2 1 le_rfl le_rfl
  have hl := TUP_ge_slope_tight m hm 2 le_rfl 1 le_rfl
  omega

/-- G8: `θ(s) ≤ n` 側の符号を逆に。反例 `m = 2`・`s = 2`・`n = 3`: `8 + 9 = 17 ≠ 19`。 -/
example : ¬ (∀ m s n : ℕ, 2 ≤ s → brk m s ≤ n → n ≤ brk (m + 1) s →
    (n + 1 ≤ theta s → TUG n s + bb (m + 1) s = 2 * (m + 1) * n + 1) ∧
      (theta s ≤ n → TUG n s + bb (m + 1) s = 2 * (m + 1) * n + 1)) := by
  intro h
  have h1 := (h 2 2 3 le_rfl (by simp [brk]) (by simp [brk])).2 (by decide)
  have hb : bb (2 + 1) 2 = 9 := w_bb_3_2
  have := w_TUG_3_2
  omega

/-- G9: 被覆の左端を真の不等号に。反例 `s = 2`・`n = 1`: `brk m 2 ≥ 1`。 -/
example : ¬ (∀ s n : ℕ, 2 ≤ s → 1 ≤ n → ∃ m, brk m s < n ∧ n ≤ brk (m + 1) s) := by
  intro h
  obtain ⟨m, h1, _⟩ := h 2 1 le_rfl le_rfl
  have := brk_pos (s := 2) le_rfl m
  omega

/-- G10: `brk 3 s = B4 s`。反例 `s = 2`: `3 ≠ 4`。 -/
example : ¬ (∀ s : ℕ, 2 ≤ s → brk 3 s = B4 s) := by
  intro h
  have h1 := h 2 le_rfl
  have h2 := w_brk_3_2
  have h3 : B4 2 = 4 := rfl
  omega
'''

REFUTE_OLD = "example : ¬ (∀ s n : ℕ, 2 ≤ s → 1 ≤ n → ∃ m, brk m s < n ∧ n ≤ brk (m + 1) s) := by"
REFUTE_NEW = "example : ¬ (∀ s n : ℕ, 2 ≤ s → 1 ≤ n → ∃ m, brk m s ≤ n ∧ n ≤ brk (m + 1) s) := by"


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
        jobs.append((mid, kind, desc, "Envelope.lean", text, expect))
    jobs.append(("RE0", "反証", "G1〜G4・G6〜G10 の言明の否定を証明する",
                 "EnvelopeMutantsAreFalse.lean", REFUTE, "pass"))
    jobs.append(("RE1", "反証", "反証ファイルの変異（G9 の代わりに真の言明の否定）",
                 "EnvelopeMutantsAreFalse.lean",
                 replace_once("RE1", REFUTE, REFUTE_OLD, REFUTE_NEW), "fail"))

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
