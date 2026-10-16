/-
  **橋 `codeAt h 1 C = keyCert h C / 2` を、$h$ 一般に示す**
  （第 82 夜 周 4・2026-10-12）。

  ## どの穴を埋めるか

  第 81 夜 周 5 までに残った紙の ① (c) は「橋」だった:

      `TreeAut.codeAt h 1 C`（貪欲側の部分木コード）と
      `SplitLemma.keyCert h C`（証書の鍵 = 2 × preorder ビットマスク）が一致する

  これは `night81r4_codecheck.py` が $h\le4$ の**全配置**で、`night81r3_keycert.py` が
  $h\le7$ の**全頂点の写像**で確かめただけで、Lean では何も言っていなかった。

  ## ここで示すこと / 示さないこと

  - ★ 示す（$h$ 一般）: **`hrel : Function.Injective (relabCert h)`** と
    **`C ⊆ cbtV h`** の下で `keyCert h C = 2 * codeAt h 1 C`。
    道筋は、`codeAt` を配置の各点の寄与の和 `∑ u ∈ C, cc m v u` に書き換え（線形性）、
    各寄与が「$u$ が $v$ の高さ $m$ の部分木に入るなら $2^{\mathrm{pre}(u)-\mathrm{pre}(v)}$、
    入らなければ 0」であることを帰納で示す。ここで preorder 番号の漸化式
    （`preIdx (2v) = preIdx v + 1`、`preIdx (2v+1) = preIdx v + 2^{h-1-\mathrm{dep}(v)}`）は
    燃料の安定性から出す。
  - ✗ 示さない: `hrel`（`relabCert h` の単射性）は**仮定のまま**。$h\le5$ は
    `KeyCert.lean` が `decide` で閉じ、$h=7$ は `KeyCertH7.lean` にある。
    $h$ 一般の単射性はここでは示していない。
  - 橋は最小性側（`GreedyMin.lean`）・到達可能性側（`GreedyReach.lean`）と鍵側
    （`KeyCert.lean`）をつなぐだけで、それ自体は新しい下界ではない。合成は `KeyCanon.lean`。

  ⚠ 新しい数値は 1 つも足していない。$M^*(T_7,10)=1001$ の層は 2 のままである。
-/
import KeyCert
import GreedyMin

set_option autoImplicit false

namespace SplitLemma

open Finset

/-! ## 1. 燃料の安定性 -/

theorem depF_succ_fuel : ∀ (f x : ℕ), x < 2 ^ f → depF (f + 1) x = depF f x := by
  intro f
  induction f with
  | zero =>
    intro x hx
    have : x = 0 := by simpa using hx
    subst this
    simp [depF]
  | succ f ih =>
    intro x hx
    by_cases h1 : x ≤ 1
    · simp [depF, h1]
    · have h2 : x / 2 < 2 ^ f := by rw [pow_succ] at hx; omega
      show (if x ≤ 1 then 0 else depF (f + 1) (x / 2) + 1)
        = (if x ≤ 1 then 0 else depF f (x / 2) + 1)
      rw [if_neg h1, if_neg h1, ih _ h2]

theorem preF_succ_fuel (h : ℕ) : ∀ (f x : ℕ), x < 2 ^ f → preF h (f + 1) x = preF h f x := by
  intro f
  induction f with
  | zero =>
    intro x hx
    have : x = 0 := by simpa using hx
    subst this
    simp [preF]
  | succ f ih =>
    intro x hx
    by_cases h1 : x ≤ 1
    · simp [preF, h1]
    · have h2 : x / 2 < 2 ^ f := by rw [pow_succ] at hx; omega
      show (if x ≤ 1 then 0 else preF h (f + 1) (x / 2)
            + (if x % 2 = 0 then 1 else 2 ^ (h - 1 - depF (f + 1) (x / 2))))
        = (if x ≤ 1 then 0 else preF h f (x / 2)
            + (if x % 2 = 0 then 1 else 2 ^ (h - 1 - depF f (x / 2))))
      rw [if_neg h1, if_neg h1, ih _ h2, depF_succ_fuel f _ h2]

/-- `depF` は深さ $d$ の節点に対し、燃料が $d$ 以上なら $d$ を返す。 -/
theorem depF_eq : ∀ (d f v : ℕ), 2 ^ d ≤ v → v < 2 ^ (d + 1) → d ≤ f → depF f v = d := by
  intro d
  induction d with
  | zero =>
    intro f v h1 h2 _
    simp only [zero_add, pow_zero, pow_one] at h1 h2
    have : v = 1 := by omega
    subst this
    cases f <;> simp [depF]
  | succ d ih =>
    intro f v h1 h2 h3
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := by
      cases f with
      | zero => omega
      | succ f' => exact ⟨f', rfl⟩
    have e1 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have e2 : 2 ^ (d + 1 + 1) = 4 * 2 ^ d := by ring
    have e0 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hv : ¬ v ≤ 1 := by omega
    simp only [depF, hv, if_false]
    rw [ih f' (v / 2) (by omega) (by omega) (by omega)]

theorem lt_of_pow_le {d f v : ℕ} (hd : 2 ^ d ≤ v) (hv : v < 2 ^ f) : d < f := by
  by_contra hc
  push Not at hc
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hc
  omega

/-! ## 2. preorder 番号の漸化式 -/

theorem preIdx_left (h v : ℕ) (hv : 1 ≤ v) (hlt : 2 * v < 2 ^ h) :
    preIdx h (2 * v) = preIdx h v + 1 := by
  obtain ⟨f, rfl⟩ : ∃ f, h = f + 1 := by
    cases h with
    | zero => simp at hlt; omega
    | succ f => exact ⟨f, rfl⟩
  have hv' : v < 2 ^ f := by rw [pow_succ] at hlt; omega
  have e1 : preIdx (f + 1) (2 * v) = preF (f + 1) f v + 1 := by
    have h1 : ¬ (2 * v ≤ 1) := by omega
    have h2 : 2 * v / 2 = v := by omega
    have h3 : 2 * v % 2 = 0 := by omega
    simp [preIdx, preF, h1, h2, h3]
  have e2 : preIdx (f + 1) v = preF (f + 1) f v := by
    simp only [preIdx]
    exact preF_succ_fuel _ f v hv'
  rw [e1, e2]

theorem preIdx_right (h d v : ℕ) (hd : 2 ^ d ≤ v) (hv2 : v < 2 ^ (d + 1))
    (hlt : 2 * v + 1 < 2 ^ h) :
    preIdx h (2 * v + 1) = preIdx h v + 2 ^ (h - 1 - d) := by
  obtain ⟨f, rfl⟩ : ∃ f, h = f + 1 := by
    cases h with
    | zero => simp at hlt
    | succ f => exact ⟨f, rfl⟩
  have hv' : v < 2 ^ f := by rw [pow_succ] at hlt; omega
  have hdf : d ≤ f := (lt_of_pow_le hd hv').le
  have hdep : depF f v = d := depF_eq d f v hd hv2 hdf
  have e1 : preIdx (f + 1) (2 * v + 1) = preF (f + 1) f v + 2 ^ (f + 1 - 1 - d) := by
    have h1 : ¬ (2 * v + 1 ≤ 1) := by omega
    have h2 : (2 * v + 1) / 2 = v := by omega
    have h3 : ¬ ((2 * v + 1) % 2 = 0) := by omega
    simp only [preIdx, preF, h1, h2, h3, if_false, hdep]
  have e2 : preIdx (f + 1) v = preF (f + 1) f v := by
    simp only [preIdx]
    exact preF_succ_fuel _ f v hv'
  rw [e1, e2]

theorem preIdx_one (h : ℕ) : preIdx h 1 = 0 := by
  cases h <;> simp [preIdx, preF]

/-! ## 3. 部分木への所属と、各点の寄与 `cc` -/

/-- `u` が、根 `v` の高さ `m` の部分木に入る（`u` の $k$ 世代前の祖先が `v`、$k<m$）。 -/
def Sub (m v u : ℕ) : Prop := ∃ k, k < m ∧ u / 2 ^ k = v

theorem Sub_pos {m v u : ℕ} (h : Sub m v u) : 0 < m := by
  obtain ⟨k, hk, _⟩ := h
  omega

theorem Sub_le {m v u : ℕ} (h : Sub m v u) : v ≤ u := by
  obtain ⟨k, _, hk⟩ := h
  rw [← hk]
  exact Nat.div_le_self _ _

theorem Sub_succ_iff (m v u : ℕ) :
    Sub (m + 1) v u ↔ u = v ∨ Sub m (2 * v) u ∨ Sub m (2 * v + 1) u := by
  constructor
  · rintro ⟨k, hk, hkv⟩
    cases k with
    | zero => left; simpa using hkv
    | succ k =>
      right
      have e : u / 2 ^ (k + 1) = u / 2 ^ k / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      rw [e] at hkv
      have : u / 2 ^ k = 2 * v ∨ u / 2 ^ k = 2 * v + 1 := by omega
      rcases this with h1 | h1
      · left; exact ⟨k, by omega, h1⟩
      · right; exact ⟨k, by omega, h1⟩
  · rintro (h1 | ⟨k, hk, hkv⟩ | ⟨k, hk, hkv⟩)
    · exact ⟨0, by omega, by simpa using h1⟩
    · refine ⟨k + 1, by omega, ?_⟩
      rw [pow_succ, ← Nat.div_div_eq_div_mul, hkv]
      omega
    · refine ⟨k + 1, by omega, ?_⟩
      rw [pow_succ, ← Nat.div_div_eq_div_mul, hkv]
      omega

theorem div_pow_le_half (u k j : ℕ) : u / 2 ^ (k + j + 1) ≤ u / 2 ^ k / 2 := by
  have e : 2 ^ (k + j + 1) = 2 ^ k * 2 * 2 ^ j := by ring
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  exact Nat.div_le_self _ _

theorem Sub_excl {m v u : ℕ} (hv : 1 ≤ v) :
    ¬ (Sub m (2 * v) u ∧ Sub m (2 * v + 1) u) := by
  rintro ⟨⟨k, hk, h1⟩, ⟨k', hk', h2⟩⟩
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · obtain ⟨j, rfl⟩ : ∃ j, k' = k + j + 1 := ⟨k' - k - 1, by omega⟩
    have := div_pow_le_half u k j
    rw [h2, h1] at this
    omega
  · subst heq
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, k = k' + j + 1 := ⟨k - k' - 1, by omega⟩
    have := div_pow_le_half u k' j
    rw [h1, h2] at this
    omega

/-- 各点 `u` が `codeAt m v` に寄与する値。 -/
def cc : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | m + 1, v, u =>
      (if u = v then 1 else 0) + 2 * cc m (2 * v) u + 2 ^ 2 ^ m * cc m (2 * v + 1) u

/-- ★ `codeAt` は各点の寄与の和（線形性）。 -/
theorem codeAt_eq_sum (C : Finset ℕ) :
    ∀ (m v : ℕ), TreeAut.codeAt m v C = ∑ u ∈ C, cc m v u := by
  intro m
  induction m with
  | zero => intro v; simp [TreeAut.codeAt, cc]
  | succ m ih =>
    intro v
    rw [TreeAut.codeAt_succ, ih, ih]
    have hind : (if v ∈ C then 1 else 0) = ∑ u ∈ C, (if u = v then 1 else 0) := by
      rw [Finset.sum_ite_eq']
    simp only [cc]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hind]

/-! ## 4. 主補題: 寄与は preorder 番号の差だけ左にずれた 1 ビット -/

theorem child_lt (d m v h : ℕ) (hh : h = d + m + 1) (hm : 1 ≤ m) (hv : v < 2 ^ (d + 1)) :
    2 * v + 1 < 2 ^ h := by
  have h1 : 2 ^ (d + 2) ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ (d + 2) = 2 * 2 ^ (d + 1) := by ring
  omega

theorem cc_main (h : ℕ) : ∀ (m d : ℕ), h = d + m → ∀ v : ℕ, 2 ^ d ≤ v → v < 2 ^ (d + 1) →
    ∀ u : ℕ, 1 ≤ u → u < 2 ^ h →
      (Sub m v u → 2 ^ preIdx h v * cc m v u = 2 ^ preIdx h u) ∧ (¬ Sub m v u → cc m v u = 0) := by
  intro m
  induction m with
  | zero =>
    intro d hd v _ _ u _ _
    refine ⟨fun hs => absurd (Sub_pos hs) (by omega), fun _ => by simp [cc]⟩
  | succ m ih =>
    intro d hd v hv1 hv2 u hu1 hu2
    have e1 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have e2 : 2 ^ (d + 1 + 1) = 4 * 2 ^ d := by ring
    have e0 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hvpos : 1 ≤ v := by omega
    have ihL := ih (d + 1) (by omega) (2 * v) (by omega) (by omega) u hu1 hu2
    have ihR := ih (d + 1) (by omega) (2 * v + 1) (by omega) (by omega) u hu1 hu2
    have hiff := Sub_succ_iff m v u
    have hex := @Sub_excl m v u hvpos
    by_cases hA : u = v
    · -- 根そのもの
      subst hA
      have nL : ¬ Sub m (2 * u) u := fun hs => by have := Sub_le hs; omega
      have nR : ¬ Sub m (2 * u + 1) u := fun hs => by have := Sub_le hs; omega
      have hcc : cc (m + 1) u u = 1 := by
        simp only [cc]
        rw [ihL.2 nL, ihR.2 nR]
        simp
      rw [hcc]
      refine ⟨fun _ => by simp, fun hn => absurd (hiff.mpr (Or.inl rfl)) hn⟩
    · by_cases hB : Sub m (2 * v) u
      · have nR : ¬ Sub m (2 * v + 1) u := fun hs => hex ⟨hB, hs⟩
        have hm : 1 ≤ m := Sub_pos hB
        have hlt : 2 * v < 2 ^ h := by
          have := child_lt d m v h (by omega) hm hv2
          omega
        have hpre := preIdx_left h v hvpos hlt
        have := (ihL.1 hB)
        rw [hpre] at this
        refine ⟨fun _ => ?_, fun hn => absurd (hiff.mpr (Or.inr (Or.inl hB))) hn⟩
        simp only [cc, if_neg hA, ihR.2 nR, mul_zero, add_zero, zero_add]
        calc 2 ^ preIdx h v * (2 * cc m (2 * v) u)
            = 2 ^ (preIdx h v + 1) * cc m (2 * v) u := by ring
          _ = 2 ^ preIdx h u := this
      · by_cases hC : Sub m (2 * v + 1) u
        · have hm : 1 ≤ m := Sub_pos hC
          have hlt : 2 * v + 1 < 2 ^ h := child_lt d m v h (by omega) hm hv2
          have hpre := preIdx_right h d v hv1 hv2 hlt
          have hexp : h - 1 - d = m := by omega
          rw [hexp] at hpre
          have := (ihR.1 hC)
          rw [hpre] at this
          refine ⟨fun _ => ?_, fun hn => absurd (hiff.mpr (Or.inr (Or.inr hC))) hn⟩
          simp only [cc, if_neg hA, ihL.2 hB, mul_zero, add_zero, zero_add]
          calc 2 ^ preIdx h v * (2 ^ 2 ^ m * cc m (2 * v + 1) u)
              = 2 ^ (preIdx h v + 2 ^ m) * cc m (2 * v + 1) u := by ring
            _ = 2 ^ preIdx h u := this
        · refine ⟨fun hs => ?_, fun _ => ?_⟩
          · rcases hiff.mp hs with h1 | h1 | h1
            · exact absurd h1 hA
            · exact absurd h1 hB
            · exact absurd h1 hC
          · simp [cc, if_neg hA, ihL.2 hB, ihR.2 hC]

/-! ## 5. 根の場合と橋 -/

theorem exists_anc (u : ℕ) (hu : 1 ≤ u) : ∃ k, 2 ^ k ≤ u ∧ u / 2 ^ k = 1 := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    rcases Nat.lt_or_ge u 2 with hlt | hge
    · exact ⟨0, by omega, by omega⟩
    · obtain ⟨k, hk1, hk2⟩ := ih (u / 2) (by omega) (by omega)
      refine ⟨k + 1, ?_, ?_⟩
      · rw [pow_succ]; omega
      · rw [pow_succ', ← Nat.div_div_eq_div_mul]
        exact hk2

/-- 根 `1` の高さ `h` の部分木は $[1,2^h)$ 全体。 -/
theorem Sub_root (h u : ℕ) (hu1 : 1 ≤ u) (hu2 : u < 2 ^ h) : Sub h 1 u := by
  obtain ⟨k, hk1, hk2⟩ := exists_anc u hu1
  refine ⟨k, ?_, hk2⟩
  by_contra hc
  push Not at hc
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hc
  omega

/-- ★ `codeAt h 1 C` は preorder ビットマスクそのもの。 -/
theorem codeAt_root_eq_sum (h : ℕ) (C : Finset ℕ) (hC : C ⊆ HullLemmaCBT.cbtV h) :
    TreeAut.codeAt h 1 C = ∑ u ∈ C, 2 ^ preIdx h u := by
  rw [codeAt_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro u hu
  have hu' := hC hu
  simp only [HullLemmaCBT.cbtV, Finset.mem_Icc] at hu'
  have hpos : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hu2 : u < 2 ^ h := by omega
  have := (cc_main h h 0 (by omega) 1 (by norm_num) (by norm_num) u hu'.1 hu2).1
    (Sub_root h u hu'.1 hu2)
  rw [preIdx_one, pow_zero, one_mul] at this
  exact this

/-- ★★ **橋**: 証書の鍵は `codeAt h 1` の 2 倍。仮定は `relabCert h` の単射性と `C ⊆ cbtV h`。 -/
theorem keyCert_eq_two_codeAt (h : ℕ) (C : Finset ℕ)
    (hrel : Function.Injective (relabCert h))
    (hC : C ⊆ HullLemmaCBT.cbtV h) :
    keyCert h C = 2 * TreeAut.codeAt h 1 C := by
  rw [codeAt_root_eq_sum h C hC, keyCert, bitkey, Finset.sum_image (fun a _ b _ hab => hrel hab),
    Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro u hu
  have hu' := hC hu
  simp only [HullLemmaCBT.cbtV, Finset.mem_Icc] at hu'
  have hpos : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hrl : relabCert h u = preIdx h u + 1 := by
    simp only [relabCert, relabOf]
    rw [if_pos ⟨by omega, by omega⟩]
  rw [hrl, pow_succ]
  ring

/-- 系: 係数 2 を外した形（`codeAt h 1 C` は `keyCert h C` の半分）。 -/
theorem codeAt_eq_half_keyCert (h : ℕ) (C : Finset ℕ)
    (hrel : Function.Injective (relabCert h))
    (hC : C ⊆ HullLemmaCBT.cbtV h) :
    TreeAut.codeAt h 1 C = keyCert h C / 2 := by
  rw [keyCert_eq_two_codeAt h C hrel hC]
  omega

#print axioms keyCert_eq_two_codeAt
#print axioms codeAt_eq_half_keyCert

end SplitLemma
