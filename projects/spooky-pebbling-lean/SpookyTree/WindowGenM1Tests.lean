/-
# `WindowGenM1*.lean`（一般の m・h ≡ 1）の検査: 具体値，既存の m = 3, 4 の取り直し，極限が空虚でないこと，公理

* `h = 25`（m = 4，H = 6），`p = 96`: 定理 L_{m,1} の整数の形は `T ≥ 269161783`。
  既存の定理 L4 の LB4（`265561661`）より `3600122 = 2(p + (p−1)(q + q²) + E_4)` だけ大きい（紙との違い，`WindowGenM1Lower.lean` 冒頭の注）。
* 一般の m の極限から m = 3, 4 の既存の極限（`Ttree_m3_tendsto`，`Ttree_m4_tendsto` と同じ文）が出る。
* 極限が空虚でないこと: すべての `m ≥ 3` で `p(H) = 2^H` なら `→ 2m + 1`，`p(H) = 2·2^H` なら `→ 2m`。
  m = 5，`p(H) = ⌊3·2^H/2⌋` なら `→ 10 + 1/32`（帯の中の点）。
-/
import SpookyTree.WindowGenM1UpperLimit

open Filter Topology

namespace SpookyTree

/-- `h = 25`、`p = 96`: `269161783 ≤ T(T_25, 96)`（定理 L_{m,1}，m = 4）。 -/
example : 269161783 ≤ Ttree 25 96 := by
  obtain ⟨ms, hV⟩ := (Ttree_isLeast (h := 25) (cap := 96) (by norm_num) (by norm_num)).1
  have := window_genm1_lower_exact (m := 4) (H := 6) (p := 96) (by norm_num) hV (by norm_num)
    (by norm_num)
  norm_num [Cw] at this
  omega

/-- m = 3 の既存の極限（`Ttree_m3_tendsto`）を一般の m の系として。 -/
example {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (3 * H + 1) (p H) : ℝ) / 2 ^ (3 * H + 1)) atTop
      (𝓝 (6 + (2 - c) ^ 3)) := by
  have h := Ttree_genm1_tendsto (m := 3) le_rfl hc1 hc2 hp
  norm_num at h
  exact h

/-- m = 4 の既存の極限（`Ttree_m4_tendsto`）を一般の m の系として。 -/
example {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (4 * H + 1) (p H) : ℝ) / 2 ^ (4 * H + 1)) atTop
      (𝓝 (8 + (2 - c) ^ 4)) := by
  have h := Ttree_genm1_tendsto (m := 4) (by norm_num) hc1 hc2 hp
  norm_num at h
  exact h

/-- `γ = 1`: すべての `m ≥ 3` で `T(T_{mH+1}, 2^H)/2^{mH+1} → 2m + 1`。 -/
example (m : ℕ) (hm : 3 ≤ m) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (2 ^ H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * m + 1)) := by
  have h := Ttree_genm1_tendsto (m := m) hm (p := fun H => 2 ^ H) (c := 1) le_rfl (by norm_num) (by
    have e : (fun H : ℕ => (((2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (1 : ℝ) := by
      funext H; push_cast; exact div_self (by positivity)
    rw [e]; exact tendsto_const_nhds)
  norm_num at h
  exact h

/-- `γ = 2`: すべての `m ≥ 3` で `T(T_{mH+1}, 2·2^H)/2^{mH+1} → 2m`。 -/
example (m : ℕ) (hm : 3 ≤ m) :
    Tendsto (fun H : ℕ => (Ttree (m * H + 1) (2 * 2 ^ H) : ℝ) / 2 ^ (m * H + 1)) atTop
      (𝓝 (2 * m)) := by
  have h := Ttree_genm1_tendsto (m := m) hm (p := fun H => 2 * 2 ^ H) (c := 2) (by norm_num) le_rfl
    (by
      have e : (fun H : ℕ => (((2 * 2 ^ H : ℕ) : ℝ)) / 2 ^ H) = fun _ => (2 : ℝ) := by
        funext H; push_cast; field_simp
      rw [e]; exact tendsto_const_nhds)
  have hz : (0 : ℝ) ^ m = 0 := zero_pow (by omega)
  simp only [sub_self, hz, add_zero] at h
  exact h

/-- `γ = 3/2`，m = 5: `T(T_{5H+1}, ⌊3·2^H/2⌋)/2^{5H+1} → 10 + 1/32 = 321/32`。 -/
example : Tendsto (fun H : ℕ => (Ttree (5 * H + 1) (3 * 2 ^ H / 2) : ℝ) / 2 ^ (5 * H + 1)) atTop
    (𝓝 (321 / 32)) := by
  have h := Ttree_genm1_tendsto (m := 5) (by norm_num) (p := fun H => 3 * 2 ^ H / 2) (c := 3 / 2)
    (by norm_num) (by norm_num) (by
    have e : ∀ᶠ H : ℕ in atTop, (((3 * 2 ^ H / 2 : ℕ) : ℝ)) / 2 ^ H = 3 / 2 := by
      filter_upwards [eventually_ge_atTop 1] with H hH
      obtain ⟨K, rfl⟩ : ∃ K, H = K + 1 := ⟨H - 1, by omega⟩
      have : 3 * 2 ^ (K + 1) / 2 = 3 * 2 ^ K := by rw [pow_succ]; omega
      rw [this]; push_cast; rw [pow_succ]; field_simp
    exact tendsto_const_nhds.congr' (e.mono fun H hH => hH.symm))
  norm_num at h
  exact h

#check @window_genm1_lower_exact
#check @window_genm1_lower
#check @Ttree_genm1_liminf
#check @Ttree_genm1_upper
#check @Ttree_genm1_tendsto
#check @Ttree_genm1_tendsto_rpow

#print axioms fullM_mul_le
#print axioms fullM_mul_card_le
#print axioms count_step
#print axioms zone_factF
#print axioms zoneInv_base
#print axioms zoneInv_step
#print axioms window_lower_zoneInv
#print axioms lam_sum
#print axioms lamC_closed
#print axioms psiG_g
#print axioms Cw_le
#print axioms genm1_chain
#print axioms window_genm1_lower_exact
#print axioms window_genm1_lower
#print axioms genm1_T_ge
#print axioms Ttree_genm1_eventually
#print axioms Ttree_genm1_liminf
#print axioms TtreeK_genm1_liminf
#print axioms genm1_up_low
#print axioms genm1_up_mid
#print axioms genm1_up_high
#print axioms Ttree_genm1_upper_eventually
#print axioms Ttree_genm1_tendsto
#print axioms Ttree_genm1_tendsto_rpow
#print axioms TtreeK_genm1_tendsto
#print axioms TtreeK_genm1_tendsto_rpow

end SpookyTree
