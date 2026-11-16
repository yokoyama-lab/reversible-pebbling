/-
# 窓の極限（m = 2，h が奇数の列）: 上界側と極限

紙は `notes/spooky-pebbling/tree-gap/WINDOW_UB_ODD_2026-11.md` の 6 節（系（極限）の 1/√2 ≤ c ≤ √2 の帯）。
`h = 2H + 1`，`X = 2^H`，`p(H)/2^H → c' ∈ [1, 2]`（紙の `γ = c√2`）。

* 上界（`Ttree_odd_upper_eventually`）: すべての `δ > 0` で十分大きい `H` について
  `T(T_h, p(H)) ≤ (4 + (2 − c')² + δ)·2^h`。`p` の位置で 3 つに分ける（紙 6 節の γ = 1, (1,2), 2 の扱い）:
  - `X < p ≤ 2X`: 定理 B-odd（`Ttree_window_odd_upper`）。
  - `2X < p`: 上限 `2X` の手順をそのまま使う（単調性）。
  - `p ≤ X`（`c' = 1` の近くだけで起こる）: `q = min(p, X − 1)` に定理 B（m = 2，`window_upper_bound_m2`）と単調性。
* 極限（`Ttree_odd_tendsto`）: 下界は付記 A の `Ttree_odd_eventually`（`WindowOddLowerLimit.lean`）。
  `T(T_h, p(H))/2^h → 4 + (2 − c')²`。紙の形 `p(H)/2^{h/2} → c ∈ [1/√2, √2]` なら `→ 4 + (2 − c√2)²`
  （`Ttree_odd_tendsto_sqrt`）。
-/
import SpookyTree.WindowUpperOddBound
import SpookyTree.WindowUpperLimit
import SpookyTree.WindowOddLowerLimit

open Filter Topology

namespace SpookyTree

/-- 定理 B（m = 2）を `h = 2H + 1` で（(B2) は 3 乗の形 `B2_of_cube` から）。 -/
theorem oddB_valid {H q : ℕ} (hq13 : 2 * H + 14 ≤ q) (hqX : q ≤ 2 ^ H - 1)
    (hcube : 2 ^ (2 * H + 5) ≤ (q - (2 * H + 6)) * (q * (q - 1))) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid (2 * H + 1) q T ms ∧
      T + 2 * (q - (2 * H + 6)) ^ 2 + 1 ≤ 6 * (2 ^ (2 * H + 1) - 1) := by
  have hh : (2 * H + 1) / 2 = H := by omega
  have hf : q - (2 * H + 1) - 5 = q - (2 * H + 6) := by omega
  have hX1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  have hXH : 2 ^ H ≤ 2 ^ (2 * H + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB2 := B2_of_cube (h := 2 * H + 1) (q := q) (by omega) (by omega)
    (by rw [hf, show 2 * H + 1 + 4 = 2 * H + 5 by omega]; exact hcube)
  obtain ⟨T, ms, hV, hT⟩ := window_upper_bound_m2 (h := 2 * H + 1) (p := q) (by omega)
    (by rw [hh]; exact hqX) hB2
  rw [hf] at hT
  exact ⟨T, ms, hV, by simpa using hT⟩

/-- `x, c ∈ [1, 2]`，`|x − c| ≤ η` なら `(2 − x)² ≤ (2 − c)² + 2η`。 -/
theorem sq_sub_le_odd {x c η : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (h : |x - c| ≤ η) : (2 - x) ^ 2 ≤ (2 - c) ^ 2 + 2 * η := by
  have hxc := abs_le.mp h
  rcases le_total x c with h' | h'
  · nlinarith [mul_nonneg (sub_nonneg.2 h') (by linarith : (0 : ℝ) ≤ x + c - 2)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h') (by linarith : (0 : ℝ) ≤ 4 - x - c)]

/-- 上界の場合 1（`p ≤ X`）: `q = min(p, X − 1)` に定理 B（m = 2）と単調性。 -/
theorem odd_up_low {H pp : ℕ} {c η δ : ℝ} (hc1 : 1 ≤ c) (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    (hη2 : η ≤ δ / 8) (hx : |(pp : ℝ) / 2 ^ H - c| ≤ η) (hX : (1024 : ℝ) ≤ 2 ^ H)
    (hl1 : 2 * (H : ℝ) + 14 ≤ η * 2 ^ H) (hp1 : pp ≤ 2 ^ H) :
    (Ttree (2 * H + 1) pp : ℝ) ≤ (4 + (2 - c) ^ 2 + δ) * (2 * 2 ^ H * 2 ^ H) := by
  have h2h : (2 : ℝ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by rw [pow_succ, pow_mul']; ring
  have hXn : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hX1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hX hl1 hx h2h hXn ⊢
  have hXpos : (0 : ℝ) < X := by linarith
  have hXX : (0 : ℝ) ≤ X * X := by positivity
  have hpX : (pp : ℝ) ≤ X := by
    have := (Nat.cast_le (α := ℝ)).mpr hp1; rwa [hXn] at this
  have hxc := abs_le.mp hx
  have hx1 : (pp : ℝ) / X ≤ 1 := by rw [div_le_one hXpos]; exact hpX
  have hc' : c ≤ 1 + η := by linarith
  have hpp : (pp : ℝ) / X * X = pp := div_mul_cancel₀ _ hXpos.ne'
  have hηX : η * X ≤ 1 / 4 * X := mul_le_mul_of_nonneg_right hη1 hXpos.le
  have hηX0 : 0 ≤ η * X := mul_nonneg hη0.le hXpos.le
  obtain ⟨q, hqdef⟩ : ∃ q, q = min pp (2 ^ H - 1) := ⟨_, rfl⟩
  have hqp : q ≤ pp := by rw [hqdef]; exact min_le_left _ _
  have hqX : q ≤ 2 ^ H - 1 := by rw [hqdef]; exact min_le_right _ _
  have hqge : (1 - η) * X - 1 ≤ (q : ℝ) := by
    rcases le_total pp (2 ^ H - 1) with h | h
    · rw [hqdef, min_eq_left h]
      have a1 : (c - η) * X ≤ (pp : ℝ) / X * X := mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      have a2 : (1 - η) * X ≤ (c - η) * X := mul_le_mul_of_nonneg_right (by linarith) hXpos.le
      linarith
    · rw [hqdef, min_eq_right h, Nat.cast_sub hX1, hXn]
      push_cast
      linarith
  have hq13r : ((2 * H + 14 : ℕ) : ℝ) ≤ (q : ℝ) := by push_cast; linarith
  have hq13 : 2 * H + 14 ≤ q := Nat.cast_le.mp hq13r
  have hfz : ((q - (2 * H + 6) : ℕ) : ℝ) = (q : ℝ) - (2 * H + 6) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hq1z : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hfge : (1 - 2 * η) * X ≤ (q : ℝ) - (2 * H + 6) := by linarith
  have hA : X / 2 ≤ (q : ℝ) - (2 * H + 6) := by linarith
  have hB : X / 2 ≤ (q : ℝ) := by linarith
  have hC : X / 4 ≤ (q : ℝ) - 1 := by linarith
  have hprod : (X / 2) * ((X / 2) * (X / 4)) ≤ ((q : ℝ) - (2 * H + 6)) * ((q : ℝ) * ((q : ℝ) - 1)) :=
    mul_le_mul hA (mul_le_mul hB hC (by positivity) (by positivity)) (by positivity) (by linarith)
  have hXXX : 1024 * (X * X) ≤ X * (X * X) := mul_le_mul_of_nonneg_right hX hXX
  have h32 : ((2 ^ (2 * H + 5) : ℕ) : ℝ) = 32 * (X * X) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, show 2 * H + 5 = H + H + 5 by ring, pow_add, pow_add, ← hXd]
    ring
  have hcube : 2 ^ (2 * H + 5) ≤ (q - (2 * H + 6)) * (q * (q - 1)) := by
    have key : ((2 ^ (2 * H + 5) : ℕ) : ℝ) ≤ (((q - (2 * H + 6)) * (q * (q - 1)) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_mul, hfz, hq1z, h32]
      linarith
    exact Nat.cast_le.mp key
  obtain ⟨T, ms, hV, hT⟩ := oddB_valid hq13 hqX hcube
  have hTt : Ttree (2 * H + 1) pp ≤ T := Ttree_le_of_valid (hV.mono_cap hqp)
  have hTtr : (Ttree (2 * H + 1) pp : ℝ) ≤ T := by exact_mod_cast hTt
  have h1 : 1 ≤ 2 ^ (2 * H + 1) := Nat.one_le_two_pow
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast [Nat.cast_sub h1] at hTr
  rw [hfz, h2h] at hTr
  have h0 : (0 : ℝ) ≤ (1 - 2 * η) * X := by
    have : (0 : ℝ) ≤ 1 - 2 * η := by linarith
    positivity
  have hsq := mul_le_mul hfge hfge h0 (by linarith)
  have hc2' : (1 - η) ^ 2 ≤ (2 - c) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have b1 := mul_le_mul_of_nonneg_right hc2' hXX
  have b2 := mul_le_mul_of_nonneg_right hη2 hXX
  have b3 := mul_nonneg hη0.le hXX
  have b4 := mul_nonneg (sq_nonneg η) hXX
  linarith

/-- 上界の場合 2（`X < p ≤ 2X`）: 定理 B-odd。 -/
theorem odd_up_mid {H pp : ℕ} {c η δ : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hδ : 0 < δ)
    (hη2 : η ≤ δ / 8) (hx : |(pp : ℝ) / 2 ^ H - c| ≤ η) (hX : (1024 : ℝ) ≤ 2 ^ H)
    (hl2 : 2 * (H : ℝ) + 14 ≤ δ / 6 * 2 ^ H) (hH5 : 5 ≤ H) (hp1 : 2 ^ H < pp)
    (hp2 : pp ≤ 2 ^ (H + 1)) :
    (Ttree (2 * H + 1) pp : ℝ) ≤ (4 + (2 - c) ^ 2 + δ) * (2 * 2 ^ H * 2 ^ H) := by
  have hT := Ttree_window_odd_upper hH5 hp1 hp2
  have hsub : pp ≤ 2 * 2 ^ H := by rw [two_pow_succ_odd] at hp2; exact hp2
  have h2h : (2 : ℝ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by rw [pow_succ, pow_mul']; ring
  have hXn : ((2 ^ H : ℕ) : ℝ) = (2 : ℝ) ^ H := by push_cast; ring
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast [Nat.cast_sub hsub] at hTr
  have hpX := (Nat.cast_lt (α := ℝ)).mpr hp1
  have hp2r := (Nat.cast_le (α := ℝ)).mpr hsub
  push_cast at hpX hp2r
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hX hl2 hx h2h hTr hpX hp2r ⊢
  rw [h2h] at hTr
  have hXpos : (0 : ℝ) < X := by linarith
  have hXX : (0 : ℝ) ≤ X * X := by positivity
  have hx1 : 1 ≤ (pp : ℝ) / X := by rw [le_div_iff₀ hXpos]; linarith
  have hx2 : (pp : ℝ) / X ≤ 2 := by rw [div_le_iff₀ hXpos]; linarith
  have key := sq_sub_le_odd hx1 hx2 hc1 hc2 hx
  have hpx : (pp : ℝ) = (pp : ℝ) / X * X := (div_mul_cancel₀ _ hXpos.ne').symm
  have e1 : 2 * (2 * X - (pp : ℝ)) ^ 2 = 2 * (X * X) * (2 - (pp : ℝ) / X) ^ 2 := by
    conv_lhs => rw [hpx]
    ring
  have e2 := mul_le_mul_of_nonneg_left key (show (0 : ℝ) ≤ 2 * (X * X) by positivity)
  have e3 : (3 * (2 * (H : ℝ) + 1) + 3) * pp ≤ (3 * (2 * H + 1) + 3) * (2 * X) :=
    mul_le_mul_of_nonneg_left hp2r (by positivity)
  have e4 := mul_le_mul_of_nonneg_right hl2 hXpos.le
  have b2 := mul_le_mul_of_nonneg_right hη2 hXX
  have b3 := mul_nonneg hδ.le hXX
  linarith

/-- 上界の場合 3（`2X < p`）: 上限 `2X` の手順（単調性）。 -/
theorem odd_up_high {H pp : ℕ} {c δ : ℝ} (hδ : 0 < δ) (hX : (1024 : ℝ) ≤ 2 ^ H)
    (hl2 : 2 * (H : ℝ) + 14 ≤ δ / 6 * 2 ^ H) (hH5 : 5 ≤ H) (hp2 : 2 ^ (H + 1) < pp) :
    (Ttree (2 * H + 1) pp : ℝ) ≤ (4 + (2 - c) ^ 2 + δ) * (2 * 2 ^ H * 2 ^ H) := by
  have hX1 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
  obtain ⟨T, ms, hV, hT⟩ := window_odd_upper_bound (H := H) (p := 2 ^ (H + 1)) hH5
    (by rw [two_pow_succ_odd]; omega) le_rfl
  have hTt : Ttree (2 * H + 1) pp ≤ T := Ttree_le_of_valid (hV.mono_cap hp2.le)
  rw [two_pow_succ_odd H, Nat.sub_self] at hT
  have h2h : (2 : ℝ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by rw [pow_succ, pow_mul']; ring
  have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hTr := (Nat.cast_le (α := ℝ)).mpr hT
  push_cast at hTr
  have hTtr : (Ttree (2 * H + 1) pp : ℝ) ≤ T := by exact_mod_cast hTt
  obtain ⟨X, hXd⟩ : ∃ X : ℝ, X = 2 ^ H := ⟨_, rfl⟩
  rw [← hXd] at hX hl2 h2h hTr ⊢
  rw [h2h] at hTr
  have hXpos : (0 : ℝ) < X := by linarith
  have hXX : (0 : ℝ) ≤ X * X := by positivity
  have e4 := mul_le_mul_of_nonneg_right hl2 hXpos.le
  have b1 := mul_nonneg (sq_nonneg (2 - c)) hXX
  have b3 := mul_nonneg hδ.le hXX
  linarith

/-- **上界（δ の形）.** `p(H)/2^H → c ∈ [1, 2]` なら，すべての `δ > 0` について十分大きい `H` で
`T(T_{2H+1}, p(H)) ≤ (4 + (2 − c)² + δ)·2^{2H+1}`。 -/
theorem Ttree_odd_upper_eventually {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    ∀ δ > 0, ∀ᶠ H in atTop,
      (Ttree (2 * H + 1) (p H) : ℝ) ≤ (4 + (2 - c) ^ 2 + δ) * 2 ^ (2 * H + 1) := by
  intro δ hδ
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ η ≤ δ / 8 :=
    ⟨min (1 / 4) (δ / 8), lt_min (by norm_num) (by positivity), min_le_left _ _, min_le_right _ _⟩
  have hclose : ∀ᶠ H in atTop, |(p H : ℝ) / 2 ^ H - c| ≤ η := by
    filter_upwards [hp.eventually (Metric.closedBall_mem_nhds c hη0)] with H hH
    rwa [Real.dist_eq] at hH
  have hbig : ∀ᶠ H : ℕ in atTop, (1024 : ℝ) ≤ 2 ^ H :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_ge_atTop _
  filter_upwards [hclose, hbig, ev_lin hη0, ev_lin (show (0 : ℝ) < δ / 6 by positivity),
    eventually_ge_atTop 5] with H hx hX hl1 hl2 hH5
  have h2h : (2 : ℝ) ^ (2 * H + 1) = 2 * 2 ^ H * 2 ^ H := by rw [pow_succ, pow_mul']; ring
  rw [h2h]
  rcases le_or_gt (p H) (2 ^ H) with hp1 | hp1
  · exact odd_up_low hc1 hη0 hη1 hη2 hx hX (by linarith) hp1
  · rcases le_or_gt (p H) (2 ^ (H + 1)) with hp2 | hp2
    · exact odd_up_mid hc1 hc2 hδ hη2 hx hX (by linarith) hH5 hp1 hp2
    · exact odd_up_high hδ hX (by linarith) hH5 hp2

/-- **奇数 h の窓の極限（`c' = p/2^H` の形）.** `p(H)/2^H → c ∈ [1, 2]` なら
`T(T_{2H+1}, p(H))/2^{2H+1} → 4 + (2 − c)²`。下界は付記 A（`Ttree_odd_eventually`），上界は定理 B-odd ほか。 -/
theorem Ttree_odd_tendsto {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1)) atTop
      (𝓝 (4 + (2 - c) ^ 2)) :=
  tendsto_of_delta_bounds (4 + (2 - c) ^ 2) (fun H => (Ttree (2 * H + 1) (p H) : ℝ))
    (fun H => (2 : ℝ) ^ (2 * H + 1)) (Eventually.of_forall (fun H => by positivity))
    (Ttree_odd_eventually hc1 hc2 hp) (Ttree_odd_upper_eventually hc1 hc2 hp)

/-- **奇数 h の窓の極限（紙の形）.** `h = 2H + 1` で `p(H)/2^{h/2} → c ∈ [1/√2, √2]` なら
`T(T_h, p(H))/2^h → 4 + (2 − c√2)²`。 -/
theorem Ttree_odd_tendsto_sqrt {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 / √2 ≤ c) (hc2 : c ≤ √2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (Ttree (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1)) atTop
      (𝓝 (4 + (2 - c * √2) ^ 2)) := by
  have hs : (0 : ℝ) < √2 := by positivity
  have hrp : ∀ H : ℕ, (2 : ℝ) ^ (((2 * H + 1 : ℕ) : ℝ) / 2) = 2 ^ H * √2 := by
    intro H
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  apply Ttree_odd_tendsto
  · calc (1 : ℝ) = 1 / √2 * √2 := by field_simp
      _ ≤ c * √2 := mul_le_mul_of_nonneg_right hc1 hs.le
  · nlinarith [mul_le_mul_of_nonneg_right hc2 hs.le, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · have e : (fun H : ℕ => (p H : ℝ) / 2 ^ H) =
        fun H => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2) * √2 := by
      funext H
      rw [hrp]
      field_simp
    rw [e]
    exact hp.mul_const _

/-! ## KSS の意味論で -/

theorem TtreeK_odd_tendsto {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2)
    (hp : Tendsto (fun H => (p H : ℝ) / 2 ^ H) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (TtreeK (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1)) atTop
      (𝓝 (4 + (2 - c) ^ 2)) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_odd_tendsto hc1 hc2 hp

theorem TtreeK_odd_tendsto_sqrt {p : ℕ → ℕ} {c : ℝ} (hc1 : 1 / √2 ≤ c) (hc2 : c ≤ √2)
    (hp : Tendsto (fun H : ℕ => (p H : ℝ) / 2 ^ (((2 * H + 1 : ℕ) : ℝ) / 2)) atTop (𝓝 c)) :
    Tendsto (fun H : ℕ => (TtreeK (2 * H + 1) (p H) : ℝ) / 2 ^ (2 * H + 1)) atTop
      (𝓝 (4 + (2 - c * √2) ^ 2)) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_odd_tendsto_sqrt hc1 hc2 hp

end SpookyTree
