/-
# 完全二分木の再帰 `F` の指数は 1.33 以上

論文（WiNF 2026）§6 (3) の「F の指数は 1.33 以上」を機械証明する。
鎖の Knill 再帰 `Fc` に直接の下解
  `Fc n S ≥ n^{5/3} · μ^{−S}`（μ = 631/500）
を当てる（`Fc_lower`）。帰納法の 1 歩は 2 点の Jensen の不等式
  `(x + y)^{5/3} ≤ (1+μ) x^{5/3} + μ y^{5/3}`（`jensen_split`）
で、これが成り立つ条件 `(1+μ)^{−3/2} + μ^{−3/2} ≤ 1` は鎖の ρ_c(q)（q = 3/2）の条件と同じである。
指数は 5/3 − log₂ μ ≈ 1.3310（q = 3/2 での 1 + 1/q − log₂ ρ_c(q) は 1.33173）。

  * `Fc_lower`: すべての `n, S` で `n^{5/3} ≤ Fc n S · μ^S`（`Fc n S` が有限のとき）
  * `cbt_F_lower`: 完全二分木で `(2^h − 1)^{5/3} ≤ F(T_h, S) · μ^S`
  * `cbt_F_exponent`: 十分大きい `h` と `S ≤ h + ⌈log₂ h⌉` で `(2^h − 1)^{1.33} ≤ F(T_h, S)`
  * `cbt_F_Rb_exponent`: 上を `S = R•(T_h)`（最小ペブル数）に当てたもの
  * `cbt_F_Rbullet_two_sided`: `F(T_h, R•(T_h))` は有限で `(2^h − 1)^{1.33} ≤ F ≤ 3^{R• − 1}`（空虚でない形）

ここで得るのは再帰 `F` の下界であって、最短手数 `M` の下界ではない（`M ≤ F` の向きしか無い）。
最小ペブル数 R•(T_h) の値は使わない。`R•(T_h) ≤ h + ⌈log₂ h⌉`（`cbt_Rb_le`）だけを使う。
-/
import TreePebbling.Chain
import TreePebbling.Exists
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace P5Tree

open Finset

/-- 下解の底 μ = 631/500（ρ_c(3/2) ≈ 1.26132 < μ < 2^{101/300} ≈ 1.26284）。 -/
local notation "μ" => (631 / 500 : ℝ)

/-- 2 点の Jensen（重み λ = 147/500）: `(x + y)^{5/3} ≤ (1+μ) x^{5/3} + μ y^{5/3}`。 -/
lemma jensen_split {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ (5 / 3 : ℝ) ≤ (1 + μ) * x ^ (5 / 3 : ℝ) + μ * y ^ (5 / 3 : ℝ) := by
  set p : ℝ := 5 / 3 with hp
  set l : ℝ := 147 / 500 with hl
  have hl0 : 0 < l := by norm_num [hl]
  have hl1 : 0 < 1 - l := by norm_num [hl]
  -- λ^{1-p} ≤ 1+μ と (1-λ)^{1-p} ≤ μ（3 乗して比べる）
  have key : ∀ {t c : ℝ}, 0 < t → 0 < c → 1 ≤ c ^ 3 * t ^ 2 → t ^ (1 - p) ≤ c := by
    intro t c ht hc h
    have hcube : (t ^ (1 - p)) ^ (3 : ℕ) = (t ^ 2)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, hp,
        show ((1 : ℝ) - 5 / 3) * ((3 : ℕ) : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg ht.le, Real.rpow_natCast]
    have h2 : (t ^ (1 - p)) ^ (3 : ℕ) ≤ c ^ 3 := by
      rw [hcube]
      have ht2 : 0 < t ^ 2 := by positivity
      rw [inv_le_iff_one_le_mul₀' ht2]
      linarith [mul_comm (c ^ 3) (t ^ 2)]
    exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg ht.le _) hc.le (by norm_num)).1 h2
  have k1 : l ^ (1 - p) ≤ 1 + μ := key hl0 (by norm_num) (by norm_num [hl])
  have k2 : (1 - l) ^ (1 - p) ≤ μ := key hl1 (by norm_num) (by norm_num [hl])
  have hconv := (convexOn_rpow (p := p) (by norm_num [hp])).2
    (show x / l ∈ Set.Ici (0 : ℝ) from div_nonneg hx hl0.le)
    (show y / (1 - l) ∈ Set.Ici (0 : ℝ) from div_nonneg hy hl1.le)
    hl0.le hl1.le (by ring)
  simp only [smul_eq_mul] at hconv
  have hsum : l * (x / l) + (1 - l) * (y / (1 - l)) = x + y := by
    field_simp
  rw [hsum] at hconv
  -- l (x/l)^p = l^{1-p} x^p
  have e1 : l * (x / l) ^ p = l ^ (1 - p) * x ^ p := by
    rw [Real.div_rpow hx hl0.le, Real.rpow_sub hl0, Real.rpow_one]
    field_simp
  have e2 : (1 - l) * (y / (1 - l)) ^ p = (1 - l) ^ (1 - p) * y ^ p := by
    rw [Real.div_rpow hy hl1.le, Real.rpow_sub hl1, Real.rpow_one]
    field_simp
  rw [e1, e2] at hconv
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx p
  have hyp : 0 ≤ y ^ p := Real.rpow_nonneg hy p
  calc (x + y) ^ p ≤ l ^ (1 - p) * x ^ p + (1 - l) ^ (1 - p) * y ^ p := hconv
    _ ≤ (1 + μ) * x ^ p + μ * y ^ p :=
        add_le_add (mul_le_mul_of_nonneg_right k1 hxp) (mul_le_mul_of_nonneg_right k2 hyp)

lemma one_le_mu : (1 : ℝ) ≤ μ := by norm_num

/-- 和が有限なら各項が有限（`ℕ∞`）。 -/
lemma enat_add3_eq_coe {a b c : ℕ∞} {v : ℕ} (h : a + b + c = v) :
    ∃ x y z : ℕ, a = x ∧ b = y ∧ c = z ∧ v = x + y + z := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe x =>
    induction b using ENat.recTopCoe with
    | top => simp at h
    | coe y =>
      induction c using ENat.recTopCoe with
      | top => simp at h
      | coe z =>
        refine ⟨x, y, z, rfl, rfl, rfl, ?_⟩
        have : ((x + y + z : ℕ) : ℕ∞) = (v : ℕ∞) := by push_cast; exact h
        exact (ENat.coe_inj.1 this).symm

/-- **鎖の再帰の下解**: `Fc n S = v` なら `n^{5/3} ≤ v · μ^S`。 -/
theorem Fc_lower : ∀ (S n v : ℕ), Fc n S = v → (n : ℝ) ^ (5 / 3 : ℝ) ≤ v * μ ^ S := by
  intro S
  induction S with
  | zero => intro n v h; rw [Fc_zero] at h; exact absurd h (ENat.top_ne_coe v)
  | succ S ihS =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    intro v h
    rw [Fc.eq_2] at h
    by_cases hn1 : n = 1
    · rw [if_pos hn1] at h
      have hv : v = 1 := by exact_mod_cast h.symm
      subst hn1; subst hv
      simp only [Nat.cast_one, Real.one_rpow, one_mul]
      exact one_le_pow₀ one_le_mu
    · rw [if_neg hn1] at h
      have hne : ((Ico 1 n).attach).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Finset.inf_empty] at h
        exact ENat.top_ne_coe v h
      obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_inf _ hne
        (fun m : {m // m ∈ Ico 1 n} => Fc m.1 (S + 1) + Fc m.1 S + Fc (n - m.1) S)
      rw [hm] at h
      obtain ⟨v1, v2, v3, h1, h2, h3, rfl⟩ := enat_add3_eq_coe h
      have hmI := mem_Ico.1 m.2
      have b1 := ihn m.1 hmI.2 v1 h1
      have b2 := ihS m.1 v2 h2
      have b3 := ihS (n - m.1) v3 h3
      have hsplit : (n : ℝ) = (m.1 : ℝ) + ((n - m.1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hmI.2.le]; ring
      have hJ := jensen_split (Nat.cast_nonneg m.1) (Nat.cast_nonneg (n - m.1))
      rw [← hsplit] at hJ
      have hmu : (0 : ℝ) ≤ μ := by norm_num
      push_cast
      calc (n : ℝ) ^ (5 / 3 : ℝ)
          ≤ (1 + μ) * (m.1 : ℝ) ^ (5 / 3 : ℝ) + μ * ((n - m.1 : ℕ) : ℝ) ^ (5 / 3 : ℝ) := hJ
        _ = (m.1 : ℝ) ^ (5 / 3 : ℝ) + μ * (m.1 : ℝ) ^ (5 / 3 : ℝ)
              + μ * ((n - m.1 : ℕ) : ℝ) ^ (5 / 3 : ℝ) := by ring
        _ ≤ v1 * μ ^ (S + 1) + μ * (v2 * μ ^ S) + μ * (v3 * μ ^ S) := by
            gcongr
        _ = (v1 + v2 + v3) * μ ^ (S + 1) := by ring

/-- 完全二分木: `F(T_h, S) = v` なら `(2^h − 1)^{5/3} ≤ v · μ^S`。 -/
theorem cbt_F_lower (h : ℕ) (hh : 0 < h) (S v : ℕ)
    (hF : (cbt h hh).F univ (cbt h hh).root S = v) :
    ((2 ^ h - 1 : ℕ) : ℝ) ^ (5 / 3 : ℝ) ≤ v * μ ^ S := by
  have hle := cbt_F_ge_Fc h hh S
  rw [hF] at hle
  have hne : Fc (2 ^ h - 1) S ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top v) hle
  obtain ⟨w, hw⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hw, ENat.coe_le_coe] at hle
  calc ((2 ^ h - 1 : ℕ) : ℝ) ^ (5 / 3 : ℝ) ≤ w * μ ^ S := Fc_lower S _ w hw.symm
    _ ≤ v * μ ^ S := by gcongr

/-- `504 (j+15) + 504 ≤ 2^(j+14)`（`clog` の評価に使う）。 -/
lemma lin_le_pow : ∀ j : ℕ, 504 * (j + 15) + 504 ≤ 2 ^ (j + 14) := by
  intro j
  induction j with
  | zero => norm_num
  | succ j ih =>
    have : 504 ≤ 2 ^ (j + 14) := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 14 ≤ j + 14))
    rw [pow_succ]; omega

/-- `h > 2^14` なら `504 ⌈log₂ h⌉ + 505 ≤ h`。 -/
lemma clog_small {h : ℕ} (hH : 2 ^ 14 < h) : 504 * Nat.clog 2 h + 505 ≤ h := by
  have hk15 : 14 < Nat.clog 2 h := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hH
  have hlow : 2 ^ (Nat.clog 2 h - 1) < h := Nat.pow_lt_of_lt_clog (by omega)
  obtain ⟨j, hj⟩ : ∃ j, Nat.clog 2 h = j + 15 := ⟨Nat.clog 2 h - 15, by omega⟩
  have := lin_le_pow j
  rw [hj, show j + 15 - 1 = j + 14 by omega] at hlow
  rw [hj]
  omega

/-- `μ^{h + ⌈log₂ h⌉} ≤ (2^h − 1)^{101/300}`（`h > 2^14`）。 -/
lemma mu_pow_le {h : ℕ} (hH : 2 ^ 14 < h) :
    μ ^ (h + Nat.clog 2 h) ≤ ((2 ^ h - 1 : ℕ) : ℝ) ^ (101 / 300 : ℝ) := by
  set c := Nat.clog 2 h
  have hc := clog_small hH
  have hh1 : 1 ≤ h := by omega
  -- 2^{h-1} ≤ 2^h - 1
  have hN : 2 ^ (h - 1) ≤ 2 ^ h - 1 := by
    have : 2 ^ h = 2 * 2 ^ (h - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
    omega
  have hNpos : (0 : ℝ) < ((2 ^ h - 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
    exact_mod_cast (show 0 < 2 ^ h - 1 by omega)
  rw [← pow_le_pow_iff_left₀ (pow_nonneg (by norm_num) _) (Real.rpow_nonneg hNpos.le _)
    (by norm_num : (1500 : ℕ) ≠ 0)]
  rw [← Real.rpow_natCast (((2 ^ h - 1 : ℕ) : ℝ) ^ (101 / 300 : ℝ)), ← Real.rpow_mul hNpos.le,
    show (101 / 300 : ℝ) * ((1500 : ℕ) : ℝ) = ((505 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← pow_mul]
  have hmu : μ ^ 125 ≤ (2 : ℝ) ^ 42 := by norm_num
  calc μ ^ ((h + c) * 1500) = (μ ^ 125) ^ (12 * (h + c)) := by rw [← pow_mul]; ring_nf
    _ ≤ ((2 : ℝ) ^ 42) ^ (12 * (h + c)) := by gcongr
    _ = (2 : ℝ) ^ (504 * (h + c)) := by rw [← pow_mul]; ring_nf
    _ ≤ (2 : ℝ) ^ (505 * (h - 1)) := by
        apply pow_le_pow_right₀ (by norm_num); omega
    _ = ((2 : ℝ) ^ (h - 1)) ^ 505 := by rw [← pow_mul]; ring_nf
    _ ≤ (((2 ^ h - 1 : ℕ) : ℝ)) ^ 505 := by
        gcongr
        exact_mod_cast hN

/-- **指数 1.33**: `h > 2^14` かつ `S ≤ h + ⌈log₂ h⌉` なら `(2^h − 1)^{1.33} ≤ F(T_h, S)`。 -/
theorem cbt_F_exponent (h : ℕ) (hh : 0 < h) (hH : 2 ^ 14 < h) (S : ℕ) (hS : S ≤ h + Nat.clog 2 h)
    (v : ℕ) (hF : (cbt h hh).F univ (cbt h hh).root S = v) :
    ((2 ^ h - 1 : ℕ) : ℝ) ^ (133 / 100 : ℝ) ≤ v := by
  set N : ℝ := ((2 ^ h - 1 : ℕ) : ℝ)
  have hNpos : 0 < N := by
    have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
    have : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ']; congr 1; omega
    exact Nat.cast_pos.2 (by omega)
  have hlow := cbt_F_lower h hh S v hF
  have hmuS : μ ^ S ≤ μ ^ (h + Nat.clog 2 h) := pow_le_pow_right₀ one_le_mu hS
  have hkey := mu_pow_le hH
  have hsplit : N ^ (5 / 3 : ℝ) = N ^ (133 / 100 : ℝ) * N ^ (101 / 300 : ℝ) := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hpos : 0 < μ ^ (h + Nat.clog 2 h) := by positivity
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  -- N^{1.33} μ^{h+c} ≤ N^{1.33} N^{101/300} = N^{5/3} ≤ v μ^S ≤ v μ^{h+c}
  have : N ^ (133 / 100 : ℝ) * μ ^ (h + Nat.clog 2 h) ≤ v * μ ^ (h + Nat.clog 2 h) :=
    calc N ^ (133 / 100 : ℝ) * μ ^ (h + Nat.clog 2 h)
        ≤ N ^ (133 / 100 : ℝ) * N ^ (101 / 300 : ℝ) :=
          mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (5 / 3 : ℝ) := hsplit.symm
      _ ≤ v * μ ^ S := hlow
      _ ≤ v * μ ^ (h + Nat.clog 2 h) := mul_le_mul_of_nonneg_left hmuS hv0
  exact le_of_mul_le_mul_right this hpos

open scoped Classical in
/-- 上を最小ペブル数 `R•(T_h)` に当てたもの（`R•(T_h) ≤ h + ⌈log₂ h⌉` は `cbt_Rb_le`）。 -/
theorem cbt_F_Rb_exponent (h : ℕ) (hh : 0 < h) (hH : 2 ^ 14 < h) (v : ℕ)
    (hF : (cbt h hh).F univ (cbt h hh).root (Rb (cbt_pebbling_exists h hh)) = v) :
    ((2 ^ h - 1 : ℕ) : ℝ) ^ (133 / 100 : ℝ) ≤ v :=
  cbt_F_exponent h hh hH _ (cbt_Rb_le h hh) v hF

open scoped Classical in
/-- **上と定理 1 を合わせた形**: `h > 2^14` なら `F(T_h, R•(T_h))` は有限で、
`(2^h − 1)^{1.33} ≤ F(T_h, R•(T_h)) ≤ 3^{R•(T_h) − 1}`。 -/
theorem cbt_F_Rbullet_two_sided (h : ℕ) (hh : 0 < h) (hH : 2 ^ 14 < h) :
    ∃ v : ℕ, (cbt h hh).F univ (cbt h hh).root (cbt h hh).Rbullet = v ∧
      ((2 ^ h - 1 : ℕ) : ℝ) ^ (133 / 100 : ℝ) ≤ v ∧ v ≤ 3 ^ ((cbt h hh).Rbullet - 1) := by
  obtain ⟨v, hv, -, hle⟩ := (cbt h hh).theorem1_F_Rbullet
  have hR : (cbt h hh).Rbullet ≤ h + Nat.clog 2 h := Nat.find_min' _ ⟨_, cbt_pebbling h hh⟩
  exact ⟨v, hv, cbt_F_exponent h hh hH _ hR v hv, hle⟩

end P5Tree
