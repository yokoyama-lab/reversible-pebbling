/-
# P5 定理 C の指数を 1.3317 へ: 完全二分木の再帰 `F` の指数は 1.3317 以上

`P5TreeLower.lean`（指数 1.33）と同じ下解 `Fc n S ≥ n^{5/3} · μ^{−S}` を，底 μ を
ρ_c(3/2) ≈ 1.2613248 のすぐ上の μ = 126133/100000 に詰めて当てる。指数は 5/3 − log₂ μ ≈ 1.331729 で，
q = 3/2 での上限 1 + 1/q − log₂ ρ_c(q) = 1.3317269 にほぼ等しい（全体の上限 1 + κ* = 1.3317424 は q ≈ 1.515 で，
差は 2·10⁻⁵ 未満）。原稿 `2026-WiNF/P5-tree-exponent.tex` §6 (3) の「1 + κ* = 1.3317…」の 4 桁目までにあたる。

  * `jensen_split_of`: 重み λ と底 μ が `1 ≤ (1+μ)^3 λ^2`，`1 ≤ μ^3 (1−λ)^2` を満たせば
    `(x + y)^{5/3} ≤ (1+μ) x^{5/3} + μ y^{5/3}`（`P5TreeLower.jensen_split` を μ, λ について一般にしたもの）
  * `Fc_lower_of`: 上の不等式を満たす `μ ≥ 1` で `n^{5/3} ≤ Fc n S · μ^S`
  * `nu_pow_le_two_pow`: `ν^{60000} ≤ 2^{20097}`（ν = 126133/100000．自然数の大小をカーネルの計算（`decide +kernel`．追加の公理なし）で確かめる）
  * `cbt_F_exponent_sharp`: `h > 2^19` かつ `S ≤ h + ⌈log₂ h⌉` で `(2^h − 1)^{1.3317} ≤ F(T_h, S)`
  * `cbt_F_Rbullet_two_sided_sharp`: `F(T_h, R•(T_h))` は有限で `(2^h − 1)^{1.3317} ≤ F ≤ 3^{R• − 1}`

ここで得るのは再帰 `F` の下界であって，最短手数 `M` の下界ではない（`M ≤ F` の向きしか無い）。
-/
import Revgarbage.P5TreeLower

namespace P5Tree

open Finset

/-- 2 点の Jensen（一般の μ, λ）。 -/
lemma jensen_split_of {μ l : ℝ} (hμ : 0 < μ) (hl0 : 0 < l) (hl1 : 0 < 1 - l)
    (c1 : 1 ≤ (1 + μ) ^ 3 * l ^ 2) (c2 : 1 ≤ μ ^ 3 * (1 - l) ^ 2) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ (5 / 3 : ℝ) ≤ (1 + μ) * x ^ (5 / 3 : ℝ) + μ * y ^ (5 / 3 : ℝ) := by
  set p : ℝ := 5 / 3 with hp
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
  have k1 : l ^ (1 - p) ≤ 1 + μ := key hl0 (by linarith) c1
  have k2 : (1 - l) ^ (1 - p) ≤ μ := key hl1 hμ c2
  have hconv := (convexOn_rpow (p := p) (by norm_num [hp])).2
    (show x / l ∈ Set.Ici (0 : ℝ) from div_nonneg hx hl0.le)
    (show y / (1 - l) ∈ Set.Ici (0 : ℝ) from div_nonneg hy hl1.le)
    hl0.le hl1.le (by ring)
  simp only [smul_eq_mul] at hconv
  have hsum : l * (x / l) + (1 - l) * (y / (1 - l)) = x + y := by
    field_simp
  rw [hsum] at hconv
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

/-- **鎖の再帰の下解（一般の μ）**: 2 点の Jensen を満たす `μ ≥ 1` で，`Fc n S = v` なら `n^{5/3} ≤ v · μ^S`。 -/
theorem Fc_lower_of {μ : ℝ} (hμ : 1 ≤ μ)
    (hJ : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      (x + y) ^ (5 / 3 : ℝ) ≤ (1 + μ) * x ^ (5 / 3 : ℝ) + μ * y ^ (5 / 3 : ℝ)) :
    ∀ (S n v : ℕ), Fc n S = v → (n : ℝ) ^ (5 / 3 : ℝ) ≤ v * μ ^ S := by
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
      exact one_le_pow₀ hμ
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
      have hJ' := hJ _ _ (Nat.cast_nonneg m.1) (Nat.cast_nonneg (n - m.1))
      rw [← hsplit] at hJ'
      have hmu : (0 : ℝ) ≤ μ := by linarith
      push_cast
      calc (n : ℝ) ^ (5 / 3 : ℝ)
          ≤ (1 + μ) * (m.1 : ℝ) ^ (5 / 3 : ℝ) + μ * ((n - m.1 : ℕ) : ℝ) ^ (5 / 3 : ℝ) := hJ'
        _ = (m.1 : ℝ) ^ (5 / 3 : ℝ) + μ * (m.1 : ℝ) ^ (5 / 3 : ℝ)
              + μ * ((n - m.1 : ℕ) : ℝ) ^ (5 / 3 : ℝ) := by ring
        _ ≤ v1 * μ ^ (S + 1) + μ * (v2 * μ ^ S) + μ * (v3 * μ ^ S) := by
            gcongr
        _ = (v1 + v2 + v3) * μ ^ (S + 1) := by ring

/-- 詰めた底 ν = 126133/100000（ρ_c(3/2) ≈ 1.2613248 < ν < 2^{20097/60000} ≈ 1.2613337）。 -/
local notation "ν" => (126133 / 100000 : ℝ)

lemma one_le_nu : (1 : ℝ) ≤ ν := by norm_num

/-- ν での 2 点の Jensen（重み λ = 11763/40000）。 -/
lemma jensen_split_nu {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ (5 / 3 : ℝ) ≤ (1 + ν) * x ^ (5 / 3 : ℝ) + ν * y ^ (5 / 3 : ℝ) :=
  jensen_split_of (l := 11763 / 40000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hx hy

/-- 鎖の再帰の下解（底 ν）。 -/
theorem Fc_lower_nu (S n v : ℕ) (h : Fc n S = v) : (n : ℝ) ^ (5 / 3 : ℝ) ≤ v * ν ^ S :=
  Fc_lower_of one_le_nu (fun _ _ hx hy => jensen_split_nu hx hy) S n v h

/-- 完全二分木: `F(T_h, S) = v` なら `(2^h − 1)^{5/3} ≤ v · ν^S`。 -/
theorem cbt_F_lower_nu (h : ℕ) (hh : 0 < h) (S v : ℕ)
    (hF : (cbt h hh).F univ (cbt h hh).root S = v) :
    ((2 ^ h - 1 : ℕ) : ℝ) ^ (5 / 3 : ℝ) ≤ v * ν ^ S := by
  have hle := cbt_F_ge_Fc h hh S
  rw [hF] at hle
  have hne : Fc (2 ^ h - 1) S ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top v) hle
  obtain ⟨w, hw⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hw, ENat.coe_le_coe] at hle
  calc ((2 ^ h - 1 : ℕ) : ℝ) ^ (5 / 3 : ℝ) ≤ w * ν ^ S := Fc_lower_nu S _ w hw.symm
    _ ≤ v * ν ^ S := by gcongr

/-- `ν^{60000} ≤ 2^{20097}`，すなわち log₂ ν ≤ 20097/60000（自然数の大小に直して計算で確かめる）。 -/
lemma nu_pow_le_two_pow : ν ^ 60000 ≤ (2 : ℝ) ^ 20097 := by
  have hnat : (126133 : ℕ) ^ 60000 ≤ 2 ^ 20097 * (100000 : ℕ) ^ 60000 :=
    by decide +kernel
  have hreal : (126133 : ℝ) ^ 60000 ≤ (2 : ℝ) ^ 20097 * (100000 : ℝ) ^ 60000 := by
    exact_mod_cast hnat
  rw [div_pow, div_le_iff₀ (by positivity)]
  exact hreal

/-- `20097 (j+20) + 20098 ≤ 2^(j+19)`（`clog` の評価に使う）。 -/
lemma lin_le_pow_sharp : ∀ j : ℕ, 20097 * (j + 20) + 20098 ≤ 2 ^ (j + 19) := by
  intro j
  induction j with
  | zero => norm_num
  | succ j ih =>
    have : 20097 ≤ 2 ^ (j + 19) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 19 ≤ j + 19))
    rw [pow_succ]; omega

/-- `h > 2^19` なら `20097 ⌈log₂ h⌉ + 20098 ≤ h`。 -/
lemma clog_small_sharp {h : ℕ} (hH : 2 ^ 19 < h) : 20097 * Nat.clog 2 h + 20098 ≤ h := by
  have hk : 19 < Nat.clog 2 h := (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hH
  have hlow : 2 ^ (Nat.clog 2 h - 1) < h := Nat.pow_lt_of_lt_clog (by omega)
  obtain ⟨j, hj⟩ : ∃ j, Nat.clog 2 h = j + 20 := ⟨Nat.clog 2 h - 20, by omega⟩
  have := lin_le_pow_sharp j
  rw [hj, show j + 20 - 1 = j + 19 by omega] at hlow
  rw [hj]
  omega

/-- `ν^{h + ⌈log₂ h⌉} ≤ (2^h − 1)^{10049/30000}`（`h > 2^19`．10049/30000 = 5/3 − 1.3317）。 -/
lemma nu_pow_le {h : ℕ} (hH : 2 ^ 19 < h) :
    ν ^ (h + Nat.clog 2 h) ≤ ((2 ^ h - 1 : ℕ) : ℝ) ^ (10049 / 30000 : ℝ) := by
  set c := Nat.clog 2 h
  have hc := clog_small_sharp hH
  have hh1 : 1 ≤ h := by omega
  have hN : 2 ^ (h - 1) ≤ 2 ^ h - 1 := by
    have : 2 ^ h = 2 * 2 ^ (h - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
    omega
  have hNpos : (0 : ℝ) < ((2 ^ h - 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
    exact_mod_cast (show 0 < 2 ^ h - 1 by omega)
  rw [← pow_le_pow_iff_left₀ (pow_nonneg (by norm_num) _) (Real.rpow_nonneg hNpos.le _)
    (by norm_num : (60000 : ℕ) ≠ 0)]
  rw [← Real.rpow_natCast (((2 ^ h - 1 : ℕ) : ℝ) ^ (10049 / 30000 : ℝ)), ← Real.rpow_mul hNpos.le,
    show (10049 / 30000 : ℝ) * ((60000 : ℕ) : ℝ) = ((20098 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← pow_mul]
  calc ν ^ ((h + c) * 60000) = (ν ^ 60000) ^ (h + c) := by rw [← pow_mul]; ring_nf
    _ ≤ ((2 : ℝ) ^ 20097) ^ (h + c) := by gcongr; exact nu_pow_le_two_pow
    _ = (2 : ℝ) ^ (20097 * (h + c)) := by rw [← pow_mul]
    _ ≤ (2 : ℝ) ^ (20098 * (h - 1)) := by
        apply pow_le_pow_right₀ (by norm_num); omega
    _ = ((2 : ℝ) ^ (h - 1)) ^ 20098 := by rw [← pow_mul]; ring_nf
    _ ≤ (((2 ^ h - 1 : ℕ) : ℝ)) ^ 20098 := by
        gcongr
        exact_mod_cast hN

/-- **定理 C（指数 1.3317）**: `h > 2^19` かつ `S ≤ h + ⌈log₂ h⌉` なら `(2^h − 1)^{1.3317} ≤ F(T_h, S)`。 -/
theorem cbt_F_exponent_sharp (h : ℕ) (hh : 0 < h) (hH : 2 ^ 19 < h) (S : ℕ)
    (hS : S ≤ h + Nat.clog 2 h) (v : ℕ) (hF : (cbt h hh).F univ (cbt h hh).root S = v) :
    ((2 ^ h - 1 : ℕ) : ℝ) ^ (13317 / 10000 : ℝ) ≤ v := by
  set N : ℝ := ((2 ^ h - 1 : ℕ) : ℝ)
  have hNpos : 0 < N := by
    have : 1 ≤ 2 ^ (h - 1) := Nat.one_le_two_pow
    have : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ']; congr 1; omega
    exact Nat.cast_pos.2 (by omega)
  have hlow := cbt_F_lower_nu h hh S v hF
  have hnuS : ν ^ S ≤ ν ^ (h + Nat.clog 2 h) := pow_le_pow_right₀ one_le_nu hS
  have hkey := nu_pow_le hH
  have hsplit : N ^ (5 / 3 : ℝ) = N ^ (13317 / 10000 : ℝ) * N ^ (10049 / 30000 : ℝ) := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hpos : 0 < ν ^ (h + Nat.clog 2 h) := by positivity
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have : N ^ (13317 / 10000 : ℝ) * ν ^ (h + Nat.clog 2 h) ≤ v * ν ^ (h + Nat.clog 2 h) :=
    calc N ^ (13317 / 10000 : ℝ) * ν ^ (h + Nat.clog 2 h)
        ≤ N ^ (13317 / 10000 : ℝ) * N ^ (10049 / 30000 : ℝ) :=
          mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (5 / 3 : ℝ) := hsplit.symm
      _ ≤ v * ν ^ S := hlow
      _ ≤ v * ν ^ (h + Nat.clog 2 h) := mul_le_mul_of_nonneg_left hnuS hv0
  exact le_of_mul_le_mul_right this hpos

open scoped Classical in
/-- 定理 C（1.3317）を最小ペブル数 `R•(T_h)` に当てたもの。 -/
theorem cbt_F_Rb_exponent_sharp (h : ℕ) (hh : 0 < h) (hH : 2 ^ 19 < h) (v : ℕ)
    (hF : (cbt h hh).F univ (cbt h hh).root (Rb (cbt_pebbling_exists h hh)) = v) :
    ((2 ^ h - 1 : ℕ) : ℝ) ^ (13317 / 10000 : ℝ) ≤ v :=
  cbt_F_exponent_sharp h hh hH _ (cbt_Rb_le h hh) v hF

open scoped Classical in
/-- **定理 C（1.3317）と定理 1 を合わせた形**: `h > 2^19` なら `F(T_h, R•(T_h))` は有限で，
`(2^h − 1)^{1.3317} ≤ F(T_h, R•(T_h)) ≤ 3^{R•(T_h) − 1}`。 -/
theorem cbt_F_Rbullet_two_sided_sharp (h : ℕ) (hh : 0 < h) (hH : 2 ^ 19 < h) :
    ∃ v : ℕ, (cbt h hh).F univ (cbt h hh).root (cbt h hh).Rbullet = v ∧
      ((2 ^ h - 1 : ℕ) : ℝ) ^ (13317 / 10000 : ℝ) ≤ v ∧ v ≤ 3 ^ ((cbt h hh).Rbullet - 1) := by
  obtain ⟨v, hv, -, hle⟩ := (cbt h hh).theorem1_F_Rbullet
  have hR : (cbt h hh).Rbullet ≤ h + Nat.clog 2 h := Nat.find_min' _ ⟨_, cbt_pebbling h hh⟩
  exact ⟨v, hv, cbt_F_exponent_sharp h hh hH _ hR v hv, hle⟩

end P5Tree
