/-
# 完全二分木の手数の階段: 上界の極限と両側の極限

`p = ⌊n^ε⌋`（`n = 2^h − 1`）のとき、`T(T_h, p)/n → 2⌈1/ε⌉`（`ε > 0`、`1/ε ∉ ℤ`）。
紙は `notes/spooky-pebbling/tree-gap/STEP_2026-10-28.md` の「系（極限は紙）」。

* 下界の極限は `WindowLowerLimit.lean` の `Ttree_rpow`（δ の形、`1/ε ∉ ℤ` は要らない）を使う（書き換えない）。
* 上界の有限の不等式は `StepUpper.lean` の `time_upper_bound_step`（`1 ≤ Λ < h`、`2^{Λ+1} ≤ p`、
  `2^Λ ≤ (p−1) − (h−Λ)` で `T + 3 ≤ 2(⌊(h−1)/Λ⌋+1)·2^h`）。幅は紙の `Λ = ⌊log₂p⌋ − 1` ではなく
  `Λ = ⌊h/K⌋ + 1`（`K ≥ 2`）と取る。すると `KΛ > h` なので `⌊(h−1)/Λ⌋ + 1 ≤ K`、仮定は
  `2^{⌊h/K⌋+2} + h + 1 ≤ p` から出る（`Ttree_le_step`）。`Kε > 1` なら `p = ⌊n^ε⌋` は十分大きい `h` でこれを満たす。
* `K = 1`（`ε > 1`、ペブルが `n` 個以上）では `Λ < h` が取れないので、全頂点を置いてから根を残して外す
  構成 `strategyFull`（手数 `2n − 1`、ペブル `n` 個）を新しく足した（`time_upper_bound_full`）。

主な定理:
* `time_upper_bound_full`: `1 ≤ h`、`2^h − 1 ≤ cap` なら `Valid h cap T ms` かつ `T + 3 = 2·2^h` の手順がある。
* `Ttree_le_step`: `2 ≤ K`、`3 ≤ h`、`2^{⌊h/K⌋+2} + h + 1 ≤ cap` なら `T(h, cap) + 3 ≤ 2K·2^h`。
* `Ttree_rpow_upper`: `ε > 0`、`K ≥ 1`、`Kε > 1` なら十分大きい `h` で `T(h, ⌊n^ε⌋) + 3 ≤ 2K·2^h`。
* `Ttree_rpow_limsup_K`: 同じ仮定で `limsup T/n ≤ 2K`（`EReal`）。`1/ε ∈ ℤ` でも使える（`K = 1/ε + 1`）。
* `Ttree_rpow_limsup`・`Ttree_rpow_tendsto`: `ε > 0`、`1/ε ∉ ℤ` なら `limsup T/n ≤ 2⌈1/ε⌉`、`T/n → 2⌈1/ε⌉`。
* `Ttree_rpow_tendsto_one_le`: `ε ≥ 1`（整数の境界 `ε = 1` を含む）では `T/n → 2`。
* `Ttree_rpow_inv_nat`: `ε = 1/m`（`m ≥ 1`）では `2m ≤ liminf`、`limsup ≤ 2(m+1)`（境界の値はこのファイルでは決めない）。
* `TtreeK_*`: KSS の意味論（`ValidK`）で同じこと。
-/
import SpookyTree.StepUpper
import SpookyTree.WindowLowerLimit

open Filter Topology

namespace SpookyTree

/-! ## 全頂点を置いてから外す構成（`K = 1`） -/

/-- 全頂点を後順で置き（根を含む）、根を残して左右の部分木を前順で外す。 -/
def strategyFull (h : ℕ) : List Move :=
  placeInt .pebble h [] ++ (removeInt (h - 1) [false] ++ removeInt (h - 1) [true])

/-- **仕様.** `1 ≤ h` なら `strategyFull` は空の盤から合法で、ペブルは `2^h − 1` 個以下、
終わると根だけペブル・他は空。 -/
theorem strategy_full_spec {h : ℕ} (hh : 1 ≤ h) :
    Runs h h [] (2 ^ h - 1) (fun _ => Cell.empty) (strategyFull h) ∧
    run (fun _ => Cell.empty) (strategyFull h) [] = .pebble ∧
    ∀ z : Node, z.length < h → z ≠ [] →
      run (fun _ => Cell.empty) (strategyFull h) z = .empty := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  simp only [strategyFull, Nat.add_sub_cancel]
  -- 1. 全頂点を置く
  have hP0 : Pat (glue .empty (k + 1) (cst .empty)) (0 + (k + 1)) [] (fun _ => Cell.empty) := by
    rw [glue_cst]; intro w _; rfl
  obtain ⟨hR1, hQ1⟩ := placeInt_spec (h := k + 1) (j := 0) (pl := .pebble) (X := .empty)
    (Or.inl ⟨rfl, rfl⟩) (g := cst .empty) (fun h0 => absurd h0 (by decide)) (k + 1) []
    (fun _ => Cell.empty) (by simp only [List.length_nil]; omega) hP0
  have hpk1 : pcPat (glue .pebble (k + 1) (cst .empty)) (0 + (k + 1)) ≤ 2 ^ (k + 1) - 1 := by
    have h1 := pcPat_glue_peb (cst .empty) 0 (k + 1)
    rw [pcPat_cst (X := .empty) (by decide)] at h1
    omega
  have hR1' := hR1.mono hpk1
  rw [Nat.zero_add] at hR1'
  have hQ1' : Pat (glue .pebble (k + 1) (cst .empty)) (0 + k + 1) [] _ := hQ1
  obtain ⟨hr1, hA0, hA1⟩ := Pat_succ.mp hQ1'
  rw [glue_succ_zero] at hr1
  rw [glue_succ_shift] at hA0 hA1
  simp only [List.nil_append] at hA0 hA1
  -- 2. 根を残して左右の部分木を外す
  obtain ⟨hR2, hr2, hB0, hB1⟩ := runs_two (h := k + 1) (k := 0 + k)
    (p := pcPat (glue .pebble k (cst .empty)) (0 + k))
    (q := pcPat (glue .pebble k (cst .empty)) (0 + k))
    (F := glue .pebble k (cst .empty)) (G := glue .empty k (cst .empty)) hr1 hA0 hA1
    (fun c' hP => removeInt_spec (h := k + 1) (j := 0) (g := cst .empty)
      (fun h0 => absurd h0 (by decide)) k [false] c'
      (by simp only [List.length_cons, List.length_nil]; omega) hP)
    (fun c' hP => removeInt_spec (h := k + 1) (j := 0) (g := cst .empty)
      (fun h0 => absurd h0 (by decide)) k [true] c'
      (by simp only [List.length_cons, List.length_nil]; omega) hP)
    le_rfl (pcPat_glue_le .empty (cst .empty) _ k)
  have hpk2 : pcPat (glue .pebble k (cst .empty)) (0 + k) +
      (1 + pcPat (glue .pebble k (cst .empty)) (0 + k)) ≤ 2 ^ (k + 1) - 1 := by
    have h2 := pcPat_glue_peb (cst .empty) 0 k
    rw [pcPat_cst (X := .empty) (by decide)] at h2
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have hR2' := hR2.mono hpk2
  rw [Nat.zero_add] at hR2'
  rw [glue_cst] at hB0 hB1
  refine ⟨Runs_append.mpr ⟨hR1', hR2'⟩, ?_, ?_⟩
  · rw [run_append]; exact hr2
  · intro z hz hne
    rw [run_append]
    match z, hz, hne with
    | [], _, hne => exact absurd rfl hne
    | false :: w, hz, _ => exact hB0 w (by simp only [List.length_cons] at hz; omega)
    | true :: w, hz, _ => exact hB1 w (by simp only [List.length_cons] at hz; omega)

/-- **手数（全頂点を置く構成）.** `1 ≤ h`、`2^h − 1 ≤ cap` なら、`T + 3 = 2·2^h`（`T = 2n − 1`）の妥当な手順がある。 -/
theorem time_upper_bound_full {h cap : ℕ} (hh : 1 ≤ h) (hc : 2 ^ h - 1 ≤ cap) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h cap T ms ∧ T + 3 = 2 * 2 ^ h := by
  obtain ⟨hR, hroot, hothers⟩ := strategy_full_spec hh
  refine ⟨(strategyFull h).length, seqOf (strategyFull h),
    valid_of_runs (hR.mono hc) hroot hothers, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have e1 := length_placeInt .pebble (k + 1) []
  have e2 := length_removeInt k [false]
  have e3 := length_removeInt k [true]
  have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  simp only [strategyFull, Nat.add_sub_cancel, List.length_append]
  omega

/-- 同じことを KSS の意味論で。 -/
theorem time_upper_bound_full_kss {h cap : ℕ} (hh : 1 ≤ h) (hc : 2 ^ h - 1 ≤ cap) :
    ∃ (T : ℕ) (ms : ℕ → Move), ValidK h cap T ms ∧ T + 3 = 2 * 2 ^ h := by
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_full hh hc
  exact ⟨T, msK h ms, validK_of_valid hV, hT⟩

/-! ## 最小手数の有限の上界 -/

/-- 妥当な手順が 1 つあれば、最小手数はその手数以下。 -/
theorem Ttree_le_of_valid {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) :
    Ttree h cap ≤ T :=
  Nat.sInf_le ⟨ms, hV⟩

/-- **`K = 1`.** `1 ≤ h`、`2^h − 1 ≤ cap` なら `T(h, cap) + 3 ≤ 2·2^h`。 -/
theorem Ttree_le_full {h cap : ℕ} (hh : 1 ≤ h) (hc : 2 ^ h - 1 ≤ cap) :
    Ttree h cap + 3 ≤ 2 * 2 ^ h := by
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_full hh hc
  have := Ttree_le_of_valid hV
  omega

/-- **`K ≥ 2`.** `2 ≤ K`、`3 ≤ h`、`2^{⌊h/K⌋+2} + h + 1 ≤ cap` なら `T(h, cap) + 3 ≤ 2K·2^h`。
`time_upper_bound_step` を `budget = cap − 1`、`Λ = ⌊h/K⌋ + 1` で使う。 -/
theorem Ttree_le_step {h cap K : ℕ} (hK : 2 ≤ K) (hh : 3 ≤ h)
    (hc : 2 ^ (h / K + 2) + h + 1 ≤ cap) : Ttree h cap + 3 ≤ 2 * K * 2 ^ h := by
  have hK0 : 0 < K := by omega
  have hdiv2 : h / K ≤ h / 2 := Nat.div_le_div_left hK (by norm_num)
  have hlt := Nat.lt_div_mul_add (a := h) hK0
  -- `omega` は変数で割る項を扱わないので `q = ⌊h/K⌋` と名前を付ける
  obtain ⟨q, hqdef⟩ : ∃ q, q = h / K := ⟨_, rfl⟩
  rw [← hqdef] at hdiv2 hlt hc
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = q + 1 := ⟨_, rfl⟩
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛh : Λ < h := by omega
  have hP : 2 ^ (Λ + 1) = 2 * 2 ^ Λ := by ring
  have hc' : 2 ^ (Λ + 1) + h + 1 ≤ cap := by
    rw [hΛdef, show q + 1 + 1 = q + 2 by ring]; exact hc
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_step (h := h) (budget := cap - 1) (Λ := Λ) hΛ1 hΛh
    (by omega) (by omega)
  have hcapeq : cap - 1 + 1 = cap := by omega
  rw [hcapeq] at hV
  have hle := Ttree_le_of_valid hV
  -- `(h−1)/Λ + 1 ≤ K`（`KΛ = K(⌊h/K⌋+1) > h`）
  have hKΛ : h - 1 < K * Λ := by
    have h2 : K * Λ = q * K + K := by rw [hΛdef]; ring
    rw [h2]
    exact lt_of_le_of_lt (Nat.sub_le h 1) hlt
  have hq : (h - 1) / Λ < K := (Nat.div_lt_iff_lt_mul (by omega)).mpr hKΛ
  have hmono : 2 * ((h - 1) / Λ + 1) * 2 ^ h ≤ 2 * K * 2 ^ h :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hq))
  calc Ttree h cap + 3 ≤ T + 3 := by omega
    _ ≤ 2 * ((h - 1) / Λ + 1) * 2 ^ h := hT
    _ ≤ 2 * K * 2 ^ h := hmono

/-! ## `p = ⌊n^ε⌋` は十分大きい `h` で仮定を満たす -/

/-- `n = 2^h − 1 > 0`（`h ≥ 1`）。 -/
theorem eventually_npos : ∀ᶠ h : ℕ in atTop, (0 : ℝ) < ((2 ^ h - 1 : ℕ) : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with h h1
  have h2 : 2 ≤ 2 ^ h := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) h1
  have : 1 ≤ 2 ^ h - 1 := by omega
  exact_mod_cast this

/-- **`K ≥ 1`、`Kε > 1` なら、十分大きい `h` で `2^{⌊h/K⌋+2} + h + 1 ≤ ⌊n^ε⌋`。**
`a = 2^{1/K}`、`b = 2^ε`、`r = 2^{ε−1/K} > 1`（`ar = b`）とおき、`2^{⌊h/K⌋} ≤ a^h`、
`n^ε ≥ (2^h/2)^ε = b^h/b`、`4a^h·b ≤ b^h/2`（`r^h ≥ 8b`）、`2h·b ≤ b^h/2` を合わせる。 -/
theorem eventually_step_cap {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : 1 ≤ K) (hKε : 1 < K * ε) :
    ∀ᶠ h : ℕ in atTop, 2 ^ (h / K + 2) + h + 1 ≤ ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hgap : 0 < ε - 1 / K := by
    have h1 : 1 / (K : ℝ) < ε := by
      rw [div_lt_iff₀ hK0]
      linarith [mul_comm (K : ℝ) ε]
    linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (2 : ℝ) ^ ((1 : ℝ) / K) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ (ε - 1 / K) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (2 : ℝ) ^ ε := ⟨_, rfl⟩
  have hab : a * r = b := by
    rw [ha, hr, hb, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hr1 : 1 < r := by rw [hr]; exact Real.one_lt_rpow (by norm_num) hgap
  have hb1 : 1 < b := by rw [hb]; exact Real.one_lt_rpow (by norm_num) hε
  have ha0 : 0 < a := by rw [ha]; positivity
  have hb0 : 0 < b := by linarith
  have hev1 := (tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_ge_atTop (8 * b)
  have hev2 := eventually_two_mul_le_mul_pow hb1 (show (0 : ℝ) < 1 / (2 * b) by positivity)
  filter_upwards [hev1, hev2, eventually_ge_atTop 1] with h h1 h2 h3
  -- `2^{⌊h/K⌋} ≤ a^h`
  have hpowK : (2 : ℝ) ^ (h / K) ≤ a ^ h := by
    rw [ha, ← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc ((h / K : ℕ) : ℝ) ≤ (h : ℝ) / K := Nat.cast_div_le
      _ = 1 / K * h := by ring
  -- `b^h / b ≤ n^ε`
  have hn : (2 : ℝ) ^ h / 2 ≤ ((2 ^ h - 1 : ℕ) : ℝ) := by
    rw [cast_two_pow_sub_one]
    have : (2 : ℝ) ≤ 2 ^ h := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ h := pow_le_pow_right₀ (by norm_num) h3
    linarith
  have hlow : b ^ h / b ≤ ((2 ^ h - 1 : ℕ) : ℝ) ^ ε := by
    have e : b ^ h / b = ((2 : ℝ) ^ h / 2) ^ ε := by
      rw [hb, Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast_mul (by norm_num),
        mul_comm (h : ℝ) ε, Real.rpow_mul_natCast (by norm_num)]
    rw [e]
    exact Real.rpow_le_rpow (by positivity) hn hε.le
  -- `4 a^h b ≤ b^h / 2`
  have hkey : 4 * (a ^ h * b) ≤ b ^ h / 2 := by
    have hm := mul_le_mul_of_nonneg_left h1 (pow_pos ha0 h).le
    have hbh : b ^ h = a ^ h * r ^ h := by rw [← hab, mul_pow]
    rw [hbh]
    have e1 : 4 * (a ^ h * b) = a ^ h * (8 * b) / 2 := by ring
    rw [e1]
    exact div_le_div_of_nonneg_right hm (by norm_num)
  -- `2h·b ≤ b^h / 2`
  have h2' : 2 * (h : ℝ) * b ≤ b ^ h / 2 := by
    have hm := mul_le_mul_of_nonneg_right h2 hb0.le
    have e : 1 / (2 * b) * b ^ h * b = b ^ h / 2 := by
      rw [show 1 / (2 * b) * b ^ h = b ^ h / 2 / b by ring]
      exact div_mul_cancel₀ _ hb0.ne'
    exact hm.trans_eq e
  have hreal : (2 : ℝ) ^ (h / K + 2) + h + 1 ≤ ((2 ^ h - 1 : ℕ) : ℝ) ^ ε := by
    refine le_trans ?_ hlow
    rw [le_div_iff₀ hb0]
    have e4 : (2 : ℝ) ^ (h / K + 2) = 4 * 2 ^ (h / K) := by ring
    rw [e4]
    have hX : (2 : ℝ) ^ (h / K) * b ≤ a ^ h * b := mul_le_mul_of_nonneg_right hpowK hb0.le
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast h3
    have hH : ((h : ℝ) + 1) * b ≤ 2 * (h : ℝ) * b :=
      mul_le_mul_of_nonneg_right (by linarith) hb0.le
    have expand : (4 * (2 : ℝ) ^ (h / K) + h + 1) * b =
        4 * ((2 : ℝ) ^ (h / K) * b) + ((h : ℝ) + 1) * b := by ring
    rw [expand]
    linarith
  apply Nat.le_floor
  exact_mod_cast hreal

/-! ## 上界: 十分大きい `h` での有限の形 -/

/-- **`K ≥ 2` の場合.** `ε > 0`、`2 ≤ K`、`Kε > 1` なら十分大きい `h` で `T(h, ⌊n^ε⌋) + 3 ≤ 2K·2^h`。 -/
theorem Ttree_rpow_upper_K {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : 2 ≤ K) (hKε : 1 < K * ε) :
    ∀ᶠ h in atTop, Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ + 3 ≤ 2 * K * 2 ^ h := by
  filter_upwards [eventually_step_cap hε (by omega) hKε, eventually_ge_atTop 3] with h hc hh
  exact Ttree_le_step hK hh hc

/-- **`ε ≥ 1` の場合.** `p = ⌊n^ε⌋ ≥ n` なので、すべての `h ≥ 1` で `T(h, ⌊n^ε⌋) + 3 ≤ 2·2^h`。 -/
theorem Ttree_rpow_upper_one {ε : ℝ} (hε : 1 ≤ ε) :
    ∀ h, 1 ≤ h → Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ + 3 ≤ 2 * 2 ^ h := by
  intro h hh
  apply Ttree_le_full hh
  apply Nat.le_floor
  have h2 : 2 ≤ 2 ^ h := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hn1 : (1 : ℝ) ≤ ((2 ^ h - 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 ^ h - 1 := by omega
    exact_mod_cast this
  calc (((2 ^ h - 1 : ℕ) : ℝ)) = (((2 ^ h - 1 : ℕ) : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (((2 ^ h - 1 : ℕ) : ℝ)) ^ ε := Real.rpow_le_rpow_of_exponent_le hn1 hε

/-- **上界（`ε` の形）.** `ε > 0`、`K ≥ 1`、`Kε > 1` なら十分大きい `h` で
`T(T_h, ⌊n^ε⌋) + 3 ≤ 2K·2^h`。`1/ε ∉ ℤ` は仮定しない。 -/
theorem Ttree_rpow_upper {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : 1 ≤ K) (hKε : 1 < K * ε) :
    ∀ᶠ h in atTop, Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ + 3 ≤ 2 * K * 2 ^ h := by
  rcases Nat.lt_or_ge K 2 with hK2 | hK2
  · have hK1 : K = 1 := by omega
    rw [hK1, Nat.cast_one, one_mul] at hKε
    filter_upwards [eventually_ge_atTop 1] with h hh
    rw [hK1, mul_one]
    exact Ttree_rpow_upper_one hKε.le h hh
  · exact Ttree_rpow_upper_K hε hK2 hKε

/-! ## 極限の道具 -/

/-- `T + 3 ≤ 2K·2^h` が十分先で成り立てば、すべての `δ > 0` で十分先 `T ≤ (2K + δ)·n`（`n = 2^h − 1`）。 -/
theorem le_of_eventually_step (K : ℕ) (T : ℕ → ℕ)
    (hup : ∀ᶠ h in atTop, T h + 3 ≤ 2 * K * 2 ^ h) :
    ∀ δ > 0, ∀ᶠ h in atTop, (T h : ℝ) ≤ (2 * K + δ) * ((2 ^ h - 1 : ℕ) : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (K : ℝ) / δ)
  filter_upwards [hup, eventually_ge_atTop (N + 1)] with h hh hN1
  have hNn : N < 2 ^ h - 1 := by
    have := Nat.lt_two_pow_self (n := h)
    omega
  have hNn' : (N : ℝ) < ((2 ^ h - 1 : ℕ) : ℝ) := by exact_mod_cast hNn
  have hK : 2 * (K : ℝ) < ((2 ^ h - 1 : ℕ) : ℝ) * δ := (div_lt_iff₀ hδ).mp (hN.trans hNn')
  have hT : (T h : ℝ) + 3 ≤ 2 * K * 2 ^ h := by exact_mod_cast hh
  have e : (2 : ℝ) ^ h = ((2 ^ h - 1 : ℕ) : ℝ) + 1 := by rw [cast_two_pow_sub_one]; ring
  rw [e] at hT
  have expand : (2 * (K : ℝ) + δ) * ((2 ^ h - 1 : ℕ) : ℝ) =
      2 * K * ((2 ^ h - 1 : ℕ) : ℝ) + ((2 ^ h - 1 : ℕ) : ℝ) * δ := by ring
  have expand2 : 2 * (K : ℝ) * (((2 ^ h - 1 : ℕ) : ℝ) + 1) =
      2 * K * ((2 ^ h - 1 : ℕ) : ℝ) + 2 * K := by ring
  rw [expand]
  rw [expand2] at hT
  linarith

/-- 挟み撃ち: δ の形の両側の評価から `u/n → L`。 -/
theorem tendsto_of_delta_bounds (L : ℝ) (u n : ℕ → ℝ) (hn : ∀ᶠ h in atTop, 0 < n h)
    (hlow : ∀ δ > 0, ∀ᶠ h in atTop, (L - δ) * n h ≤ u h)
    (hup : ∀ δ > 0, ∀ᶠ h in atTop, u h ≤ (L + δ) * n h) :
    Tendsto (fun h => u h / n h) atTop (𝓝 L) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hlow ((L - a) / 2) (by linarith), hn] with h hh hpos
    rw [lt_div_iff₀ hpos]
    calc a * n h < (L - (L - a) / 2) * n h := mul_lt_mul_of_pos_right (by linarith) hpos
      _ ≤ u h := hh
  · filter_upwards [hup ((b - L) / 2) (by linarith), hn] with h hh hpos
    rw [div_lt_iff₀ hpos]
    calc u h ≤ (L + (b - L) / 2) * n h := hh
      _ < b * n h := mul_lt_mul_of_pos_right (by linarith) hpos

/-- `∀ δ > 0` で十分先 `u ≤ L + δ` なら `limsup u ≤ L`（`EReal` の limsup。有界性の仮定は要らない）。 -/
theorem limsup_ereal_le_of_eventually {u : ℕ → ℝ} {L : ℝ}
    (h : ∀ δ > 0, ∀ᶠ n in atTop, u n ≤ L + δ) :
    limsup (fun n => (u n : EReal)) atTop ≤ (L : EReal) := by
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  induction b using EReal.rec with
  | bot => exact absurd hb (not_lt.mpr bot_le)
  | top => exact le_top
  | coe x =>
    have hx : L < x := EReal.coe_lt_coe_iff.mp hb
    refine limsup_le_of_le (h := ?_)
    filter_upwards [h (x - L) (by linarith)] with n hn
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- `0 < ε`、`1/ε ∉ ℤ` なら `K = ⌈1/ε⌉` は `K ≥ 1` かつ `Kε > 1`。 -/
theorem ceil_inv_spec {ε : ℝ} (hε : 0 < ε) (hnot : ∀ k : ℕ, (k : ℝ) ≠ 1 / ε) :
    1 ≤ ⌈1 / ε⌉₊ ∧ 1 < (⌈1 / ε⌉₊ : ℝ) * ε := by
  have hinv : 0 < 1 / ε := by positivity
  have hKgt : 1 / ε < (⌈1 / ε⌉₊ : ℝ) :=
    lt_of_le_of_ne (Nat.le_ceil _) (fun h => hnot _ h.symm)
  refine ⟨?_, ?_⟩
  · have h0 : (0 : ℝ) < ⌈1 / ε⌉₊ := hinv.trans hKgt
    have : 0 < ⌈1 / ε⌉₊ := by exact_mod_cast h0
    omega
  · calc (1 : ℝ) = 1 / ε * ε := (div_mul_cancel₀ 1 hε.ne').symm
      _ < (⌈1 / ε⌉₊ : ℝ) * ε := mul_lt_mul_of_pos_right hKgt hε

/-! ## 上界の極限 -/

/-- **上界の極限（一般の `K`）.** `ε > 0`、`K ≥ 1`、`Kε > 1` なら `limsup_{h→∞} T(T_h, ⌊n^ε⌋)/n ≤ 2K`。
`1/ε ∉ ℤ` は仮定しない（`1/ε = m ∈ ℤ` なら `K = m + 1` で `2(m+1)`）。 -/
theorem Ttree_rpow_limsup_K {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : 1 ≤ K) (hKε : 1 < K * ε) :
    limsup (fun h : ℕ => (((Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ) /
      ((2 ^ h - 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop ≤ ((2 * (K : ℝ) : ℝ) : EReal) := by
  apply limsup_ereal_le_of_eventually
  intro δ hδ
  filter_upwards [le_of_eventually_step K (fun h => Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊)
    (Ttree_rpow_upper hε hK hKε) δ hδ, eventually_npos] with h hh hpos
  rw [div_le_iff₀ hpos]
  exact hh

/-- **上界の極限.** `ε > 0`、`1/ε ∉ ℤ` なら `limsup_{h→∞} T(T_h, ⌊n^ε⌋)/n ≤ 2⌈1/ε⌉`。 -/
theorem Ttree_rpow_limsup {ε : ℝ} (hε : 0 < ε) (hnot : ∀ k : ℕ, (k : ℝ) ≠ 1 / ε) :
    limsup (fun h : ℕ => (((Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ) /
      ((2 ^ h - 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop ≤ ((2 * (⌈1 / ε⌉₊ : ℝ) : ℝ) : EReal) := by
  obtain ⟨hK1, hKε⟩ := ceil_inv_spec hε hnot
  exact Ttree_rpow_limsup_K hε hK1 hKε

/-! ## 両側の極限 -/

/-- **手数の階段（極限）.** `ε > 0`、`1/ε ∉ ℤ`、`n = 2^h − 1`、`p = ⌊n^ε⌋` なら
`T(T_h, p)/n → 2⌈1/ε⌉`（`h → ∞`）。下側は `Ttree_rpow`（`WindowLowerLimit.lean`）、上側は `Ttree_rpow_upper`。 -/
theorem Ttree_rpow_tendsto {ε : ℝ} (hε : 0 < ε) (hnot : ∀ k : ℕ, (k : ℝ) ≠ 1 / ε) :
    Tendsto (fun h : ℕ => (Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ))
      atTop (𝓝 (2 * (⌈1 / ε⌉₊ : ℝ))) := by
  obtain ⟨hK1, hKε⟩ := ceil_inv_spec hε hnot
  exact tendsto_of_delta_bounds (2 * (⌈1 / ε⌉₊ : ℝ))
    (fun h => (Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ)) (fun h => ((2 ^ h - 1 : ℕ) : ℝ))
    eventually_npos (Ttree_rpow hε)
    (le_of_eventually_step _ (fun h => Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊)
      (Ttree_rpow_upper hε hK1 hKε))

/-- **`ε ≥ 1`（整数の境界 `ε = 1` を含む）.** `T(T_h, ⌊n^ε⌋)/n → 2`（`= 2⌈1/ε⌉`）。
上側は全頂点の構成（`Ttree_rpow_upper_one`）なので `1/ε ∉ ℤ` は要らない。 -/
theorem Ttree_rpow_tendsto_one_le {ε : ℝ} (hε : 1 ≤ ε) :
    Tendsto (fun h : ℕ => (Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ))
      atTop (𝓝 2) := by
  have hε0 : 0 < ε := by linarith
  have hc : ⌈1 / ε⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff one_ne_zero]
    constructor
    · simp only [Nat.sub_self, Nat.cast_zero]
      exact one_div_pos.mpr hε0
    · rw [Nat.cast_one, div_le_one hε0]
      exact hε
  have hlow := Ttree_rpow hε0
  rw [hc, Nat.cast_one, mul_one] at hlow
  have hup : ∀ᶠ h in atTop, Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ + 3 ≤ 2 * 1 * 2 ^ h := by
    filter_upwards [eventually_ge_atTop 1] with h hh
    rw [mul_one]
    exact Ttree_rpow_upper_one hε h hh
  refine tendsto_of_delta_bounds 2
    (fun h => (Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ)) (fun h => ((2 ^ h - 1 : ℕ) : ℝ))
    eventually_npos hlow (fun δ hδ => ?_)
  filter_upwards [le_of_eventually_step 1 (fun h => Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊)
    hup δ hδ] with h hh
  have e : (2 * ((1 : ℕ) : ℝ) + δ) = 2 + δ := by norm_num
  rw [e] at hh
  exact hh

/-! ## 境界 `ε = 1/m`（`1/ε ∈ ℤ`） -/

/-- **境界の挟み.** `m ≥ 1`、`ε = 1/m` なら `2m ≤ liminf T/n` かつ `limsup T/n ≤ 2(m+1)`。
極限が `2m` か（`1/ε ∉ ℤ` の式の延長）はここでは決めない。 -/
theorem Ttree_rpow_inv_nat {m : ℕ} (hm : 1 ≤ m) :
    ((2 * (m : ℝ) : ℝ) : EReal) ≤
      liminf (fun h : ℕ => (((Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ (1 / (m : ℝ))⌋₊ : ℝ) /
        ((2 ^ h - 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop ∧
    limsup (fun h : ℕ => (((Ttree h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ (1 / (m : ℝ))⌋₊ : ℝ) /
        ((2 ^ h - 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop ≤ ((2 * ((m : ℝ) + 1) : ℝ) : EReal) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hε : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  refine ⟨?_, ?_⟩
  · have h := Ttree_rpow_liminf hε
    have hc : ⌈1 / (1 / (m : ℝ))⌉₊ = m := by rw [one_div_one_div, Nat.ceil_natCast]
    rw [hc] at h
    exact h
  · have hKε : 1 < ((m + 1 : ℕ) : ℝ) * (1 / (m : ℝ)) := by
      have hinv : 1 / (m : ℝ) * m = 1 := div_mul_cancel₀ 1 hm0.ne'
      have e : ((m + 1 : ℕ) : ℝ) * (1 / (m : ℝ)) = 1 / (m : ℝ) * m + 1 / (m : ℝ) := by
        push_cast; ring
      rw [e, hinv]
      linarith
    have h := Ttree_rpow_limsup_K hε (K := m + 1) (by omega) hKε
    rw [Nat.cast_succ] at h
    exact h

/-! ## KSS の意味論で -/

theorem TtreeK_rpow_tendsto {ε : ℝ} (hε : 0 < ε) (hnot : ∀ k : ℕ, (k : ℝ) ≠ 1 / ε) :
    Tendsto (fun h : ℕ => (TtreeK h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ) / ((2 ^ h - 1 : ℕ) : ℝ))
      atTop (𝓝 (2 * (⌈1 / ε⌉₊ : ℝ))) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_rpow_tendsto hε hnot

theorem TtreeK_rpow_limsup {ε : ℝ} (hε : 0 < ε) (hnot : ∀ k : ℕ, (k : ℝ) ≠ 1 / ε) :
    limsup (fun h : ℕ => (((TtreeK h ⌊(((2 ^ h - 1 : ℕ) : ℝ)) ^ ε⌋₊ : ℝ) /
      ((2 ^ h - 1 : ℕ) : ℝ) : ℝ) : EReal)) atTop ≤ ((2 * (⌈1 / ε⌉₊ : ℝ) : ℝ) : EReal) := by
  simpa only [Ttree_eq_TtreeK] using Ttree_rpow_limsup hε hnot

end SpookyTree
