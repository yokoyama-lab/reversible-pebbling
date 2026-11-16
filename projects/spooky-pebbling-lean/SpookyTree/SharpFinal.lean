/-
# 先頭の係数は 2: 最小ペブル数での手数は `(2 + o(1)) · 2^h · h / log₂ h`

* `time_lower_bound_sharp`: 上限 `h + 1` のどの妥当な手順も
  `T + 1 ≥ 2 (2^h − 1) + 2 · 2^h · (h − 3⌈log₂(h+1)⌉ − 1) / (log₂(h+1) + 4)`。
  `Cut.lean` の固定の深さでの切断（係数 1/2）を、ペブルの個数についての帰納法（`SharpCut.lean`）に替えたもの。
* `time_upper_bound_sharp`: `h ≥ 32` で、`lg = ⌊log₂ h⌋`、`ll = ⌊log₂ lg⌋` として
  `lg · (lg − 2 ll) · (T + 3) ≤ 2 (lg · h + 4h + lg²) · 2^h` の妥当な手順がある。
  `time_upper_bound` でブロックの幅を `Λ = lg − 2 ll` に取っただけ（`2^Λ ≤ 4h / lg²` なので浅い部分の寄与が消える）。
* `time_sharp_kss`: KSS の意味論（`ValidK`）について上の 2 つを並べた形。

どちらの式も `2 · 2^h · h / log₂ h` に `1 + O(log log h / log h)` を掛けた形なので、
`T(T_h, h+1) = (2 + o(1)) · 2^h · h / log₂ h = (2 + o(1)) · n log₂ n / log₂ log₂ n`。
-/
import SpookyTree.SharpCut
import SpookyTree.UpperKSS

namespace SpookyTree

/-- **鋭い下界（一般形）.** 手数 + 1 ≥ 2 (2^h − 1) + 2 Fb(h)。 -/
theorem sharp_main {h cap T : ℕ} {ms : ℕ → Move} (hV : Valid h cap T ms) (hh : 1 ≤ h)
    {Λ K Ψ : ℝ} (hΛΨ : Λ = Ψ + 2) (hΨ0 : 0 ≤ Ψ) (hK1 : 1 ≤ K)
    (hΨ : ∀ p : ℕ, 1 ≤ p → p ≤ cap → psi p ≤ Ψ)
    (hK : ∀ j : ℕ, K < (j : ℝ) + 1 → j < h → (cap : ℝ) * j * Λ ≤ 2 ^ j) :
    2 * ((2 : ℝ) ^ h - 1) + 2 * Fb Λ K h ≤ T + 1 := by
  have hroot : ([] : Node).length < h := by simp; omega
  have hfree0 : ∀ z ∈ subtree h [], st ms 0 z ≠ .pebble := by intro z _; simp [st]
  -- 根への置く手がある
  obtain ⟨τ0, -, hτ0T, hτ0v, hτ0p⟩ :=
    lemmaR hV _ [] rfl hroot 0 T (Nat.zero_le _) le_rfl hfree0 hV.root []
      (by simp [mem_subtree]; omega)
  have hpeb : st ms (τ0 + 1) [] = .pebble := by
    have := st_after_place hτ0p; rw [hτ0v] at this; exact this
  -- τ0 以前の置く手は n 個以上
  set E1 := (Finset.range T).filter (fun i => i ≤ τ0 ∧ IsPlace (ms i))
  have hE1 : 2 ^ h - 1 ≤ E1.card := by
    have hsub : subtree h [] ⊆ E1.image (fun i => (ms i).v) := by
      intro z hz
      obtain ⟨i, -, hi2, hi3, hi4⟩ :=
        lemmaR hV _ [] rfl hroot 0 (τ0 + 1) (Nat.zero_le _) (by omega) hfree0 hpeb z hz
      refine Finset.mem_image.mpr ⟨i, ?_, hi3⟩
      simp only [E1, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, hi4⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := E1) (f := fun i => (ms i).v)
    rw [card_subtree] at h1; simp at h1
    omega
  -- τ0 より後: 鋭い切断の補題
  have hE2 := sharpA hV hΛΨ hΨ0 hK1 hΨ hK h τ0 (by rw [hτ0v]; simp) hτ0T hτ0p
  rw [hτ0v] at hE2
  have hdisj : Disjoint E1 (plSet ms T τ0 []) := by
    rw [Finset.disjoint_left]; intro i hi hi'
    simp only [E1, plSet, Finset.mem_filter] at hi hi'; omega
  have hsub : E1 ∪ plSet ms T τ0 [] ⊆ (Finset.range T).filter (fun i => IsPlace (ms i)) := by
    intro i hi
    simp only [E1, plSet, Finset.mem_union, Finset.mem_filter] at hi ⊢
    rcases hi with ⟨a, _, b⟩ | ⟨a, _, b, _⟩ <;> exact ⟨a, b⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hmv := moves_eq hV hh
  unfold nPlace at hmv
  -- 実数で足し合わせる
  have hmvR : (T : ℝ) + 1
      = 2 * (((Finset.range T).filter (fun i => IsPlace (ms i))).card : ℝ) := by
    exact_mod_cast hmv
  have hcardR : (E1.card : ℝ) + ((plSet ms T τ0 []).card : ℝ)
      ≤ (((Finset.range T).filter (fun i => IsPlace (ms i))).card : ℝ) := by
    exact_mod_cast hcard
  have e : ((2 ^ h - 1 : ℕ) : ℝ) = (2 : ℝ) ^ h - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  have hE1R : (2 : ℝ) ^ h - 1 ≤ (E1.card : ℝ) := by
    rw [← e]; exact_mod_cast hE1
  linarith

theorem add_four_le_two_mul_two_pow : ∀ c : ℕ, 2 ≤ c → c + 4 ≤ 2 * 2 ^ c := by
  intro c hc
  induction c, hc using Nat.le_induction with
  | base => norm_num
  | succ c hc ih => rw [pow_succ]; omega

/-- **鋭い下界.** 完全二分木 `T_h` をペブル `h + 1` 個で解く妥当な手順の手数 `T` は
`T + 1 ≥ 2 (2^h − 1) + 2 · 2^h · (h − 3⌈log₂(h+1)⌉ − 1) / (log₂(h+1) + 4)`。先頭の係数は 2。 -/
theorem time_lower_bound_sharp {h T : ℕ} {ms : ℕ → Move} (hV : Valid h (h + 1) T ms)
    (hh : 1 ≤ h) :
    2 * ((2 : ℝ) ^ h - 1)
      + 2 * (2 ^ h * (((h : ℝ) - (3 * (Nat.clog 2 (h + 1) : ℝ) + 1))
          / (Real.logb 2 ((h : ℝ) + 1) + 4))) ≤ T + 1 := by
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.clog 2 (h + 1) := ⟨_, rfl⟩
  rw [← hc]
  have hpow : h + 1 ≤ 2 ^ c := by rw [hc]; exact Nat.le_pow_clog (by norm_num) (h + 1)
  have hhR : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.logb 2 ((h : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have key := sharp_main hV hh (Λ := Real.logb 2 ((h : ℝ) + 1) + 4) (K := 3 * (c : ℝ) + 1)
    (Ψ := Real.logb 2 ((h : ℝ) + 1) + 2) (by ring) (by linarith) (by linarith) ?_ ?_
  · unfold Fb at key
    exact key
  · -- ψ(p) ≤ Ψ
    intro p hp1 hpc
    rw [psi_of_pos hp1]
    have hle : (p : ℝ) ≤ (h : ℝ) + 1 := by exact_mod_cast hpc
    have : Real.logb 2 (p : ℝ) ≤ Real.logb 2 ((h : ℝ) + 1) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hp1) hle
    linarith
  · -- (h + 1) · j · Λ ≤ 2^j（j ≥ 3c + 1）
    intro j hKj hjh
    have h3c : 3 * c + 1 ≤ j := by
      have h' : ((3 * c + 1 : ℕ) : ℝ) < ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
      have := Nat.cast_lt.mp h'
      omega
    have hc2 : 2 ≤ c := by
      by_contra hlt
      have hc1 : c ≤ 1 := by omega
      have : 2 ^ c ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hc1
      omega
    have hc4 := add_four_le_two_mul_two_pow c hc2
    have hjle : j ≤ 2 ^ c := by omega
    have hlogc : Real.logb 2 ((h : ℝ) + 1) ≤ c := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith), Real.rpow_natCast]
      exact_mod_cast hpow
    have h1 : (((h + 1 : ℕ)) : ℝ) ≤ (2 : ℝ) ^ c := by exact_mod_cast hpow
    have h2 : (j : ℝ) ≤ (2 : ℝ) ^ c := by exact_mod_cast hjle
    have h3 : Real.logb 2 ((h : ℝ) + 1) + 4 ≤ 2 * (2 : ℝ) ^ c := by
      have : ((c + 4 : ℕ) : ℝ) ≤ ((2 * 2 ^ c : ℕ) : ℝ) := by exact_mod_cast hc4
      push_cast at this
      linarith
    have h4 : (2 : ℝ) ^ c * (2 : ℝ) ^ c * (2 * (2 : ℝ) ^ c) = (2 : ℝ) ^ (3 * c + 1) := by ring
    have h5 : (2 : ℝ) ^ (3 * c + 1) ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) h3c
    calc (((h + 1 : ℕ)) : ℝ) * j * (Real.logb 2 ((h : ℝ) + 1) + 4)
        ≤ (2 : ℝ) ^ c * (2 : ℝ) ^ c * (2 * (2 : ℝ) ^ c) :=
          mul_le_mul (mul_le_mul h1 h2 (Nat.cast_nonneg j) (by positivity)) h3
            (by linarith) (by positivity)
      _ = (2 : ℝ) ^ (3 * c + 1) := h4
      _ ≤ (2 : ℝ) ^ j := h5

theorem two_mul_add_one_le_two_pow : ∀ n : ℕ, 3 ≤ n → 2 * n + 1 ≤ 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- **鋭い上界.** `h ≥ 32`、`lg = ⌊log₂ h⌋`、`ll = ⌊log₂ lg⌋` として、
`lg · (lg − 2 ll) · (T + 3) ≤ 2 (lg · h + 4h + lg²) · 2^h` を満たす妥当な手順がある。
すなわち `T ≤ 2 · 2^h · h / (lg − 2 ll) · (1 + 4/lg + lg/h)`。先頭の係数は 2。 -/
theorem time_upper_bound_sharp {h : ℕ} (hh : 32 ≤ h) :
    ∃ (T : ℕ) (ms : ℕ → Move), Valid h (h + 1) T ms ∧
      Nat.log 2 h * (Nat.log 2 h - 2 * Nat.log 2 (Nat.log 2 h)) * (T + 3)
        ≤ 2 * (Nat.log 2 h * h + 4 * h + Nat.log 2 h * Nat.log 2 h) * 2 ^ h := by
  obtain ⟨lg, hlg⟩ : ∃ lg, lg = Nat.log 2 h := ⟨_, rfl⟩
  obtain ⟨ll, hll⟩ : ∃ ll, ll = Nat.log 2 lg := ⟨_, rfl⟩
  rw [← hlg, ← hll]
  have hpow_lg : 2 ^ lg ≤ h := by rw [hlg]; exact Nat.pow_log_le_self 2 (by omega)
  have hlg5 : 5 ≤ lg := by
    rw [hlg]; exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
  have hpow_ll : 2 ^ ll ≤ lg := by rw [hll]; exact Nat.pow_log_le_self 2 (by omega)
  have hlt_ll : lg < 2 ^ (ll + 1) := by
    rw [hll]; exact Nat.lt_pow_succ_log_self (by norm_num) lg
  have hll1 : 1 ≤ ll := by
    rw [hll]; exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr (by omega)
  have h2ll : 2 * ll + 1 ≤ lg := by
    rcases Nat.lt_or_ge ll 3 with h3 | h3
    · omega
    · exact le_trans (two_mul_add_one_le_two_pow ll h3) hpow_ll
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, lg = Λ + 2 * ll := ⟨lg - 2 * ll, by omega⟩
  have hΛsub : lg - 2 * ll = Λ := by omega
  rw [hΛsub]
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛle : Λ ≤ lg := by omega
  have hcap : 2 ^ (Λ + 1) ≤ h + 1 := by
    have : 2 ^ (Λ + 1) ≤ 2 ^ lg := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound hΛ1 hcap
  refine ⟨T, ms, hV, ?_⟩
  -- lg² · 2^Λ ≤ 4h
  have hA : lg * lg * 2 ^ Λ ≤ 4 * h := by
    have h1 : 2 ^ Λ * (2 ^ ll * 2 ^ ll) = 2 ^ lg := by
      rw [hΛdef, pow_add, two_mul, pow_add]
    have h2 : 2 ^ (ll + 1) = 2 * 2 ^ ll := by rw [pow_succ]; ring
    have h3 : lg * lg ≤ (2 * 2 ^ ll) * (2 * 2 ^ ll) := Nat.mul_le_mul (by omega) (by omega)
    calc lg * lg * 2 ^ Λ ≤ (2 * 2 ^ ll) * (2 * 2 ^ ll) * 2 ^ Λ := Nat.mul_le_mul_right _ h3
      _ = 4 * (2 ^ Λ * (2 ^ ll * 2 ^ ll)) := by ring
      _ = 4 * 2 ^ lg := by rw [h1]
      _ ≤ 4 * h := by omega
  have hB : Λ * ((h - 1) / Λ) ≤ h := le_trans (Nat.mul_div_le _ _) (Nat.sub_le _ _)
  have e1 : lg * Λ * 2 ^ Λ ≤ 4 * h :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hΛle)) hA
  have e2 : lg * (Λ * ((h - 1) / Λ)) ≤ lg * h := Nat.mul_le_mul_left _ hB
  have e3 : lg * Λ ≤ lg * lg := Nat.mul_le_mul_left _ hΛle
  calc lg * Λ * (T + 3) ≤ lg * Λ * (2 * (2 ^ Λ + (h - 1) / Λ + 1) * 2 ^ h) :=
        Nat.mul_le_mul_left _ hT
    _ = 2 * (lg * Λ * 2 ^ Λ + lg * (Λ * ((h - 1) / Λ)) + lg * Λ) * 2 ^ h := by ring
    _ ≤ 2 * (4 * h + lg * h + lg * lg) * 2 ^ h :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by linarith))
    _ = 2 * (lg * h + 4 * h + lg * lg) * 2 ^ h := by ring

/-- **KSS の意味論での、先頭の係数 2 の上下界.** `h ≥ 32` のとき、ペブル `h + 1` 個の KSS の意味論の手順について:
上界 `lg · (lg − 2 ll) · (T + 3) ≤ 2 (lg · h + 4h + lg²) · 2^h` を満たす手順があり、
どの手順も `T + 1 ≥ 2 (2^h − 1) + 2 · 2^h · (h − 3⌈log₂(h+1)⌉ − 1) / (log₂(h+1) + 4)`。 -/
theorem time_sharp_kss {h : ℕ} (hh : 32 ≤ h) :
    (∃ (T : ℕ) (ms : ℕ → Move), ValidK h (h + 1) T ms ∧
      Nat.log 2 h * (Nat.log 2 h - 2 * Nat.log 2 (Nat.log 2 h)) * (T + 3)
        ≤ 2 * (Nat.log 2 h * h + 4 * h + Nat.log 2 h * Nat.log 2 h) * 2 ^ h) ∧
    (∀ (T : ℕ) (ms : ℕ → Move), ValidK h (h + 1) T ms →
      2 * ((2 : ℝ) ^ h - 1)
        + 2 * (2 ^ h * (((h : ℝ) - (3 * (Nat.clog 2 (h + 1) : ℝ) + 1))
            / (Real.logb 2 ((h : ℝ) + 1) + 4))) ≤ T + 1) := by
  refine ⟨?_, fun T ms hV => time_lower_bound_sharp hV.valid (by omega)⟩
  obtain ⟨T, ms, hV, hT⟩ := time_upper_bound_sharp hh
  exact ⟨T, msK h ms, validK_of_valid hV, hT⟩

end SpookyTree
