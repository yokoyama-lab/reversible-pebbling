/-
# 定理 U（子の数が有界な木の spooky pebbling の普遍上界）と系 U1・U2

紙 `notes/spooky-pebbling/tree-gap/UNIVERSAL_UB_2026-11.md` の 5 節。木・規則・終状態・最小手数は
`RootedTree.lean` のもの（`RootedTree.legal`。LLJ の規則。`ghost` は前提なし）で、
`RootedWindowLower.lean` の下界 `window_lower_bound_eps` と同じ `Valid`／`TP` の上で述べる。
子の数の上限は `chs t v`（`par u = some v` となる `u < n` の集合）の大きさ `≤ d`。

* `uub_run`（紙の (S2) の一般形）: 整数 `K ≥ 2` と閾値 `S_1, …, S_{K−1} ≥ 1` について、
  ペブル上限 `p ≥ ⌊(n−1)/S_{K−1}⌋ + d + Bd d S (K−1)` なら、手数 `T` の妥当な手順で
  `T + 1 ≤ 2Kn`（各頂点を置く回数の和が `Kn` 以下）。
* `theorem_U`（紙の定理 U）: `K ≥ 2`、`d ≥ 1`、`s ≥ 2`、`s^K ≥ n`、`p ≥ P*(n,d,K,s)` なら
  `T(T, p) ≤ 2Kn − 1`。`P*` は紙の式そのもの（`Pstar`）。証明は `P* ≥ PU`（`L` の項を除いた値）を使う。
* `cor_U1`（紙の系 U1）: `0 < ε < 1`、`1/ε ∉ ℤ`、`K = ⌈1/ε⌉`、`d` 固定。ある `n₀` があって、
  `n ≥ n₀` なら子が `d` 以下のすべての木で `T(T, ⌊n^ε⌋) ≤ 2Kn − 1`。
* `cor_U2`（紙の系 U2）: 同じ範囲で `2Kn − 1 − 2(K−1)n^{(K−1)ε} ≤ T ≤ 2Kn − 1`（下界は
  `window_lower_bound_eps`）、`cor_U2_limit`: `|T/n − 2K| ≤ η` が `n ≥ N(η)` のすべての木で一様。
-/
import SpookyPebblingExtra.RootedUniversalUpperBuild

namespace Spooky
namespace RootedTree
namespace UUB

open Finset Classical

variable {t : RootedTree}

/-! ## 有限の形（一般の閾値） -/

/-- **定理 U の有限形（一般の閾値）.** -/
theorem uub_run (ht : t.isTree = true) {d K p : ℕ} (hd : ∀ v, v < t.n → (chs t v).card ≤ d)
    (S : ℕ → ℕ) (hK : 2 ≤ K) (hS : ∀ i, 1 ≤ i → i < K → 1 ≤ S i)
    (hp : (t.n - 1) / S (K - 1) + d + Bd d S (K - 1) ≤ p) :
    ∃ ms : List Move, t.Run p allEmpty ms t.rootPebble ∧ ms.length + 1 ≤ 2 * K * t.n := by
  have hL := lev_all ht hd S (K - 1) (by omega) (fun i hi1 hi2 => hS i hi1 (by omega))
  obtain ⟨ms, h1, h2, h3⟩ := global_run ht hd (hS (K - 1) (by omega) (by omega)) le_rfl
    (Bd_pos d S (K - 1) (by omega)) hL
  have hrun : t.Run p allEmpty ms t.rootPebble := ⟨LOk_ok (LOk_mono hp h1), h3⟩
  refine ⟨ms, hrun, ?_⟩
  have hmv := moves_eq ht (valid_of_run hrun)
  rw [nPlace_toFun] at hmv
  have hK1 : K - 1 + 1 = K := by omega
  rw [hK1] at h2
  have : 2 * np ms ≤ 2 * K * t.n := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 h2
  omega

/-- 同じことを `Valid` と最小手数 `TP` で。 -/
theorem uub_TP (ht : t.isTree = true) {d K p : ℕ} (hd : ∀ v, v < t.n → (chs t v).card ≤ d)
    (S : ℕ → ℕ) (hK : 2 ≤ K) (hS : ∀ i, 1 ≤ i → i < K → 1 ≤ S i)
    (hp : (t.n - 1) / S (K - 1) + d + Bd d S (K - 1) ≤ p) :
    (∃ T ms, t.Valid p T ms ∧ T + 1 ≤ 2 * K * t.n) ∧ (t.PLengths p).Nonempty ∧
      t.TP p + 1 ≤ 2 * K * t.n := by
  obtain ⟨ms, hrun, hlen⟩ := uub_run ht hd S hK hS hp
  refine ⟨⟨ms.length, toFun ms, valid_of_run hrun, hlen⟩, ⟨ms.length, ms, rfl, hrun⟩, ?_⟩
  have := TP_le (t := t) (s := p) ⟨ms, rfl, hrun⟩
  omega

/-! ## 閾値 `S_j = s^j`（紙の 5 節） -/

/-- 構成のペブルの上限（紙の `P*` から `max(L, ·)` の `L` を除いた値）。 -/
def PU (K d s : ℕ) : ℕ := s + d + (K - 2) * (d * s + d - 1) + d * (s - 1)

/-- 紙の `P*(n,d,K,s) = s + d + (K−2)(ds + d − 1) + max(L, d(s−1))`、`L = (d−1)⌊log₂ n⌋ + d + 1`。 -/
def Pstar (n d K s : ℕ) : ℕ :=
  s + d + (K - 2) * (d * s + d - 1) + max ((d - 1) * Nat.log 2 n + d + 1) (d * (s - 1))

theorem PU_le_Pstar (n d K s : ℕ) : PU K d s ≤ Pstar n d K s := by
  unfold PU Pstar
  have := le_max_right ((d - 1) * Nat.log 2 n + d + 1) (d * (s - 1))
  omega

theorem div_geom_le {d s j : ℕ} (hs : 1 ≤ s) :
    (Mg d (s ^ (j + 2)) - 1) / s ^ (j + 1) ≤ d * s - 1 := by
  unfold Mg
  have hnum : 1 + d * (s ^ (j + 2) - 1) - 1 = d * (s ^ (j + 2) - 1) := by omega
  rw [hnum]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0; simp
  · have hpos : 0 < s ^ (j + 1) := pow_pos hs _
    have hA : 1 ≤ s ^ (j + 2) := Nat.one_le_pow _ _ hs
    have hlt : d * (s ^ (j + 2) - 1) / s ^ (j + 1) < d * s := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      have e : d * s * s ^ (j + 1) = d * s ^ (j + 2) := by ring
      rw [e]
      exact Nat.mul_lt_mul_of_pos_left (by omega) hdpos
    omega

theorem Bd_geom {d s : ℕ} (hs : 1 ≤ s) :
    ∀ j, 1 ≤ j → Bd d (fun i => s ^ i) j ≤ 1 + d * (s - 1) + (j - 1) * (d * s + d - 1)
  | 0, h => absurd h (by decide)
  | 1, _ => by simp [Bd, Mg]
  | j + 2, _ => by
      have ih := Bd_geom (d := d) hs (j + 1) (by omega)
      have hdiv := div_geom_le (d := d) (j := j) hs
      show (Mg d (s ^ (j + 2)) - 1) / s ^ (j + 1) + d + Bd d (fun i => s ^ i) (j + 1) ≤ _
      have hds : d = 0 ∨ 1 ≤ d * s := by
        rcases Nat.eq_zero_or_pos d with h | h
        · exact Or.inl h
        · exact Or.inr (Nat.mul_pos h hs)
      have e1 : (j + 2 - 1) * (d * s + d - 1) = (j + 1 - 1) * (d * s + d - 1) + (d * s + d - 1) := by
        rw [show j + 2 - 1 = (j + 1 - 1) + 1 by omega, Nat.add_one_mul]
      rw [e1]
      rcases hds with h | h
      · have h0 : d * s = 0 := by rw [h, Nat.zero_mul]
        omega
      · omega

/-- 閾値 `S_j = s^j`（`s^K ≥ n`）での全体の上限は `PU K d s` 以下。 -/
theorem bound_geom_le {n d K s : ℕ} (hK : 2 ≤ K) (hs : 1 ≤ s) (hsK : n ≤ s ^ K) :
    (n - 1) / s ^ (K - 1) + d + Bd d (fun i => s ^ i) (K - 1) ≤ PU K d s := by
  have htop : (n - 1) / s ^ (K - 1) ≤ s - 1 := by
    have hpos : 0 < s ^ (K - 1) := pow_pos hs _
    have hlt : (n - 1) / s ^ (K - 1) < s := by
      rw [Nat.div_lt_iff_lt_mul hpos]
      have e : s * s ^ (K - 1) = s ^ K := by
        rw [← pow_succ']; congr 1; omega
      rw [e]
      have : 1 ≤ s ^ K := Nat.one_le_pow _ _ hs
      omega
    omega
  have hB := Bd_geom (d := d) hs (K - 1) (by omega)
  have e : K - 1 - 1 = K - 2 := by omega
  rw [e] at hB
  unfold PU
  omega

/-- **定理 U の有限形（`S_j = s^j`）.** ペブル上限 `p ≥ PU K d s`（`s ≥ 1`、`s^K ≥ n`）で `T + 1 ≤ 2Kn`。 -/
theorem theorem_U_PU (ht : t.isTree = true) {d K s p : ℕ} (hd : ∀ v, v < t.n → (chs t v).card ≤ d)
    (hK : 2 ≤ K) (hs : 1 ≤ s) (hsK : t.n ≤ s ^ K) (hp : PU K d s ≤ p) :
    (∃ T ms, t.Valid p T ms ∧ T + 1 ≤ 2 * K * t.n) ∧ (t.PLengths p).Nonempty ∧
      t.TP p + 1 ≤ 2 * K * t.n :=
  uub_TP ht hd (fun i => s ^ i) hK (fun _ _ _ => Nat.one_le_pow _ _ hs)
    (le_trans (bound_geom_le hK hs hsK) hp)

/-- **定理 U（紙の文面）.** 整数 `K ≥ 2`、`d ≥ 1`、`s ≥ 2`、`s^K ≥ n`。子の数が `d` 以下の頂点 `n` の
根つき木 `t` と `p ≥ P*(n,d,K,s)` について `T(t, p) ≤ 2Kn − 1`（妥当な手順があり、その手数が
`2Kn − 1` 以下）。 -/
theorem theorem_U (ht : t.isTree = true) {d K s p : ℕ} (hd : ∀ v, v < t.n → (chs t v).card ≤ d)
    (_hd1 : 1 ≤ d) (hK : 2 ≤ K) (hs : 2 ≤ s) (hsK : t.n ≤ s ^ K) (hp : Pstar t.n d K s ≤ p) :
    (∃ T ms, t.Valid p T ms ∧ T ≤ 2 * K * t.n - 1) ∧ (t.PLengths p).Nonempty ∧
      t.TP p ≤ 2 * K * t.n - 1 := by
  obtain ⟨⟨T, ms, hV, hT⟩, hne, hTP⟩ :=
    theorem_U_PU ht hd hK (by omega) hsK (le_trans (PU_le_Pstar _ _ _ _) hp)
  exact ⟨⟨T, ms, hV, by omega⟩, hne, by omega⟩

/-! ## 系 U1・U2（`p = ⌊n^ε⌋`） -/

section Asymptotic

/-- `PU K d s ≤ (1 + 2d + 2(K−2)d)·s`（`s ≥ 1`）。 -/
theorem PU_le_lin {K d s : ℕ} (hs : 1 ≤ s) : PU K d s ≤ (1 + 2 * d + 2 * (K - 2) * d) * s := by
  unfold PU
  have h1 : d ≤ d * s := Nat.le_mul_of_pos_right d hs
  have h2 : (K - 2) * (d * s + d - 1) ≤ (K - 2) * (2 * (d * s)) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : d * (s - 1) ≤ d * s := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h4 : (1 + 2 * d + 2 * (K - 2) * d) * s = s + 2 * (d * s) + (K - 2) * (2 * (d * s)) := by
    ring
  omega

/-- `1/ε ∉ ℤ` の下での `K = ⌈1/ε⌉` の性質。 -/
theorem K_props {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hint : ∀ k : ℤ, (k : ℝ) ≠ 1 / ε) :
    2 ≤ ⌈1 / ε⌉₊ ∧ 1 / (⌈1 / ε⌉₊ : ℝ) < ε ∧ ((⌈1 / ε⌉₊ : ℝ) - 1) * ε < 1 := by
  set K := ⌈1 / ε⌉₊ with hKdef
  have hinv : 1 < 1 / ε := by rw [lt_div_iff₀ hε0]; linarith
  have hKge : 1 / ε ≤ (K : ℝ) := Nat.le_ceil _
  have hKne : (K : ℝ) ≠ 1 / ε := by
    have := hint (K : ℤ)
    simpa using this
  have hKgt : 1 / ε < (K : ℝ) := lt_of_le_of_ne hKge (Ne.symm hKne)
  have hKlt : (K : ℝ) < 1 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have : (1 : ℝ) < K := lt_trans hinv hKgt
    have : 1 < K := by exact_mod_cast this
    omega
  · have hKpos : (0 : ℝ) < K := lt_trans (by norm_num) (lt_trans hinv hKgt)
    rw [div_lt_iff₀ hKpos]
    rw [div_lt_iff₀ hε0] at hKgt
    linarith
  · have : (K : ℝ) - 1 < 1 / ε := by linarith
    rw [lt_div_iff₀ hε0] at this
    exact this

/-- 実数の補題: `x ≥ A^{1/δ}`（`A ≥ 0`、`δ > 0`、`x ≥ 0`）なら `x^δ ≥ A`。 -/
theorem rpow_ge_of_ge {A x δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) (hx : A ^ (1 / δ) ≤ x) : A ≤ x ^ δ := by
  have h0 : 0 ≤ A ^ (1 / δ) := Real.rpow_nonneg hA _
  have := Real.rpow_le_rpow h0 hx hδ.le
  rw [← Real.rpow_mul hA, one_div_mul_cancel hδ.ne', Real.rpow_one] at this
  exact this

/-- **系 U1.** `0 < ε < 1`、`1/ε ∉ ℤ`、`d` を固定する。ある `n₀` があって、`n ≥ n₀` なら子の数が
`d` 以下のすべての根つき木で `T(t, ⌊n^ε⌋) ≤ 2⌈1/ε⌉n − 1`（妥当な手順がある）。 -/
theorem cor_U1 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hint : ∀ k : ℤ, (k : ℝ) ≠ 1 / ε) (d : ℕ) :
    ∃ n₀ : ℕ, ∀ t : RootedTree, t.isTree = true → (∀ v, v < t.n → (chs t v).card ≤ d) →
      n₀ ≤ t.n → (t.PLengths ⌊(t.n : ℝ) ^ ε⌋₊).Nonempty ∧
        t.TP ⌊(t.n : ℝ) ^ ε⌋₊ ≤ 2 * ⌈1 / ε⌉₊ * t.n - 1 := by
  obtain ⟨hK2, hδ, _⟩ := K_props hε0 hε1 hint
  set K := ⌈1 / ε⌉₊ with hKdef
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  set δ := ε - 1 / (K : ℝ) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  set C : ℕ := 1 + 2 * d + 2 * (K - 2) * d with hC
  refine ⟨⌈((2 * C : ℕ) : ℝ) ^ (1 / δ)⌉₊ + 1, ?_⟩
  intro t ht hd hn
  set n := t.n with hndef
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  set r := (n : ℝ) ^ (1 / (K : ℝ)) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hnR (by positivity)
  set s := ⌈r⌉₊ with hsdef
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by linarith)))
  have hsK : n ≤ s ^ K := by
    have h1 : r ≤ (s : ℝ) := Nat.le_ceil _
    have h2 : r ^ K ≤ (s : ℝ) ^ K := pow_le_pow_left₀ (by linarith) h1 K
    have h3 : r ^ K = (n : ℝ) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hn0, one_div_mul_cancel hKpos.ne', Real.rpow_one]
    rw [h3] at h2
    exact_mod_cast h2
  have hsle : (s : ℝ) ≤ 2 * r := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ r by linarith)
    linarith
  -- n^δ ≥ 2C
  have hnδ : ((2 * C : ℕ) : ℝ) ≤ (n : ℝ) ^ δ := by
    apply rpow_ge_of_ge (by positivity) hδpos
    have := Nat.le_ceil (((2 * C : ℕ) : ℝ) ^ (1 / δ))
    have : (⌈((2 * C : ℕ) : ℝ) ^ (1 / δ)⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : _ ≤ n)
    linarith
  have key : (PU K d s : ℝ) ≤ (n : ℝ) ^ ε := by
    have h1 : (PU K d s : ℝ) ≤ (C : ℝ) * s := by exact_mod_cast PU_le_lin hs1
    have hsplit : (n : ℝ) ^ ε = r * (n : ℝ) ^ δ := by
      rw [hr, ← Real.rpow_add (by linarith)]
      congr 1; rw [hδdef]; ring
    rw [hsplit]
    have hC0 : (0 : ℝ) ≤ C := by positivity
    calc (PU K d s : ℝ) ≤ (C : ℝ) * s := h1
      _ ≤ (C : ℝ) * (2 * r) := mul_le_mul_of_nonneg_left hsle hC0
      _ = ((2 * C : ℕ) : ℝ) * r := by push_cast; ring
      _ ≤ (n : ℝ) ^ δ * r := mul_le_mul_of_nonneg_right hnδ (by linarith)
      _ = r * (n : ℝ) ^ δ := by ring
  have hp : PU K d s ≤ ⌊(n : ℝ) ^ ε⌋₊ := Nat.le_floor key
  obtain ⟨-, hne, hTP⟩ := theorem_U_PU ht hd hK2 hs1 hsK hp
  exact ⟨hne, Nat.le_sub_one_of_lt hTP⟩

/-- **系 U2（両側）.** 同じ範囲で、`n ≥ n₀` の子が `d` 以下のすべての木で
`2Kn ≤ T + 1 + 2(K−1)n^{(K−1)ε}` かつ `T + 1 ≤ 2Kn`（`T = T(t, ⌊n^ε⌋)`、`K = ⌈1/ε⌉`）。 -/
theorem cor_U2 {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hint : ∀ k : ℤ, (k : ℝ) ≠ 1 / ε) (d : ℕ) :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ t : RootedTree, t.isTree = true → (∀ v, v < t.n → (chs t v).card ≤ d) →
      n₀ ≤ t.n →
        2 * (⌈1 / ε⌉₊ : ℝ) * t.n ≤ (t.TP ⌊(t.n : ℝ) ^ ε⌋₊ : ℝ) + 1 +
            2 * ((⌈1 / ε⌉₊ - 1 : ℕ) : ℝ) * (t.n : ℝ) ^ (((⌈1 / ε⌉₊ - 1 : ℕ) : ℝ) * ε) ∧
          t.TP ⌊(t.n : ℝ) ^ ε⌋₊ + 1 ≤ 2 * ⌈1 / ε⌉₊ * t.n := by
  obtain ⟨n₀, hn₀⟩ := cor_U1 hε0 hε1 hint d
  refine ⟨max n₀ 1, le_max_right _ _, ?_⟩
  intro t ht hd hn
  have hn1 : 1 ≤ t.n := le_trans (le_max_right _ _) hn
  obtain ⟨hne, hTP⟩ := hn₀ t ht hd (le_trans (le_max_left _ _) hn)
  set p := ⌊(t.n : ℝ) ^ ε⌋₊ with hpdef
  have hnR : (1 : ℝ) ≤ t.n := by exact_mod_cast hn1
  have hp1 : 1 ≤ p := Nat.le_floor (by
    have := Real.one_le_rpow hnR hε0.le
    exact_mod_cast this)
  have hpn : (p : ℝ) ≤ (t.n : ℝ) ^ ε := Nat.floor_le (by positivity)
  obtain ⟨ms, hlen, hrun⟩ := Nat.sInf_mem hne
  have hV := valid_of_run hrun
  have hlow := (window_lower_bound_eps ht hV hp1 hε0 hpn).2
  have hTPeq : t.TP p = ms.length := hlen.symm
  refine ⟨?_, ?_⟩
  · rw [hTPeq]; exact hlow
  · have h2 : 2 ≤ ⌈1 / ε⌉₊ := (K_props hε0 hε1 hint).1
    have : 0 < 2 * ⌈1 / ε⌉₊ * t.n := Nat.mul_pos (Nat.mul_pos two_pos (by omega)) (by omega)
    omega

/-- **系 U2（極限）.** `T(t, ⌊n^ε⌋)/n → 2⌈1/ε⌉` が、子の数が `d` 以下のすべての根つき木で一様: 任意の
`η > 0` にある `N` があって、`n ≥ N` のそのようなすべての木で `|T/n − 2⌈1/ε⌉| ≤ η`。 -/
theorem cor_U2_limit {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hint : ∀ k : ℤ, (k : ℝ) ≠ 1 / ε) (d : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ t : RootedTree, t.isTree = true → (∀ v, v < t.n → (chs t v).card ≤ d) → N ≤ t.n →
      |(t.TP ⌊(t.n : ℝ) ^ ε⌋₊ : ℝ) / t.n - 2 * (⌈1 / ε⌉₊ : ℝ)| ≤ η := by
  obtain ⟨hK2, -, hγ⟩ := K_props hε0 hε1 hint
  obtain ⟨n₀, hn₀1, hn₀⟩ := cor_U2 hε0 hε1 hint d
  set K := ⌈1 / ε⌉₊ with hKdef
  have hK1 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  set e := ((K : ℝ) - 1) * ε with hedef
  set γ := 1 - e with hγdef
  have hγpos : 0 < γ := by rw [hγdef]; linarith
  have he0 : 0 ≤ e := by
    rw [hedef]
    have : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    nlinarith
  set A := 2 * (K : ℝ) / η with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨max n₀ (⌈A ^ (1 / γ)⌉₊ + 1), ?_⟩
  intro t ht hd hn
  have hn0 : n₀ ≤ t.n := le_trans (le_max_left _ _) hn
  obtain ⟨hlow, hup⟩ := hn₀ t ht hd hn0
  set n := t.n with hndef
  set T := t.TP ⌊(n : ℝ) ^ ε⌋₊ with hTdef
  have hn1 : 1 ≤ n := le_trans hn₀1 hn0
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  rw [hK1] at hlow
  -- m = n^e ≥ 1、n = m · n^γ
  set m := (n : ℝ) ^ e with hm
  have hm1 : 1 ≤ m := Real.one_le_rpow hnR he0
  have hsplit : (n : ℝ) = m * (n : ℝ) ^ γ := by
    rw [hm, ← Real.rpow_add hnpos, hγdef]
    simp
  have hnγ : A ≤ (n : ℝ) ^ γ := by
    apply rpow_ge_of_ge hA0 hγpos
    have := Nat.le_ceil (A ^ (1 / γ))
    have : (⌈A ^ (1 / γ)⌉₊ : ℝ) ≤ n := by
      exact_mod_cast (le_trans (Nat.le_succ _) (le_trans (le_max_right _ _) hn))
    linarith
  -- 2K m ≤ η n
  have hkey : 2 * (K : ℝ) * m ≤ η * n := by
    rw [hsplit]
    have : 2 * (K : ℝ) = η * A := by rw [hA]; field_simp
    rw [this]
    have hm0 : 0 ≤ m := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hnγ (mul_nonneg hη.le hm0)]
  have hupR : (T : ℝ) + 1 ≤ 2 * (K : ℝ) * n := by exact_mod_cast hup
  rw [abs_le]
  constructor
  · -- 下側: T ≥ 2Kn − 1 − 2(K−1)m ≥ 2Kn − 2Km ≥ (2K − η)n
    rw [le_sub_iff_add_le, le_div_iff₀ hnpos]
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hnpos]
    nlinarith

end Asymptotic

end UUB
end RootedTree
end Spooky
