import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The geometric grid of the composition anchor (this work)

The anchor DP does not run over all values `v` — it runs over a
**geometric grid**: the integers `1, 2, …, 2^{M+1}-1` followed by every
`a * 2^b` with `2^M ≤ a < 2^{M+1}`.  Indexing it is a bijection,

  index `i` ↦ `gval M i`,   value `A * 2^b` ↦ `norm M A b`,

and `norm` **rounds down**, which is the only direction the certificate
can afford: a smaller value can only make the DP's answer smaller, and
the answer is used as a lower bound.

This file supplies the four facts the soundness argument needs:

* `norm_le`         — `gval M (norm M A b) ≤ A * 2^b` (rounding is down);
* `gval_lt_succ`    — consecutive grid points are strictly increasing;
* `gval_mono`       — hence `gval` is monotone;
* `lt_gval_norm_succ` — `norm` is the *largest* index that fits, so
  `gval M r ≤ A * 2^b` forces `r ≤ norm M A b` (`le_norm`).

`gval` and `norm` are the Lean counterparts of `unidx` and `rd_index` in
`scripts/m33_anchor_c.c`; `norm` is stated for a pair `(A, b)` because
that is how the DP meets it — as `a₁ * 2^d - a₂` at exponent `b₂`, which
stays small even when the value it denotes does not.
-/

namespace RevPebbling.AnchorGrid

/-- The grid point at index `i`. -/
def gval (M i : Nat) : Nat :=
  let t := i + 1
  if t < 2 ^ (M + 1) then t
  else
    let b := t / 2 ^ M - 1
    (t - b * 2 ^ M) * 2 ^ b

/-- The largest grid index whose value is at most `A * 2^b`. -/
def norm (M A b : Nat) : Nat :=
  if Nat.log2 A + 1 ≤ M + 1 then
    if M + 1 - (Nat.log2 A + 1) ≤ b then
      (b - (M + 1 - (Nat.log2 A + 1))) * 2 ^ M
        + A * 2 ^ (M + 1 - (Nat.log2 A + 1)) - 1
    else A * 2 ^ b - 1
  else
    (b + (Nat.log2 A + 1 - (M + 1))) * 2 ^ M
      + A / 2 ^ (Nat.log2 A + 1 - (M + 1)) - 1

/-- Rounding a plain value down to the grid. -/
def gidx (M v : Nat) : Nat := norm M v 0

-- ------------------------------------------------------------------
-- Reading `gval` off a normalised pair
-- ------------------------------------------------------------------

theorem two_pow_succ (M : Nat) : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by
  rw [Nat.pow_succ]; omega

/-- **THE GRID POINT OF A NORMALISED PAIR.** -/
theorem gval_pair (M a b : Nat) (h1 : 2 ^ M ≤ a) (h2 : a < 2 ^ (M + 1)) :
    gval M (b * 2 ^ M + a - 1) = a * 2 ^ b := by
  have hM : 0 < 2 ^ M := Nat.two_pow_pos _
  have hsucc := two_pow_succ M
  have ht : b * 2 ^ M + a - 1 + 1 = b * 2 ^ M + a := by omega
  unfold gval
  simp only [ht]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp only [Nat.zero_mul, Nat.zero_add]
    rw [if_pos h2, Nat.pow_zero, Nat.mul_one]
  · have hge : ¬ (b * 2 ^ M + a < 2 ^ (M + 1)) := by
      have : 2 ^ M ≤ b * 2 ^ M := Nat.le_mul_of_pos_left _ hb
      omega
    rw [if_neg hge]
    have ha1 : a / 2 ^ M = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have hdiv : (b * 2 ^ M + a) / 2 ^ M = b + 1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, ha1]
      omega
    rw [hdiv]
    simp only [Nat.add_sub_cancel]
    congr 1
    omega

/-- Below `2^{M+1}` the grid is just the integers. -/
theorem gval_small (M V : Nat) (h1 : 1 ≤ V) (h2 : V < 2 ^ (M + 1)) :
    gval M (V - 1) = V := by
  unfold gval
  have ht : V - 1 + 1 = V := by omega
  simp only [ht, if_pos h2]

-- ------------------------------------------------------------------
-- Rounding is downward
-- ------------------------------------------------------------------

theorem log2_bounds {A : Nat} (hA : 1 ≤ A) :
    2 ^ Nat.log2 A ≤ A ∧ A < 2 ^ (Nat.log2 A + 1) :=
  ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

/-- **ROUNDING IS DOWNWARD.**  The three branches are: an exact
normalised pair, an exact small integer, and a genuine round-down. -/
theorem norm_le (M A b : Nat) (hA : 1 ≤ A) :
    gval M (norm M A b) ≤ A * 2 ^ b := by
  obtain ⟨hlo, hhi⟩ := log2_bounds hA
  unfold norm
  set L := Nat.log2 A + 1 with hL
  by_cases hcase : L ≤ M + 1
  · rw [if_pos hcase]
    set sh := M + 1 - L with hsh
    by_cases hb : sh ≤ b
    · rw [if_pos hb]
      have h1 : 2 ^ M ≤ A * 2 ^ sh := by
        calc 2 ^ M = 2 ^ (L - 1) * 2 ^ sh := by rw [← Nat.pow_add]; congr 1; omega
          _ ≤ A * 2 ^ sh := Nat.mul_le_mul_right _ (by
              have : L - 1 = Nat.log2 A := by omega
              rw [this]; exact hlo)
      have h2 : A * 2 ^ sh < 2 ^ (M + 1) := by
        calc A * 2 ^ sh < 2 ^ L * 2 ^ sh := by
              exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hhi
          _ = 2 ^ (M + 1) := by rw [← Nat.pow_add]; congr 1; omega
      rw [gval_pair M _ _ h1 h2, Nat.mul_assoc, ← Nat.pow_add]
      have : sh + (b - sh) = b := by omega
      rw [this]
    · rw [if_neg hb]
      have h2 : A * 2 ^ b < 2 ^ (M + 1) := by
        calc A * 2 ^ b < 2 ^ L * 2 ^ b := by
              exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hhi
          _ ≤ 2 ^ (M + 1) := by
              rw [← Nat.pow_add]
              exact Nat.pow_le_pow_right (by omega) (by omega)
      have h1 : 1 ≤ A * 2 ^ b :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [gval_small M _ h1 h2]
  · rw [if_neg hcase]
    set sh := L - (M + 1) with hsh
    have hshpos : 1 ≤ sh := by omega
    have hpos : 0 < 2 ^ sh := Nat.two_pow_pos _
    have h1 : 2 ^ M ≤ A / 2 ^ sh := by
      rw [Nat.le_div_iff_mul_le hpos, ← Nat.pow_add]
      calc 2 ^ (M + sh) = 2 ^ (L - 1) := by congr 1; omega
        _ ≤ A := by
            have : L - 1 = Nat.log2 A := by omega
            rw [this]; exact hlo
    have h2 : A / 2 ^ sh < 2 ^ (M + 1) := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add]
      calc A < 2 ^ L := hhi
        _ = 2 ^ (M + 1 + sh) := by congr 1; omega
    rw [gval_pair M _ _ h1 h2]
    calc A / 2 ^ sh * 2 ^ (b + sh) = A / 2 ^ sh * 2 ^ sh * 2 ^ b := by
          rw [Nat.pow_add]; ring
      _ ≤ A * 2 ^ b := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)


-- ------------------------------------------------------------------
-- `norm` is the largest index that fits
-- ------------------------------------------------------------------

theorem gval_lt (M i : Nat) (h : i + 1 < 2 ^ (M + 1)) : gval M i = i + 1 := by
  unfold gval; rw [if_pos h]

/-- Above the initial run every index is a normalised pair. -/
theorem gval_eq_pair (M i : Nat) (h : 2 ^ (M + 1) ≤ i + 1) :
    ∃ a b, 2 ^ M ≤ a ∧ a < 2 ^ (M + 1) ∧ i = b * 2 ^ M + a - 1 ∧ 1 ≤ b := by
  have hM : 0 < 2 ^ M := Nat.two_pow_pos _
  have hsucc := two_pow_succ M
  -- name every product so that `omega` only ever sees linear atoms
  have hd : 2 ^ M * ((i + 1) / 2 ^ M) + (i + 1) % 2 ^ M = i + 1 :=
    Nat.div_add_mod (i + 1) (2 ^ M)
  have hrlt : (i + 1) % 2 ^ M < 2 ^ M := Nat.mod_lt _ hM
  have hq2 : 2 ≤ (i + 1) / 2 ^ M := by
    rw [Nat.le_div_iff_mul_le hM]; omega
  have hshift : ((i + 1) / 2 ^ M - 1) * 2 ^ M
      = 2 ^ M * ((i + 1) / 2 ^ M) - 2 ^ M := by
    rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
  exact ⟨(i + 1) % 2 ^ M + 2 ^ M, (i + 1) / 2 ^ M - 1,
    by omega, by omega, by omega, by omega⟩

/-- **THE GRID IS STRICTLY INCREASING.** -/
theorem gval_lt_succ (M i : Nat) : gval M i < gval M (i + 1) := by
  have hM : 0 < 2 ^ M := Nat.two_pow_pos _
  have hsucc := two_pow_succ M
  by_cases h2 : i + 2 < 2 ^ (M + 1)
  · rw [gval_lt M i (by omega), gval_lt M (i + 1) (by omega)]; omega
  · by_cases h1 : i + 1 < 2 ^ (M + 1)
    · -- the boundary: `i + 2 = 2^(M+1)`
      have he : i + 2 = 2 ^ (M + 1) := by omega
      rw [gval_lt M i (by omega)]
      have : i + 1 = 1 * 2 ^ M + 2 ^ M - 1 := by omega
      rw [this, gval_pair M (2 ^ M) 1 (Nat.le_refl _) (by omega)]
      have : 2 ^ M * 2 ^ 1 = 2 ^ (M + 1) := by rw [← Nat.pow_add]
      omega
    · obtain ⟨a, b, ha1, ha2, hi, hb⟩ := gval_eq_pair M i (by omega)
      have hgi : gval M i = a * 2 ^ b := by rw [hi]; exact gval_pair M a b ha1 ha2
      by_cases hac : a + 1 < 2 ^ (M + 1)
      · have hi' : i + 1 = b * 2 ^ M + (a + 1) - 1 := by omega
        rw [hgi, hi', gval_pair M (a + 1) b (by omega) hac]
        have := Nat.two_pow_pos b
        calc a * 2 ^ b < (a + 1) * 2 ^ b := by
              exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr (by omega)
          _ = (a + 1) * 2 ^ b := rfl
      · have hae : a + 1 = 2 ^ (M + 1) := by omega
        have hi' : i + 1 = (b + 1) * 2 ^ M + 2 ^ M - 1 := by
          have : (b + 1) * 2 ^ M = b * 2 ^ M + 2 ^ M := by rw [Nat.succ_mul]
          omega
        rw [hgi, hi', gval_pair M (2 ^ M) (b + 1) (Nat.le_refl _) (by omega)]
        have hpow : 2 ^ M * 2 ^ (b + 1) = 2 ^ (M + 1) * 2 ^ b := by
          rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
        rw [hpow]
        exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr (by omega)

theorem gval_mono (M : Nat) {i j : Nat} (h : i ≤ j) : gval M i ≤ gval M j := by
  induction j with
  | zero => have : i = 0 := by omega
            rw [this]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega)) (Nat.le_of_lt (gval_lt_succ M j))

theorem gval_lt_of_lt (M : Nat) {i j : Nat} (h : i < j) : gval M i < gval M j :=
  Nat.lt_of_lt_of_le (gval_lt_succ M i) (gval_mono M (by omega))


/-- **`norm` IS THE LARGEST INDEX THAT FITS.**  The next grid point is
already too big. -/
theorem lt_gval_norm_succ (M A b : Nat) (hA : 1 ≤ A) :
    A * 2 ^ b < gval M (norm M A b + 1) := by
  obtain ⟨hlo, hhi⟩ := log2_bounds hA
  have hM : 0 < 2 ^ M := Nat.two_pow_pos _
  have hsucc := two_pow_succ M
  by_cases hcase : Nat.log2 A + 1 ≤ M + 1
  · -- the two exact branches: the value is hit on the nose
    have hval : gval M (norm M A b) = A * 2 ^ b := by
      unfold norm
      rw [if_pos hcase]
      by_cases hb : M + 1 - (Nat.log2 A + 1) ≤ b
      · rw [if_pos hb]
        set sh := M + 1 - (Nat.log2 A + 1) with hsh
        have h1 : 2 ^ M ≤ A * 2 ^ sh := by
          calc 2 ^ M = 2 ^ (Nat.log2 A) * 2 ^ sh := by
                rw [← Nat.pow_add]; congr 1; omega
            _ ≤ A * 2 ^ sh := Nat.mul_le_mul_right _ hlo
        have h2 : A * 2 ^ sh < 2 ^ (M + 1) := by
          calc A * 2 ^ sh < 2 ^ (Nat.log2 A + 1) * 2 ^ sh :=
                (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hhi
            _ = 2 ^ (M + 1) := by rw [← Nat.pow_add]; congr 1; omega
        rw [gval_pair M _ _ h1 h2, Nat.mul_assoc, ← Nat.pow_add]
        congr 2
        omega
      · rw [if_neg hb]
        have h2 : A * 2 ^ b < 2 ^ (M + 1) := by
          calc A * 2 ^ b < 2 ^ (Nat.log2 A + 1) * 2 ^ b :=
                (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hhi
            _ ≤ 2 ^ (M + 1) := by
                rw [← Nat.pow_add]
                exact Nat.pow_le_pow_right (by omega) (by omega)
        exact gval_small M _ (Nat.one_le_iff_ne_zero.mpr (by positivity)) h2
    calc A * 2 ^ b = gval M (norm M A b) := hval.symm
      _ < gval M (norm M A b + 1) := gval_lt_succ M _
  · -- the rounding branch: the next point is `(a+1) * 2^(b+sh)`
    unfold norm
    rw [if_neg hcase]
    set sh := Nat.log2 A + 1 - (M + 1) with hsh
    have hpos : 0 < 2 ^ sh := Nat.two_pow_pos _
    set a := A / 2 ^ sh with ha
    have h1 : 2 ^ M ≤ a := by
      rw [ha, Nat.le_div_iff_mul_le hpos, ← Nat.pow_add]
      calc 2 ^ (M + sh) = 2 ^ (Nat.log2 A) := by congr 1; omega
        _ ≤ A := hlo
    have h2 : a < 2 ^ (M + 1) := by
      rw [ha, Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add]
      calc A < 2 ^ (Nat.log2 A + 1) := hhi
        _ = 2 ^ (M + 1 + sh) := by congr 1; omega
    -- `A < (a + 1) * 2^sh`
    have hdm : 2 ^ sh * a + A % 2 ^ sh = A := by rw [ha]; exact Nat.div_add_mod A (2 ^ sh)
    have hmod : A % 2 ^ sh < 2 ^ sh := Nat.mod_lt _ hpos
    have hsplit : (a + 1) * 2 ^ sh = 2 ^ sh * a + 2 ^ sh := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    have hAlt : A < (a + 1) * 2 ^ sh := by omega
    -- the successor grid point
    have hnext : (a + 1) * 2 ^ (b + sh) ≤ gval M ((b + sh) * 2 ^ M + a - 1 + 1) := by
      by_cases hac : a + 1 < 2 ^ (M + 1)
      · have hi' : (b + sh) * 2 ^ M + a - 1 + 1 = (b + sh) * 2 ^ M + (a + 1) - 1 := by
          omega
        rw [hi', gval_pair M (a + 1) (b + sh) (by omega) hac]
      · have hae : a + 1 = 2 ^ (M + 1) := by omega
        have hi' : (b + sh) * 2 ^ M + a - 1 + 1
            = (b + sh + 1) * 2 ^ M + 2 ^ M - 1 := by
          have : (b + sh + 1) * 2 ^ M = (b + sh) * 2 ^ M + 2 ^ M := by rw [Nat.succ_mul]
          omega
        rw [hi', gval_pair M (2 ^ M) (b + sh + 1) (Nat.le_refl _) (by omega), hae]
        have : (2:Nat) ^ M * 2 ^ (b + sh + 1) = 2 ^ (M + 1) * 2 ^ (b + sh) := by
          rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
        omega
    refine Nat.lt_of_lt_of_le ?_ hnext
    calc A * 2 ^ b < (a + 1) * 2 ^ sh * 2 ^ b :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hAlt
      _ = (a + 1) * 2 ^ (b + sh) := by rw [Nat.pow_add]; ring

/-- **THE ROUNDING CHARACTERISATION.**  A grid point that fits under
`A * 2^b` has index at most `norm M A b`. -/
theorem le_norm {M A b r : Nat} (hA : 1 ≤ A) (h : gval M r ≤ A * 2 ^ b) :
    r ≤ norm M A b := by
  by_contra hc
  have hle : norm M A b + 1 ≤ r := by omega
  have := gval_mono M hle
  have := lt_gval_norm_succ M A b hA
  omega

/-- Rounding a plain value: `gidx` is the index of the largest grid point
at most `v`. -/
theorem gval_gidx_le (M v : Nat) (hv : 1 ≤ v) : gval M (gidx M v) ≤ v := by
  have := norm_le M v 0 hv
  simpa [gidx] using this

theorem le_gidx {M v r : Nat} (hv : 1 ≤ v) (h : gval M r ≤ v) : r ≤ gidx M v := by
  refine le_norm (b := 0) hv ?_
  simpa using h


-- ------------------------------------------------------------------
-- The index arithmetic the DP actually performs
-- ------------------------------------------------------------------

/-- The `(mantissa, exponent)` pair of a grid index. -/
def gpair (M i : Nat) : Nat × Nat :=
  if i + 1 < 2 ^ (M + 1) then (i + 1, 0)
  else ((i + 1) - ((i + 1) / 2 ^ M - 1) * 2 ^ M, (i + 1) / 2 ^ M - 1)

theorem gval_gpair (M i : Nat) : gval M i = (gpair M i).1 * 2 ^ (gpair M i).2 := by
  unfold gval gpair
  by_cases h : i + 1 < 2 ^ (M + 1) <;> simp [h]

theorem gpair_pos (M i : Nat) : 1 ≤ (gpair M i).1 := by
  have hM : 0 < 2 ^ M := Nat.two_pow_pos _
  unfold gpair
  by_cases h : i + 1 < 2 ^ (M + 1)
  · simp [h]
  · simp only [h, if_false]
    have hd : 2 ^ M * ((i + 1) / 2 ^ M) + (i + 1) % 2 ^ M = i + 1 :=
      Nat.div_add_mod (i + 1) (2 ^ M)
    have hshift : ((i + 1) / 2 ^ M - 1) * 2 ^ M
        = 2 ^ M * ((i + 1) / 2 ^ M) - 2 ^ M := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
    have hq2 : 2 ≤ (i + 1) / 2 ^ M := by
      rw [Nat.le_div_iff_mul_le hM]
      have := two_pow_succ M; omega
    omega

theorem gpair_lt (M i : Nat) : (gpair M i).1 < 2 ^ (M + 1) := by
  have hM : 0 < 2 ^ M := Nat.two_pow_pos _
  have hsucc := two_pow_succ M
  unfold gpair
  by_cases h : i + 1 < 2 ^ (M + 1)
  · simp [h]
  · simp only [h, if_false]
    have hd : 2 ^ M * ((i + 1) / 2 ^ M) + (i + 1) % 2 ^ M = i + 1 :=
      Nat.div_add_mod (i + 1) (2 ^ M)
    have hlt := Nat.mod_lt (i + 1) hM
    have hshift : ((i + 1) / 2 ^ M - 1) * 2 ^ M
        = 2 ^ M * ((i + 1) / 2 ^ M) - 2 ^ M := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
    have hq2 : 2 ≤ (i + 1) / 2 ^ M := by
      rw [Nat.le_div_iff_mul_le hM]; omega
    omega

theorem gpair_normalised (M i : Nat) (h : 1 ≤ (gpair M i).2) :
    2 ^ M ≤ (gpair M i).1 := by
  have hM : 0 < 2 ^ M := Nat.two_pow_pos _
  have hsucc := two_pow_succ M
  unfold gpair at h ⊢
  by_cases hs : i + 1 < 2 ^ (M + 1)
  · simp [hs] at h
  · simp only [hs, if_false] at h ⊢
    have hd : 2 ^ M * ((i + 1) / 2 ^ M) + (i + 1) % 2 ^ M = i + 1 :=
      Nat.div_add_mod (i + 1) (2 ^ M)
    have hlt := Nat.mod_lt (i + 1) hM
    have hshift : ((i + 1) / 2 ^ M - 1) * 2 ^ M
        = 2 ^ M * ((i + 1) / 2 ^ M) - 2 ^ M := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
    have hq2 : 2 ≤ (i + 1) / 2 ^ M := by
      rw [Nat.le_div_iff_mul_le hM]; omega
    omega

/-- A smaller grid point cannot have a larger exponent. -/
theorem gpair_exp_mono (M : Nat) {i j : Nat} (h : j < i) :
    (gpair M j).2 ≤ (gpair M i).2 := by
  by_contra hc
  have hb : 1 ≤ (gpair M j).2 := by omega
  have h1 : 2 ^ M ≤ (gpair M j).1 := gpair_normalised M j hb
  have h2 : (gpair M i).1 < 2 ^ (M + 1) := gpair_lt M i
  have hlt : gval M j < gval M i := gval_lt_of_lt M h
  rw [gval_gpair, gval_gpair] at hlt
  have hstep : (gpair M i).2 + 1 ≤ (gpair M j).2 := by omega
  have : (gpair M i).1 * 2 ^ (gpair M i).2 < 2 ^ M * 2 ^ (gpair M j).2 := by
    calc (gpair M i).1 * 2 ^ (gpair M i).2
        < 2 ^ (M + 1) * 2 ^ (gpair M i).2 :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h2
      _ = 2 ^ M * 2 ^ ((gpair M i).2 + 1) := by
          rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      _ ≤ 2 ^ M * 2 ^ (gpair M j).2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hstep)
  have : 2 ^ M * 2 ^ (gpair M j).2 ≤ (gpair M j).1 * 2 ^ (gpair M j).2 :=
    Nat.mul_le_mul_right _ h1
  omega

/-- **THE INDEX OF `gval i - gval j`, ROUNDED DOWN.**  This is the Lean
counterpart of `rd_index`; unlike the C it needs no shortcut for a large
exponent gap (measured: dropping the shortcut costs nothing). -/
def rdIndex (M i j : Nat) : Nat :=
  norm M ((gpair M i).1 * 2 ^ ((gpair M i).2 - (gpair M j).2) - (gpair M j).1)
    (gpair M j).2

/-- **THE ROUNDING IS SOUND.** -/
theorem gval_rdIndex_le (M : Nat) {i j : Nat} (h : j < i) :
    gval M (rdIndex M i j) ≤ gval M i - gval M j := by
  have hlt : gval M j < gval M i := gval_lt_of_lt M h
  have hb := gpair_exp_mono M h
  set a1 := (gpair M i).1 with ha1
  set b1 := (gpair M i).2 with hb1
  set a2 := (gpair M j).1 with ha2
  set b2 := (gpair M j).2 with hb2
  have hgi : gval M i = a1 * 2 ^ b1 := gval_gpair M i
  have hgj : gval M j = a2 * 2 ^ b2 := gval_gpair M j
  have hpow : 2 ^ b1 = 2 ^ (b1 - b2) * 2 ^ b2 := by
    rw [← Nat.pow_add]; congr 1; omega
  -- the difference, factored at the smaller exponent
  have hfac : gval M i - gval M j = (a1 * 2 ^ (b1 - b2) - a2) * 2 ^ b2 := by
    rw [hgi, hgj, hpow, Nat.sub_mul, Nat.mul_assoc]
  have hApos : 1 ≤ a1 * 2 ^ (b1 - b2) - a2 := by
    by_contra hc
    have : a1 * 2 ^ (b1 - b2) ≤ a2 := by omega
    have : a1 * 2 ^ b1 ≤ a2 * 2 ^ b2 := by
      calc a1 * 2 ^ b1 = a1 * 2 ^ (b1 - b2) * 2 ^ b2 := by rw [hpow, Nat.mul_assoc]
        _ ≤ a2 * 2 ^ b2 := Nat.mul_le_mul_right _ this
    omega
  rw [hfac]
  exact norm_le M _ _ hApos

end RevPebbling.AnchorGrid
