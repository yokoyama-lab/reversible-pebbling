import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Packed round-down values (this work, the composition anchor in Lean)

The composition anchor of `CompositionAnchor` is a DP whose values reach
`2^{T-2}`.  Carrying them as `Nat` would make every cell a bignum
operation; carrying them as a *packed pair* `(exponent, mantissa)` keeps
every cell in machine arithmetic.

  `key = e * 2^32 + m`,  value `kval key = m * 2^e`,  `m < 2^32`.

Unlike the C generator (`scripts/m33_anchor_c.c`, which biases the
exponent so that it may be negative) the exponent here is a `Nat`, so
**every representable value is an exact natural number**.  That is what
lets the DP feed `CompositionAnchor.midpoint_composition`, whose
certificate function is `Nat`-valued.

Two facts are all the arithmetic the soundness argument needs:

* `kval_flAdd_le` — addition **rounds down**: `kval (flAdd x y) ≤
  kval x + kval y`.  It holds for arbitrary keys, with no invariant.
* `kval_mono` — on *normalised* keys (`wf`) the order on keys is the
  order on values, so the DP may compare keys directly.

`wf` is preserved by `flAdd` (`wf_flAdd`), so the DP never leaves the
normalised region.
-/

namespace RevPebbling.AnchorKey

-- A value is packed as `exponent * 2^32 + mantissa`.  (`Nat` is used
-- throughout rather than a type synonym: `omega` does not see through an
-- `abbrev` when it collects hypotheses, so `h : x ≤ y` would be invisible.)

def TWO32 : Nat := 4294967296

theorem two32_eq : TWO32 = 2 ^ 32 := by decide

def kexp (k : Nat) : Nat := k / TWO32

def kmant (k : Nat) : Nat := k % TWO32

/-- The exact natural number a key denotes. -/
def kval (k : Nat) : Nat := kmant k * 2 ^ kexp k

/-- Assemble a key from an exponent and a mantissa. -/
def mkKey (e m : Nat) : Nat := e * TWO32 + m

theorem kexp_mkKey {e m : Nat} (h : m < TWO32) : kexp (mkKey e m) = e := by
  have h' : m < 4294967296 := h
  simp only [kexp, mkKey, TWO32]
  omega

theorem kmant_mkKey {e m : Nat} (h : m < TWO32) : kmant (mkKey e m) = m := by
  have h' : m < 4294967296 := h
  simp only [kmant, mkKey, TWO32]
  omega

theorem kval_mkKey {e m : Nat} (h : m < TWO32) : kval (mkKey e m) = m * 2 ^ e := by
  unfold kval
  rw [kexp_mkKey h, kmant_mkKey h]

theorem kmant_lt (k : Nat) : kmant k < TWO32 := by
  simp only [kmant, TWO32]; omega

theorem kmant_lt' (k : Nat) : kmant k < 4294967296 := kmant_lt k

/-- The packed layout, as plain arithmetic. -/
theorem split_key (k : Nat) : kexp k * 4294967296 + kmant k = k := by
  simp only [kexp, kmant, TWO32]; omega

/-- A key is *normalised* when a nonzero exponent comes with a mantissa
that uses its top bit.  This is what makes the order on keys agree with
the order on values. -/
def wf (k : Nat) : Prop := kexp k = 0 ∨ 2 ^ 31 ≤ kmant k

instance (k : Nat) : Decidable (wf k) := by unfold wf; infer_instance

-- ------------------------------------------------------------------
-- The order on normalised keys is the order on values
-- ------------------------------------------------------------------

/-- **KEY ORDER IS VALUE ORDER** (on normalised keys).  A larger
exponent beats any mantissa, because the mantissa is capped at `2^32`
while a normalised one is at least `2^31`. -/
theorem kval_mono {x y : Nat} (hx : wf x) (hy : wf y) (h : x ≤ y) :
    kval x ≤ kval y := by
  have hdx := split_key x
  have hdy := split_key y
  have hp32 : (2:Nat) ^ 32 = 4294967296 := by norm_num
  have hp31 : (2:Nat) ^ 31 = 2147483648 := by norm_num
  have hmx := kmant_lt' x
  have hmy := kmant_lt' y
  rcases Nat.lt_trichotomy (kexp x) (kexp y) with hlt | heq | hgt
  · -- a bigger exponent wins outright
    have hy1 : 2 ^ 31 ≤ kmant y := by
      rcases hy with h0 | h1
      · omega
      · exact h1
    calc kval x = kmant x * 2 ^ kexp x := rfl
      _ ≤ 2 ^ 32 * 2 ^ kexp x := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (32 + kexp x) := by rw [Nat.pow_add]
      _ ≤ 2 ^ (31 + kexp y) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = 2 ^ 31 * 2 ^ kexp y := by rw [Nat.pow_add]
      _ ≤ kmant y * 2 ^ kexp y := Nat.mul_le_mul_right _ hy1
      _ = kval y := rfl
  · -- same exponent: compare mantissas
    show kmant x * 2 ^ kexp x ≤ kmant y * 2 ^ kexp y
    rw [heq]
    exact Nat.mul_le_mul_right _ (by omega)
  · -- a bigger exponent on the left contradicts `x ≤ y`
    exfalso
    have hle : (kexp y + 1) * 4294967296 ≤ kexp x * 4294967296 :=
      Nat.mul_le_mul_right _ (by omega)
    omega

-- ------------------------------------------------------------------
-- Round-down addition
-- ------------------------------------------------------------------

/-- Addition, rounded **down** to the packed format. -/
def flAdd (x y : Nat) : Nat :=
  let hi := if x < y then y else x
  let lo := if x < y then x else y
  let ex := kexp hi
  let d := ex - kexp lo
  if 32 ≤ d then hi
  else
    let s := kmant hi + kmant lo / 2 ^ d
    if TWO32 ≤ s then mkKey (ex + 1) (s / 2) else mkKey ex s

/-- The carry cannot overflow the mantissa field. -/
theorem flAdd_s_lt (hi lo : Nat) {d : Nat} :
    kmant hi + kmant lo / 2 ^ d < 2 * TWO32 := by
  have h1 := kmant_lt hi
  have h2 : kmant lo / 2 ^ d ≤ kmant lo := Nat.div_le_self _ _
  have h3 := kmant_lt lo
  omega

/-- The one arithmetic fact behind the whole certificate: shifting a
mantissa right and the exponent left never gains value. -/
theorem shift_le {m ex ey d : Nat} (hd : d = ex - ey) :
    m / 2 ^ d * 2 ^ ex ≤ m * 2 ^ ey := by
  rcases Nat.le_total ey ex with h | h
  · have hex : ex = ey + d := by omega
    calc m / 2 ^ d * 2 ^ ex = m / 2 ^ d * 2 ^ d * 2 ^ ey := by
          rw [hex, Nat.pow_add]; ring
      _ ≤ m * 2 ^ ey := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
  · have hd0 : d = 0 := by omega
    rw [hd0, Nat.pow_zero, Nat.div_one]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h)

/-- **ADDITION ROUNDS DOWN.**  No normalisation hypothesis is needed. -/
theorem kval_flAdd_le (x y : Nat) : kval (flAdd x y) ≤ kval x + kval y := by
  unfold flAdd
  by_cases hxy : x < y
  · simp only [hxy, if_true]
    set hi := y
    set lo := x
    by_cases hd : 32 ≤ kexp hi - kexp lo
    · simp only [hd, if_true]; omega
    · simp only [hd, if_false]
      set s := kmant hi + kmant lo / 2 ^ (kexp hi - kexp lo) with hs
      have hstep : s * 2 ^ kexp hi ≤ kval lo + kval hi := by
        have h := shift_le (m := kmant lo) (ex := kexp hi) (ey := kexp lo)
          (d := kexp hi - kexp lo) rfl
        show (kmant hi + kmant lo / 2 ^ (kexp hi - kexp lo)) * 2 ^ kexp hi ≤ _
        rw [Nat.add_mul]
        show _ ≤ kmant lo * 2 ^ kexp lo + kmant hi * 2 ^ kexp hi
        omega
      by_cases hc : TWO32 ≤ s
      · simp only [hc, if_true]
        have hlt : s / 2 < TWO32 := by
          have := flAdd_s_lt hi lo (d := kexp hi - kexp lo)
          omega
        rw [kval_mkKey hlt]
        calc s / 2 * 2 ^ (kexp hi + 1) = s / 2 * 2 * 2 ^ kexp hi := by
              rw [Nat.pow_succ]; ring
          _ ≤ s * 2 ^ kexp hi := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
          _ ≤ kval lo + kval hi := hstep

      · simp only [hc, if_false]
        rw [kval_mkKey (by omega)]
        omega
  · simp only [hxy, if_false]
    set hi := x
    set lo := y
    by_cases hd : 32 ≤ kexp hi - kexp lo
    · simp only [hd, if_true]; omega
    · simp only [hd, if_false]
      set s := kmant hi + kmant lo / 2 ^ (kexp hi - kexp lo) with hs
      have hstep : s * 2 ^ kexp hi ≤ kval hi + kval lo := by
        have h := shift_le (m := kmant lo) (ex := kexp hi) (ey := kexp lo)
          (d := kexp hi - kexp lo) rfl
        show (kmant hi + kmant lo / 2 ^ (kexp hi - kexp lo)) * 2 ^ kexp hi ≤ _
        rw [Nat.add_mul]
        show _ ≤ kmant hi * 2 ^ kexp hi + kmant lo * 2 ^ kexp lo
        omega
      by_cases hc : TWO32 ≤ s
      · simp only [hc, if_true]
        have hlt : s / 2 < TWO32 := by
          have := flAdd_s_lt hi lo (d := kexp hi - kexp lo)
          omega
        rw [kval_mkKey hlt]
        calc s / 2 * 2 ^ (kexp hi + 1) = s / 2 * 2 * 2 ^ kexp hi := by
              rw [Nat.pow_succ]; ring
          _ ≤ s * 2 ^ kexp hi := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
          _ ≤ kval hi + kval lo := hstep
      · simp only [hc, if_false]
        rw [kval_mkKey (by omega)]
        omega

/-- **NORMALISATION IS PRESERVED.**  A nonzero exponent can only appear
with the high mantissa bit set: either it was already there, or it comes
from a carry. -/
theorem wf_flAdd {x y : Nat} (hx : wf x) (hy : wf y) : wf (flAdd x y) := by
  unfold flAdd
  by_cases hxy : x < y <;> simp only [hxy, if_true, if_false]
  · by_cases hd : 32 ≤ kexp y - kexp x
    · simp only [hd, if_true]; exact hy
    · simp only [hd, if_false]
      set s := kmant y + kmant x / 2 ^ (kexp y - kexp x) with hs
      by_cases hc : TWO32 ≤ s
      · simp only [hc, if_true]
        have hlt : s / 2 < TWO32 := by
          have := flAdd_s_lt y x (d := kexp y - kexp x); omega
        right
        rw [kmant_mkKey hlt]
        have h2 : (2:Nat) ^ 31 * 2 ≤ s := by
          have e1 : TWO32 = 4294967296 := rfl
          have e2 : (2:Nat) ^ 31 = 2147483648 := by norm_num
          omega
        exact (Nat.le_div_iff_mul_le (by norm_num)).mpr h2
      · simp only [hc, if_false]
        rcases Nat.eq_zero_or_pos (kexp y) with h0 | hpos
        · left; rw [kexp_mkKey (by omega)]; exact h0
        · right
          rw [kmant_mkKey (by omega)]
          rcases hy with h | h
          · omega
          · exact Nat.le_trans h (Nat.le_add_right _ _)
  · by_cases hd : 32 ≤ kexp x - kexp y
    · simp only [hd, if_true]; exact hx
    · simp only [hd, if_false]
      set s := kmant x + kmant y / 2 ^ (kexp x - kexp y) with hs
      by_cases hc : TWO32 ≤ s
      · simp only [hc, if_true]
        have hlt : s / 2 < TWO32 := by
          have := flAdd_s_lt x y (d := kexp x - kexp y); omega
        right
        rw [kmant_mkKey hlt]
        have h2 : (2:Nat) ^ 31 * 2 ≤ s := by
          have e1 : TWO32 = 4294967296 := rfl
          have e2 : (2:Nat) ^ 31 = 2147483648 := by norm_num
          omega
        exact (Nat.le_div_iff_mul_le (by norm_num)).mpr h2
      · simp only [hc, if_false]
        rcases Nat.eq_zero_or_pos (kexp x) with h0 | hpos
        · left; rw [kexp_mkKey (by omega)]; exact h0
        · right
          rw [kmant_mkKey (by omega)]
          rcases hx with h | h
          · omega
          · exact Nat.le_trans h (Nat.le_add_right _ _)

-- ------------------------------------------------------------------
-- The two constants the DP starts and stops at
-- ------------------------------------------------------------------

/-- The key for `1`. -/
def flOne : Nat := 1

theorem kval_flOne : kval flOne = 1 := by
  show kmant 1 * 2 ^ kexp 1 = 1
  unfold kmant kexp
  norm_num [TWO32]

theorem wf_flOne : wf flOne := by
  left; show (1:Nat) / TWO32 = 0; norm_num [TWO32]

/-- The key for `2^k`. -/
def flPow2 (k : Nat) : Nat :=
  if k ≤ 31 then mkKey 0 (2 ^ k) else mkKey (k - 31) (2 ^ 31)

theorem kval_flPow2 (k : Nat) : kval (flPow2 k) = 2 ^ k := by
  unfold flPow2
  by_cases h : k ≤ 31
  · simp only [h, if_true]
    rw [kval_mkKey (by rw [two32_eq]; exact Nat.pow_lt_pow_right (by omega) (by omega))]
    simp
  · simp only [h, if_false]
    rw [kval_mkKey (by rw [two32_eq]; exact Nat.pow_lt_pow_right (by omega) (by omega)),
      ← Nat.pow_add]
    congr 1
    omega

theorem wf_flPow2 (k : Nat) : wf (flPow2 k) := by
  unfold flPow2
  by_cases h : k ≤ 31
  · simp only [h, if_true]
    left
    exact kexp_mkKey (by rw [two32_eq]; exact Nat.pow_lt_pow_right (by omega) (by omega))
  · simp only [h, if_false]
    right
    rw [kmant_mkKey (by rw [two32_eq]; exact Nat.pow_lt_pow_right (by omega) (by omega))]

end RevPebbling.AnchorKey
