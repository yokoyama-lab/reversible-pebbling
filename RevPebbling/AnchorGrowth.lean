import RevPebbling.DispersionGrowth

/-!
# From a midpoint anchor to the growth rate (this work)

`DispersionGrowth.growth_ge_of_midv_geometric` turns a geometric **lower**
bound on the midpoints into a lower bound on `c`, using the left half of
the sandwich `2^{S-1} m_S ≤ f_S`.  This file is its mirror on the right
half, `f_S ≤ 2^S M_S`.

The one thing to be careful about is the polynomial factor.  Bounding
`M_S` by `S · m_S` (`Sandwich.rowMax_le_mul_midv`) would leave an `S` in
front of the geometric term, which `GrowthRate.growth_le_of_geometric`
does not accept.  It is not needed: `RowMax.rowMax_succ` says the row
maxima are the *partial sums* of the midpoints, so a geometric bound on
the midpoints sums to a geometric bound on the maxima with only the
constant `B/(B-1)` — no polynomial factor at all (`rowMax_le_geom`).

Consequently `m_S ≤ C·B^S` gives `c ≤ 2B`, exactly dual to the `2B ≤ c`
of the dispersion family.
-/

namespace RevPebbling.AnchorGrowth

open RevPebbling.GrowthRate RevPebbling.RowMax RevPebbling.Sandwich
open RevPebbling.CompositionAnchor RevPebbling.GrowthClosedForm

/-- **THE MAXIMA ARE THE PARTIAL SUMS.**  A geometric bound on the
midpoints therefore gives a geometric bound on the row maxima, with the
constant `B/(B-1)` and no polynomial factor. -/
theorem rowMax_le_geom {C B : ℝ} (hC : 0 < C) (hB : 1 < B)
    (h : ∀ s : ℕ, (midv s : ℝ) ≤ C * B ^ s) :
    ∀ s : ℕ, (rowMax s : ℝ) ≤ C * B ^ (s + 1) / (B - 1)
  | 0 => by
      have h0 := h 0
      have hm0 : midv 0 = 1 := by decide
      have hr0 : rowMax 0 = 1 := by decide
      have hm : (midv 0 : ℝ) = 1 := by rw [hm0]; norm_num
      have hr : ((rowMax 0 : ℕ) : ℝ) = 1 := by rw [hr0]; norm_num
      rw [hr]
      rw [hm] at h0
      simp only [pow_zero, mul_one] at h0
      rw [le_div_iff₀ (by linarith), pow_one]
      nlinarith
  | s + 1 => by
      have ih := rowMax_le_geom hC hB h s
      have hstep : ((rowMax (s + 1) : ℕ) : ℝ)
          = (midv (s + 1) : ℝ) + (rowMax s : ℝ) := by
        rw [rowMax_succ]; push_cast; ring
      have hmid := h (s + 1)
      have hBpos : (0 : ℝ) < B := by linarith
      have hpow : (0 : ℝ) < B ^ (s + 1) := by positivity
      rw [hstep, le_div_iff₀ (by linarith)]
      have hid : C * B ^ (s + 1 + 1) = C * B ^ (s + 1) * B := by
        rw [pow_succ]; ring
      rw [hid]
      have h2 : (rowMax s : ℝ) * (B - 1) ≤ C * B ^ (s + 1) := by
        rw [← le_div_iff₀ (by linarith)]
        exact ih
      nlinarith

/-- **THE BRIDGE: a geometric upper bound on the midpoints is an upper
bound on `c`, with the ratio doubled.**  Dual to
`DispersionGrowth.growth_ge_of_midv_geometric`. -/
theorem growth_le_of_midv_geometric (hsub : Submult fRow) {C B : ℝ}
    (hC : 0 < C) (hB : 1 < B)
    (h : ∀ s : ℕ, (midv s : ℝ) ≤ C * B ^ s) :
    growth hsub pos_fRow ≤ 2 * B := by
  have hBpos : (0 : ℝ) < B := by linarith
  refine growth_le_of_geometric hsub pos_fRow (B := 2 * B)
    (C := C / (B * (B - 1)) + 1) (by positivity) (by positivity) ?_
  intro k
  match k with
  | 0 =>
      have h1 : ((fRow (0 + 1) : ℕ) : ℝ) = 1 := by norm_num [fRow]
      rw [h1, pow_one]
      have hCB : (0 : ℝ) < C / (B * (B - 1)) := by positivity
      nlinarith
  | j + 1 =>
      have hnat := fRow_le_two_pow_mul_rowMax j
      have hcast : ((fRow (j + 2) : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ (j + 2) * (rowMax j : ℝ) := by exact_mod_cast hnat
      have hgeo := rowMax_le_geom hC hB h j
      have hpow2 : (0 : ℝ) < (2 : ℝ) ^ (j + 2) := by positivity
      have hchain : ((fRow (j + 2) : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ (j + 2) * (C * B ^ (j + 1) / (B - 1)) :=
        le_trans hcast (mul_le_mul_of_nonneg_left hgeo (by positivity))
      have hidx : ((fRow (j + 1 + 1) : ℕ) : ℝ) = ((fRow (j + 2) : ℕ) : ℝ) := by
        norm_num
      rw [hidx]
      refine le_trans hchain ?_
      have hid : C / (B * (B - 1)) * (2 * B) ^ (j + 1 + 1)
          = (2 : ℝ) ^ (j + 2) * (C * B ^ (j + 1) / (B - 1)) := by
        rw [mul_pow]
        have hj : (j : ℕ) + 1 + 1 = j + 2 := by omega
        rw [hj, pow_succ B (j + 1)]
        field_simp
        try ring
      have hnn : (0 : ℝ) ≤ (2 * B) ^ (j + 1 + 1) := by positivity
      nlinarith [hid, hnn]


-- ------------------------------------------------------------------
-- From a midpoint anchor to a geometric bound
-- ------------------------------------------------------------------

/-- The largest midpoint below `t`.  This is a *number*, not a
computation: `midv r` is an entry of a row with `2^{r+1}-1` entries, so
for the `t` of a real anchor it cannot be evaluated — and it does not
need to be, since it only ever appears as the constant `C`. -/
def midvMax (t : Nat) : Nat :=
  (List.range t).foldr (fun r acc => max (midv r) acc) 1

theorem one_le_foldr_max : ∀ (l : List Nat), 1 ≤ l.foldr (fun r acc => max (midv r) acc) 1
  | [] => Nat.le_refl _
  | _ :: t => le_trans (one_le_foldr_max t) (le_max_right _ _)

theorem one_le_midvMax (t : Nat) : 1 ≤ midvMax t := one_le_foldr_max _

theorem le_foldr_max {l : List Nat} {r : Nat} (h : r ∈ l) :
    midv r ≤ l.foldr (fun x acc => max (midv x) acc) 1 := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_max_left _ _
      · exact le_trans (ih h') (le_max_right _ _)

theorem midv_le_midvMax {t r : Nat} (h : r < t) : midv r ≤ midvMax t :=
  le_foldr_max (List.mem_range.mpr h)

/-- **AN ANCHOR IS A GEOMETRIC BOUND.**  `m_{s+t} ≤ m_s · v` for every
`s`, together with any `B` whose `t`-th power dominates `v`, bounds every
midpoint by `C · B^s` — with `C` the largest midpoint below `t`.  No
real powers are involved: the `t`-th root is taken by *choosing* `B`. -/
theorem midv_le_geom_of_anchor {t : Nat} (ht : 1 ≤ t) {v : Nat}
    (ha : ∀ s, midv (s + t) ≤ midv s * v) {B : ℝ} (hB : 1 ≤ B)
    (hvB : (v : ℝ) ≤ B ^ t) :
    ∀ s : ℕ, (midv s : ℝ) ≤ (midvMax t : ℝ) * B ^ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rcases Nat.lt_or_ge s t with hlt | hge
    · have h1 : (midv s : ℝ) ≤ (midvMax t : ℝ) := by
        exact_mod_cast midv_le_midvMax hlt
      have h2 : (1 : ℝ) ≤ B ^ s := one_le_pow₀ hB
      have h3 : (0 : ℝ) ≤ (midvMax t : ℝ) := by positivity
      nlinarith
    · obtain ⟨s', rfl⟩ : ∃ s', s = s' + t := ⟨s - t, by omega⟩
      have hih := ih s' (by omega)
      have hcast : (midv (s' + t) : ℝ) ≤ (midv s' : ℝ) * (v : ℝ) := by
        exact_mod_cast ha s'
      have hBpow : (0 : ℝ) ≤ B ^ t := by positivity
      calc (midv (s' + t) : ℝ) ≤ (midv s' : ℝ) * (v : ℝ) := hcast
        _ ≤ ((midvMax t : ℝ) * B ^ s') * B ^ t :=
            mul_le_mul hih hvB (by positivity) (by positivity)
        _ = (midvMax t : ℝ) * B ^ (s' + t) := by rw [pow_add]; ring

/-- **THE ANCHOR, ON THE GROWTH RATE.**  This is the step
`CompositionAnchor` describes in prose ("iterating the chain … gives
`d ≤ (v*)^{1/t}` and `c = 2d ≤ 2·(v*)^{1/t}`") and never formalised. -/
theorem growth_le_of_anchor (hsub : Submult fRow) {t v : Nat} (ht : 1 ≤ t)
    (ha : ∀ s, midv (s + t) ≤ midv s * v) {B : ℝ} (hB : 1 < B)
    (hvB : (v : ℝ) ≤ B ^ t) :
    growth hsub pos_fRow ≤ 2 * B :=
  growth_le_of_midv_geometric hsub
    (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_midvMax t))
    hB (midv_le_geom_of_anchor ht ha (le_of_lt hB) hvB)

end RevPebbling.AnchorGrowth
