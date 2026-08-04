import RevPebbling.GameCost

/-!
# Knill's observations, in general (this work)

`PebblingTheory` verifies Knill 1995's Observation 2.2 and the corner
recurrence on bounded grids (`F` there is a lookup into a fixed
64 × 24 table, so the statements are bounded by construction).  With
the general row `rowIter` and its prefix sums `Fpre` those become
theorems about every space level:

* `Fpre_linear`     — Obs 2.2(i): while there are at least as many
  pebbles as cells, `F(n,S) = 2n - 1` (the bounded check only covers
  the diagonal `S = n`, so this is strictly stronger);
* `Fpre_antitone_space` — Obs 2.2(ii): `F` is nonincreasing in the
  space;
* `midv_succ_le_two_mul` — the right half of the midpoint sandwich,
  `m_S ≤ 2 m_{S-1}` (the left half is `Sandwich.midv_le_succ`);
* `fRow_corner_recurrence` — the corner recurrence at the reach limit,
  `f_S = 2 f_{S-1} + F(2^{S-2}, S)`.  What forces the split there is not
  finiteness but *length*: the row simply has no other feasible cut.
-/

namespace RevPebbling.KnillObs

open RevPebbling.DifferenceMergeProperty RevPebbling.CountRecursion
open RevPebbling.CompositionAnchor RevPebbling.RowMax RevPebbling.GameCost
open RevPebbling.KnillUnique

/-- Prefix sums respect pointwise domination. -/
theorem sum_take_le_of_dom (a b : List Nat) (hlen : b.length ≤ a.length)
    (hdom : ∀ i (hi : i < b.length),
      a[i]'(Nat.lt_of_lt_of_le hi hlen) ≤ b[i]) :
    ∀ k, k ≤ b.length → (a.take k).sum ≤ (b.take k).sum := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      intro hk
      have hkb : k < b.length := by omega
      have hka : k < a.length := by omega
      rw [take_succ_sum a k hka, take_succ_sum b k hkb]
      have := ih (by omega)
      have := hdom k hkb
      omega

/-- `S ≤ 2^{S-1}`: the reach limit always covers the linear regime. -/
theorem succ_le_two_pow : ∀ n : Nat, n + 2 ≤ 2 ^ (n + 1)
  | 0 => by omega
  | n + 1 => by
      have ih := succ_le_two_pow n
      have h : (2:Nat) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by
        rw [Nat.pow_succ]; omega
      omega

/-- **Obs 2.2(i), fully general.**  With at least as many pebbles as
cells the cost is `2n - 1`: every entry of the row's first `S - 1`
places is `1`. -/
theorem Fpre_linear (s n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ s + 2) :
    Fpre (rowIter s) n = 2 * n - 1 := by
  obtain ⟨hsort, hpos⟩ := rowIter_invariant s
  have hcount := rowIter_count_one s
  have hlen := rowIter_length s
  have hone := two_pow_ge_one s
  have hnlen : n - 1 ≤ (rowIter s).length := by
    rw [hlen]
    have := succ_le_two_pow s
    omega
  -- every entry below index `s + 1` equals 1
  have hall : ∀ i (hi : i < (rowIter s).length), i ≤ s →
      (rowIter s)[i] = 1 := by
    intro i hi hle
    have hup : (rowIter s)[i] ≤ 1 :=
      sorted_getElem_le_of_countLe _ 1 i hsort hi (by omega)
    have hlo : 1 ≤ (rowIter s)[i] := hpos _ (List.getElem_mem hi)
    omega
  -- so the prefix sum is the length of the prefix
  have hsum : ∀ k, k ≤ n - 1 → ((rowIter s).take k).sum = k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro hk
        have hklen : k < (rowIter s).length := by omega
        rw [take_succ_sum _ k hklen, ih (by omega), hall k hklen (by omega)]
  show 1 + 2 * ((rowIter s).take (n - 1)).sum = 2 * n - 1
  rw [hsum (n - 1) (Nat.le_refl _)]
  omega

/-- **Obs 2.2(ii), fully general.**  More pebbles never cost more time.
The row is pointwise nonincreasing in the space level, so its prefix
sums are too — up to the reach limit of the *smaller* space, beyond
which the shorter row says nothing. -/
theorem Fpre_antitone_space (s n : Nat) (hn : n ≤ 2 ^ (s + 1)) :
    Fpre (rowIter (s + 1)) n ≤ Fpre (rowIter s) n := by
  have hlen := rowIter_succ_length_ge s
  have hdom := gen_pointwise_dom s
  have hrow := rowIter_length s
  have hone := two_pow_ge_one s
  have hn' : n - 1 ≤ (rowIter s).length := by omega
  have h := sum_take_le_of_dom (rowIter (s + 1)) (rowIter s) hlen hdom (n - 1) hn'
  show 1 + 2 * _ ≤ 1 + 2 * _
  omega

/-- **The right half of the midpoint sandwich, fully general**: the
midpoint at most doubles (`PebblingTheory.midpoint_monotone_doubling`
checks `m_{S-1} ≤ m_S ≤ 2 m_{S-1}` for `S ≤ 8`; the left half is
`Sandwich.midv_le_succ`).

At `v = 2 m_{S-1}` the lower counting recursion sees the previous row
twice — once at `v` and once at `v/2 = m_{S-1}` — so the new row already
has half its mass there. -/
theorem midv_succ_le_two_mul (s : Nat) : midv (s + 1) ≤ 2 * midv s := by
  have hm := midv_pos s
  have hlow := count_recursion_lower s (2 * midv s) (by omega)
  have hhalf : 2 * midv s / 2 = midv s := by omega
  rw [hhalf] at hlow
  have hbase := countLe_midv s
  have hmono : countLe (rowIter s) (midv s) ≤ countLe (rowIter s) (2 * midv s) :=
    countLe_mono_val _ (by omega)
  have hone := two_pow_ge_one s
  have hpow : (2:Nat) ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ]; omega
  refine midv_le_of_countLe (s + 1) (2 * midv s) (by omega) ?_
  omega

/-- **THE CORNER RECURRENCE, fully general** (the bounded-grid version
is `PebblingTheory.corner_half_split_recurrence`, `2 ≤ p ≤ 7`):

  `f_S = F(2^{S-2}, S) + 2 f_{S-1}`.

What forces the split at the reach limit is not finiteness but
*length*: with `n = 2·|prev| + 2` and both parts bounded by `|prev|`,
the only feasible cut is the midpoint. -/
theorem fRow_corner_recurrence (s : Nat) :
    fRow (s + 3) = Fpre (rowIter (s + 1)) (2 ^ (s + 1)) + 2 * fRow (s + 2) := by
  obtain ⟨hsort, hpos⟩ := rowIter_invariant s
  have hsolve := gen_solvesKnill (rowIter s) hsort hpos
  have hlen := rowIter_length s
  have hone := two_pow_ge_one s
  have hpow : (2:Nat) ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by
    rw [Nat.pow_succ]; omega
  have hpow' : (2:Nat) ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ]; omega
  have hn : 2 ^ (s + 1 + 1) = 2 * (rowIter s).length + 2 := by omega
  obtain ⟨k, l, hkl, hk, hl, heq⟩ :=
    hsolve.attain (2 ^ (s + 1 + 1)) (by omega) (by omega)
  -- length forces `k = l = |prev|`
  have hkeq : k = (rowIter s).length := by omega
  have hleq : l = (rowIter s).length := by omega
  subst hkeq
  subst hleq
  have hrow : (gen (rowIter s) (2 * (rowIter s).length)).1 = rowIter (s + 1) := rfl
  rw [hrow] at heq
  have hidx : (rowIter s).length + 1 = 2 ^ (s + 1) := by omega
  rw [hidx] at heq
  rw [Fpre_reach_limit (s + 1)] at heq
  rw [Fpre_reach_limit s] at heq
  -- `fRow (s+1+2)` and `fRow (s+3)` are the same term, but not the same
  -- syntax, and `omega` compares atoms syntactically
  rw [show fRow (s + 1 + 2) = fRow (s + 3) from rfl] at heq
  omega

end RevPebbling.KnillObs
