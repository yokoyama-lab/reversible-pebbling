import RevPebbling.HpkResolved
import RevPebbling.AttainSplit
import RevPebbling.ReachLimit
import RevPebbling.GameLinearLower

/-!
# `LowerRowExact` discharged: the game optimum *is* the row (this work)

`AttainSplit.LowerRowExact` was the last hypothesis of link (1).  Unlike
`hpk` it says nothing about plays — it is the outer induction hypothesis
on the number of pebbles,

  `LowerRowExact s : ∀ m ≤ 2^(s+1), gameF m (s+2) = Fpre (rowIter s) m`.

This file proves it for every `s`, by induction on `s`, and with it
`GameGap.GameOptimal` and `GameDecomposition.GameAttain` — the two
hypotheses every growth-rate result of this artifact was measured
against.

## The induction

The `≤` half is unconditional (`GameCost.gameF_le_Fpre`: Knill's
construction).  The `≥` half is `ge_row_of_lower`, a strong induction on
the chain length `m` inside the induction on `s`.  Three cases:

* `m = 1` — both sides are `1`.
* `m ≤ s + 3` — the **linear regime**.  `GameLinearLower.gameF_linear`
  and `KnillObs.Fpre_linear` both give `2m - 1`, so the recursion is not
  needed at all.
* otherwise — take an optimal play and split on its peak.
  * If the peak is at most `s + 2` the play is a witness one level down,
    so `m` is within *that* reach limit and the induction hypothesis on
    `s` applies; `KnillObs.Fpre_antitone_space` closes it.
  * If the peak is `s + 3`, `HpkResolved.gameF_recursion_ge_final`
    applies — with nothing carried, since `hpk` is now a theorem.  The
    two lower terms are rewritten by the induction hypothesis on `s`, the
    upper term by the induction hypothesis on `m`, and
    `KnillUnique.gen_solvesKnill`'s `le` field says the row is at most
    any such split.

The measurement that fixed this shape: at level `s + 3` the peak of an
optimal play is forced to be `s + 3` exactly when `m ≥ s + 3`, i.e. the
non-forced case is precisely the linear regime — checked by exhaustive
search for `s ≤ 2`, and it is what makes the second bullet unnecessary
below `s + 4`.

## Why the two reach bounds are free

Applying the induction hypothesis on `s` to the lower terms needs
`x + 1 ≤ 2^(s+1)` and `m - (x+1) ≤ 2^(s+1)`.  Both come from
`ReachLimit.reachIn_iff` applied to the plays those terms are built from:
`reachIn_lower_suffix` and `reachIn_upper` expose the reaches that
`CutLower` and `CutUpperFix` construct but only use for their cost.
-/

namespace RevPebbling.RowExact

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.GameCost
open RevPebbling.LiftAbove RevPebbling.CutOptimal RevPebbling.CutLower
open RevPebbling.CutFull RevPebbling.CutTime RevPebbling.CutUpperFix
open RevPebbling.UpperPeak RevPebbling.HpkResolved
open RevPebbling.CountRecursion RevPebbling.DifferenceMergeProperty
open RevPebbling.KnillUnique RevPebbling.KnillObs RevPebbling.ReachLimit
open RevPebbling.GameLinearLower RevPebbling.AttainSplit
open RevPebbling.GameDecomposition RevPebbling.GameGap RevPebbling.RowMax
open RevPebbling.GameKnill RevPebbling.CutUpper

-- ------------------------------------------------------------------
-- The reaches hidden inside the two lower terms
-- ------------------------------------------------------------------

/-- **THE LOWER SUFFIX IS A REACH.**  `CutLower.gameF_le_lower_suffix`
builds a play of `x + 1` cells with `S` pebbles and then keeps only its
length; the play itself bounds `x + 1` by the reach limit. -/
theorem reachIn_lower_suffix {n S a x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hfirst : firstOn (execB (emptyBoard n) (s.take a)) = some x)
    (hpk : maxOnes (doneBoard (x + 1)) (keepBelow (x + 1) (s.drop a)) ≤ S) :
    ∃ t, ReachIn (x + 1) S t := by
  set b₀ := execB (emptyBoard n) (s.take a) with hb₀
  set t := keepBelow (x + 1) (s.drop a) with ht
  have hlow : b₀.take (x + 1) = doneBoard (x + 1) :=
    lower_cfg_eq_doneBoard (by omega) hfirst
  have hsuf : legalB b₀ (s.drop a) = true := by
    have h := hleg
    rw [← List.take_append_drop a s, legal_append, Bool.and_eq_true] at h
    exact h.2
  have hlegT : legalB (doneBoard (x + 1)) t = true := by
    have h := legalB_keepBelow (x + 1) (s.drop a) b₀ hsuf
    rwa [hlow] at h
  have hexT : execB (doneBoard (x + 1)) t = emptyBoard (x + 1) := by
    have h := execB_keepBelow (x + 1) (s.drop a) b₀
    rw [hlow] at h
    rw [← h]
    have hfull : execB b₀ (s.drop a) = doneBoard n := by
      rw [hb₀, ← exec_append, List.take_append_drop]
      exact hex
    rw [hfull, doneBoard_take hx]
  have hlegR : legalB (emptyBoard (x + 1)) t.reverse = true := by
    have h := legal_reverse (doneBoard (x + 1)) t hlegT
    rwa [hexT] at h
  have hexR : execB (emptyBoard (x + 1)) t.reverse = doneBoard (x + 1) := by
    have h := exec_reverse_cancel (doneBoard (x + 1)) t
    rwa [hexT] at h
  have hpkR : maxOnes (emptyBoard (x + 1)) t.reverse ≤ S := by
    have h := maxOnes_reverse (doneBoard (x + 1)) t
    rw [hexT] at h
    omega
  refine ⟨t.reverse.length, t.reverse, Nat.le_refl _, ?_, hlegR, hexR, hpkR⟩
  intro i hi
  have hi' : i ∈ t := by simpa using hi
  have := List.of_mem_filter hi'
  simpa using this

/-- **THE UPPER PART IS A REACH.**  Same for the second term: the
restriction above the cut is itself a play, so `n - (x+1)` is within the
reach limit for `S` pebbles. -/
theorem reachIn_upper {n S x : Nat} {s : List Nat}
    (hx : x + 1 < n)
    (hr : ∀ i ∈ s, i < n)
    (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n)
    (hupk : maxOnes (List.replicate (n - (x + 1)) false) (shiftAbove x s) ≤ S) :
    ∃ t, ReachIn (n - (x + 1)) S t := by
  have hdrop : (emptyBoard n).drop (x + 1) = emptyBoard (n - (x + 1)) := by
    show (List.replicate n false).drop (x + 1) = List.replicate (n - (x + 1)) false
    exact drop_replicate n (x + 1) false
  refine ⟨(shiftAbove x s).length, shiftAbove x s, Nat.le_refl _, ?_, ?_, ?_, hupk⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have hif := List.mem_filter.mp hi
    have h1 := hr i hif.1
    have h2 : x < i := by simpa using hif.2
    omega
  · have h := legalB_shiftAbove x s (emptyBoard n) hleg
    rwa [hdrop] at h
  · have h := execB_shiftAbove x s (emptyBoard n)
    rw [hex, hdrop] at h
    rw [← h, doneBoard_drop hx]

-- ------------------------------------------------------------------
-- The base level, S = 2
-- ------------------------------------------------------------------

/-- **THE BASE OF THE INDUCTION.**  Two cells and two pebbles: `f_2 = 3`
by `GameDecomposition.three_le_gameF_two`, and one cell costs one move. -/
theorem lowerRowExact_zero : LowerRowExact 0 := by
  intro m h1 h2
  have hp : (2:Nat) ^ (0 + 1) = 2 := rfl
  rw [hp] at h2
  have hm : m = 1 ∨ m = 2 := by omega
  rcases hm with rfl | rfl
  · rw [gameF_one 2 (by omega), Fpre_one]
  · have hle : gameF 2 2 ≤ Fpre (rowIter 0) 2 := gameF_le_Fpre 0 2 (by omega) (by omega)
    have hge := three_le_gameF_two
    have hf : Fpre (rowIter 0) 2 = 3 := rfl
    show gameF 2 2 = Fpre (rowIter 0) 2
    omega

-- ------------------------------------------------------------------
-- The step: no play beats the row
-- ------------------------------------------------------------------

/-- **THE `≥` HALF, ONE LEVEL UP.**  Given the identification at level
`s + 2`, no play on `m` cells with `s + 3` pebbles is shorter than the
row predicts. -/
theorem ge_row_of_lower {s : Nat} (hs : LowerRowExact s) :
    ∀ m, 1 ≤ m → m ≤ 2 ^ (s + 2) →
      Fpre (rowIter (s + 1)) m ≤ gameF m (s + 3) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro h1 h2
    rcases Nat.lt_or_ge m 2 with hlt2 | hge2
    · -- one cell
      have hm : m = 1 := by omega
      subst hm
      rw [Fpre_one, gameF_one (s + 3) (by omega)]
    rcases Nat.lt_or_ge m (s + 4) with hlin | hbig
    · -- the linear regime: both sides are `2m - 1`
      rw [Fpre_linear (s + 1) m h1 (by omega), gameF_linear h1 (by omega)]
    -- an optimal play exists, since `m` is within the reach limit
    have hne : ∃ t, ReachIn m (s + 3) t := (reachIn_iff m (s + 1) h1).mpr h2
    obtain ⟨p, hlen, hr, hleg, hex, hpk⟩ := reachIn_gameF hne
    by_cases hsmall : maxOnes (emptyBoard m) p ≤ s + 2
    · -- the last pebble was never needed: drop to the level below
      have hr2 : ReachIn m (s + 2) p.length := ⟨p, Nat.le_refl _, hr, hleg, hex, hsmall⟩
      have hmle : m ≤ 2 ^ (s + 1) := (reachIn_iff m s h1).mp ⟨_, hr2⟩
      have heq := hs m h1 hmle
      have hg := gameF_le hr2
      have hmono := Fpre_antitone_space s m hmle
      omega
    · -- the peak is exactly `s + 3`, so the recursion applies
      have hpeak : maxOnes (emptyBoard m) p = (s + 2) + 1 := by omega
      have hrec0 := gameF_recursion_ge_final (S := s + 2) (n := m) (s := p)
        (by omega) (by omega) hr hleg hex hpeak hlen
      -- `s + 2 + 1` and `s + 3` are the same level; say so, or `omega`
      -- will treat the two `gameF` terms as unrelated atoms
      have hrec : gameF (cutFull m (s + 2) p + 1) (s + 3)
          + gameF (cutFull m (s + 2) p + 1) (s + 2)
          + gameF (m - (cutFull m (s + 2) p + 1)) (s + 2)
          ≤ gameF m (s + 3) := hrec0
      have hxlt : cutFull m (s + 2) p + 1 < m := cutFull_lt (by omega) (by omega)
      obtain ⟨a, hafull, ha⟩ := cutFull_attained (exists_full_time hpeak)
      have hpkl := hpk_at_full_cut (x := cutFull m (s + 2) p) (a := a)
        (by omega) (by omega) hr hleg hex (Nat.le_of_eq hpeak) hlen hafull ha
      have hxle : cutFull m (s + 2) p + 1 ≤ 2 ^ (s + 1) :=
        (reachIn_iff _ s (by omega)).mp
          (reachIn_lower_suffix hxlt hleg hex ha hpkl)
      have hkle : m - (cutFull m (s + 2) p + 1) ≤ 2 ^ (s + 1) :=
        (reachIn_iff _ s (by omega)).mp
          (reachIn_upper hxlt hr hleg hex
            (upper_peak_le (Nat.le_of_eq hpeak) hfull_cutFull))
      -- the induction hypotheses
      have e1 : Fpre (rowIter (s + 1)) (cutFull m (s + 2) p + 1)
          ≤ gameF (cutFull m (s + 2) p + 1) (s + 3) :=
        ih _ (by omega) (by omega) (by omega)
      have e2 := hs (cutFull m (s + 2) p + 1) (by omega) hxle
      have e3 := hs (m - (cutFull m (s + 2) p + 1)) (by omega) hkle
      -- the row is at most any feasible split
      obtain ⟨hsort, hpos⟩ := rowIter_invariant s
      have hgen : (gen (rowIter s) (2 * (rowIter s).length)).1 = rowIter (s + 1) := rfl
      have hlenr := rowIter_length s
      have hsplit := (gen_solvesKnill (rowIter s) hsort hpos).le
        (m - (cutFull m (s + 2) p + 1) - 1) (cutFull m (s + 2) p)
        (by omega) (by omega)
      rw [hgen, show m - (cutFull m (s + 2) p + 1) - 1 + cutFull m (s + 2) p + 2 = m
            from by omega,
          show m - (cutFull m (s + 2) p + 1) - 1 + 1
            = m - (cutFull m (s + 2) p + 1) from by omega] at hsplit
      omega

/-- The identification propagates upward. -/
theorem lowerRowExact_succ {s : Nat} (hs : LowerRowExact s) :
    LowerRowExact (s + 1) := by
  intro m h1 h2
  refine Nat.le_antisymm (gameF_le_Fpre (s + 1) m h1 h2) ?_
  exact ge_row_of_lower hs m h1 h2

/-- **`LowerRowExact`, FOR EVERY LEVEL — NOTHING CARRIED.**  The game
optimum is exactly what the generated row computes, on the whole reach
range. -/
theorem lowerRowExact_all : ∀ s, LowerRowExact s
  | 0 => lowerRowExact_zero
  | s + 1 => lowerRowExact_succ (lowerRowExact_all s)

/-- The same, unfolded. -/
theorem gameF_eq_row (s m : Nat) (h1 : 1 ≤ m) (h2 : m ≤ 2 ^ (s + 1)) :
    gameF m (s + 2) = Fpre (rowIter s) m :=
  lowerRowExact_all s m h1 h2

-- ------------------------------------------------------------------
-- The two hypotheses of the artifact, discharged
-- ------------------------------------------------------------------

/-- **`GameOptimal`, PROVED.**  This was the hypothesis every growth-rate
result of this artifact was stated relative to: the cost the structure
theorems compute is the true optimum of the game. -/
theorem gameOptimal_holds : GameOptimal := by
  intro s
  have h := gameF_eq_row s (2 ^ (s + 1)) (two_pow_ge_one (s + 1)) (Nat.le_refl _)
  rw [h, Fpre_reach_limit s]

/-- **`GameAttain`, PROVED.**  With the game optimum identified with the
row, the split the row attains is a split the game attains. -/
theorem gameAttain_holds : GameAttain := by
  intro s n h2 hN
  have hlenr := rowIter_length s
  have hpow := two_pow_ge_one (s + 1)
  obtain ⟨hsort, hpos⟩ := rowIter_invariant s
  have hgen : (gen (rowIter s) (2 * (rowIter s).length)).1 = rowIter (s + 1) := rfl
  obtain ⟨k, l, hkl, hk, hl, hval⟩ :=
    (gen_solvesKnill (rowIter s) hsort hpos).attain n h2 hN
  rw [hgen] at hval
  refine ⟨k, l, hkl, hk, hl, ?_⟩
  rw [gameF_eq_row (s + 1) n (by omega) (by omega),
      gameF_eq_row (s + 1) (l + 1) (by omega) (by omega)]
  exact hval

/-- **THE SPACE-OPTIMAL TIME OF THE GAME IS `f_S`, UNCONDITIONALLY.**
`GameGap.gameF_eq_fRow` said this relative to `GameOptimal`; here it is
as a theorem. -/
theorem gameF_eq_fRow_all (s : Nat) : gameF (2 ^ (s + 1)) (s + 2) = fRow (s + 2) := by
  rw [gameF_eq_row s (2 ^ (s + 1)) (two_pow_ge_one (s + 1)) (Nat.le_refl _)]
  exact Fpre_reach_limit s

/-- The same as a row sum — `GameGap.gameF_eq_row_sum` with its
hypothesis discharged. -/
theorem gameF_eq_row_sum_all (s : Nat) :
    gameF (2 ^ (s + 1)) (s + 2) = 1 + 2 * (rowIter s).sum :=
  gameF_eq_fRow_all s

-- ------------------------------------------------------------------
-- Tests: the identification must reproduce values found independently
-- ------------------------------------------------------------------

/-! The values below were computed by breadth-first search over board
configurations, outside Lean and outside the generator.  They agree with
what `gameF_eq_row` now proves, which is what makes the theorem a
statement about the game rather than about its own definition. -/

example : gameF 4 3 = 9 := by
  have h : gameF 4 3 = Fpre (rowIter 1) 4 := gameF_eq_row 1 4 (by omega) (by omega)
  have v : Fpre (rowIter 1) 4 = 9 := by decide
  omega

example : gameF 8 4 = 25 := by
  have h : gameF 8 4 = Fpre (rowIter 2) 8 := gameF_eq_row 2 8 (by omega) (by omega)
  have v : Fpre (rowIter 2) 8 = 25 := by decide
  omega

example : gameF 16 5 = 71 := by
  have h : gameF 16 5 = Fpre (rowIter 3) 16 := gameF_eq_row 3 16 (by omega) (by omega)
  have v : Fpre (rowIter 3) 16 = 71 := by decide
  omega

/-- Inside the linear regime, where the recursion is not used. -/
example : gameF 5 5 = 9 := by
  have h : gameF 5 5 = Fpre (rowIter 3) 5 := gameF_eq_row 3 5 (by omega) (by omega)
  have v : Fpre (rowIter 3) 5 = 9 := by decide
  omega

/-- Strictly between the linear regime and the reach limit. -/
example : gameF 12 5 = 39 := by
  have h : gameF 12 5 = Fpre (rowIter 3) 12 := gameF_eq_row 3 12 (by omega) (by omega)
  have v : Fpre (rowIter 3) 12 = 39 := by decide
  omega

end RevPebbling.RowExact
