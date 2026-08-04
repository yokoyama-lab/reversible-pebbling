import RevPebbling.GameCost
import RevPebbling.CutVocabulary
import RevPebbling.KnillObs

/-!
# The linear lower bound on the game, in general (this work)

`PebblingTheory.knill_floor` checks Knill's Obs 2.2(i) — `F(n,S) = 2n-1`
once `S ≥ n` — on a grid, and `KnillObs.Fpre_linear` generalises it, but
only as a statement about the generated **row**.  This file proves the
corresponding statement about the **game**, and the interesting half of
it holds for *every* space budget:

  `two_mul_sub_one_le_gameF : 1 ≤ n → 2 * n - 1 ≤ gameF n S`

No play, however many pebbles it is given, pebbles a chain of `n` cells
in fewer than `2n - 1` moves.  Together with the achievability half
(`gameF_le_Fpre` and `KnillObs.Fpre_linear`) this pins the linear regime
exactly: `gameF n S = 2n - 1` whenever `n ≤ S` (`gameF_linear`).

## Why it is worth having

Every other lower bound in this artifact is a bound on `fRow`, the row
the generator computes; the game side had **no** unconditional lower
bound at all — that is exactly what `GameGap.GameOptimal` and
`GameDecomposition.GameAttain` are hypotheses about.  This one is
unconditional, so it is the first general statement in the artifact of
the form "no play can do better".

## The argument

Counting, not induction on the recursion.  Write `s.count i` for the
number of times a play toggles cell `i`.

* `nth_execB_parity` — a cell ends pebbled iff it was toggled an odd
  number of times.  So the top cell is toggled at least once and every
  lower cell an even number of times.
* `not_mem_above` — if a cell is never toggled it is always empty, so no
  move on the cell above it is ever legal, so nothing above it is ever
  toggled either.  Since the top cell *is* toggled, every cell is.
* Hence every cell below the top is toggled at least twice (at least
  once, and evenly), and the top at least once: `2(n-1) + 1` moves.

`length_filter_succ` and `two_mul_le_length_filter` do the summation
without any `Finset` machinery — peeling one cell at a time off the
filter is enough.
-/

namespace RevPebbling.GameLinearLower

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.CutVocabulary
open RevPebbling.GameKnill RevPebbling.KnillObs
open RevPebbling.CountRecursion RevPebbling.DifferenceMergeProperty

-- ------------------------------------------------------------------
-- Toggling one cell
-- ------------------------------------------------------------------

theorem nth_toggle_self (b : Board) (i : Nat) (h : i < b.length) :
    nth (toggle b i) i = !(nth b i) :=
  nth_set_eq b i _ h

theorem nth_toggle_ne (b : Board) (i j : Nat) (h : j ≠ i) :
    nth (toggle b j) i = nth b i :=
  nth_set_ne b j i _ h

/-- **A CELL ENDS PEBBLED IFF IT WAS TOGGLED ODDLY OFTEN.** -/
theorem nth_execB_parity : ∀ (s : List Nat) (b : Board) (i : Nat),
    i < b.length →
      nth (execB b s) i
        = (if s.count i % 2 = 1 then !(nth b i) else nth b i)
  | [], b, i, _ => by simp [execB]
  | j :: rest, b, i, hi => by
      have hlen : i < (toggle b j).length := by
        rw [toggle, length_set]; exact hi
      have ih := nth_execB_parity rest (toggle b j) i hlen
      show nth (execB (toggle b j) rest) i = _
      rw [ih]
      by_cases h : j = i
      · subst h
        rw [nth_toggle_self b j hi]
        have hc : (j :: rest).count j = rest.count j + 1 := by
          simp [List.count_cons]
        rw [hc]
        by_cases hp : rest.count j % 2 = 1
        · have h0 : (rest.count j + 1) % 2 = 0 := by omega
          simp [hp, h0]
        · have h1 : (rest.count j + 1) % 2 = 1 := by omega
          simp [hp, h1]
      · rw [nth_toggle_ne b i j h]
        have hc : (j :: rest).count i = rest.count i := by
          simp [List.count_cons, h, Ne.symm h]
        rw [hc]

-- ------------------------------------------------------------------
-- A never-toggled cell blocks everything above it
-- ------------------------------------------------------------------

theorem nth_emptyBoard (n k : Nat) : nth (emptyBoard n) k = false :=
  nth_replicate n k

/-- If cell `i` is never toggled and starts empty, no move on cell
`i + 1` is ever legal. -/
theorem not_mem_succ : ∀ (s : List Nat) (b : Board) (i : Nat),
    legalB b s = true → i ∉ s → nth b i = false → (i + 1) ∉ s
  | [], _, _, _, _, _ => by simp
  | j :: rest, b, i, hleg, hni, hb => by
      simp only [legalB, Bool.and_eq_true] at hleg
      have hji : j ≠ i := fun h => hni (h ▸ List.mem_cons_self ..)
      have hnirest : i ∉ rest := fun h => hni (List.mem_cons_of_mem _ h)
      have hj1 : j ≠ i + 1 := by
        intro h
        subst h
        have hok := hleg.1
        simp [okMove, hb] at hok
      have hb' : nth (toggle b j) i = false := by
        rw [nth_toggle_ne b i j hji]; exact hb
      have hrec := not_mem_succ rest (toggle b j) i hleg.2 hnirest hb'
      intro hc
      rcases List.mem_cons.mp hc with h | h
      · exact hj1 h.symm
      · exact hrec h

/-- Nothing at or above a never-toggled cell is ever toggled. -/
theorem not_mem_above (s : List Nat) (n i : Nat)
    (hleg : legalB (emptyBoard n) s = true) (hni : i ∉ s) :
    ∀ d, (i + d) ∉ s := by
  intro d
  induction d with
  | zero => simpa using hni
  | succ d ih =>
      have heq : i + (d + 1) = (i + d) + 1 := by omega
      rw [heq]
      exact not_mem_succ s (emptyBoard n) (i + d) hleg ih
        (nth_emptyBoard n (i + d))

-- ------------------------------------------------------------------
-- Summing the counts, without `Finset`
-- ------------------------------------------------------------------

theorem length_filter_succ (m : Nat) : ∀ (s : List Nat),
    (s.filter (fun i => decide (i < m + 1))).length
      = (s.filter (fun i => decide (i < m))).length + s.count m := by
  intro s
  induction s with
  | nil => simp
  | cons j rest ih =>
      rw [List.filter_cons, List.filter_cons, List.count_cons]
      by_cases h1 : j < m
      · rw [if_pos (by simp only [decide_eq_true_eq]; omega),
            if_pos (by simp only [decide_eq_true_eq]; omega),
            if_neg (by simp only [beq_iff_eq]; omega)]
        simp only [List.length_cons]
        omega
      · by_cases h2 : j = m
        · subst h2
          rw [if_pos (by simp only [decide_eq_true_eq]; omega),
              if_neg (by simp only [decide_eq_true_eq]; omega),
              if_pos (by simp)]
          simp only [List.length_cons]
          omega
        · rw [if_neg (by simp only [decide_eq_true_eq]; omega),
              if_neg (by simp only [decide_eq_true_eq]; omega),
              if_neg (by simp only [beq_iff_eq]; omega)]
          omega

theorem two_mul_le_length_filter (s : List Nat) : ∀ m,
    (∀ i, i < m → 2 ≤ s.count i) →
      2 * m ≤ (s.filter (fun i => decide (i < m))).length
  | 0, _ => by omega
  | m + 1, h => by
      rw [length_filter_succ m s]
      have ih := two_mul_le_length_filter s m (fun i hi => h i (by omega))
      have hm := h m (by omega)
      omega

-- ------------------------------------------------------------------
-- The lower bound
-- ------------------------------------------------------------------

/-- **NO PLAY BEATS `2n - 1`.**  Any legal play that pebbles the far end
of a chain of `n` cells, with any peak whatsoever, makes at least
`2n - 1` moves. -/
theorem two_mul_sub_one_le_length {n : Nat} (hn : 1 ≤ n) {s : List Nat}
    (hr : ∀ i ∈ s, i < n) (hleg : legalB (emptyBoard n) s = true)
    (hex : execB (emptyBoard n) s = doneBoard n) :
    2 * n - 1 ≤ s.length := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hblen : (emptyBoard (m + 1)).length = m + 1 := by simp
  -- the values of the final board
  have hdb : doneBoard (m + 1) = (emptyBoard (m + 1)).set m true := rfl
  have hdone_top : nth (doneBoard (m + 1)) m = true := by
    rw [hdb]
    exact nth_set_eq (emptyBoard (m + 1)) m true (by simp)
  have hdone_low : ∀ i, i < m → nth (doneBoard (m + 1)) i = false := by
    intro i hi
    rw [hdb, nth_set_ne _ _ _ _ (by omega : m ≠ i)]
    exact nth_emptyBoard _ i
  -- the top cell is toggled
  have htop : m ∈ s := by
    by_contra hc
    have := nth_exec_of_not_mem s (emptyBoard (m + 1)) m hc
    rw [hex, hdone_top, nth_emptyBoard] at this
    exact Bool.noConfusion this
  -- hence every cell is toggled
  have hall : ∀ i, i < m + 1 → i ∈ s := by
    intro i hi
    by_contra hc
    exact not_mem_above s (m + 1) i hleg hc (m - i)
      (by rw [show i + (m - i) = m by omega]; exact htop)
  -- every cell below the top is toggled at least twice
  have hcount2 : ∀ i, i < m → 2 ≤ s.count i := by
    intro i hi
    have hpos : 1 ≤ s.count i := by
      rcases Nat.eq_zero_or_pos (s.count i) with h0 | hp
      · exact absurd (hall i (by omega)) (List.count_eq_zero.mp h0)
      · exact hp
    by_contra hc
    have hone : s.count i = 1 := by omega
    have hp := nth_execB_parity s (emptyBoard (m + 1)) i
      (by rw [emptyBoard_length]; omega)
    rw [hex, hone] at hp
    rw [hdone_low i hi, nth_emptyBoard] at hp
    simp at hp
  have hcount1 : 1 ≤ s.count m := by
    rcases Nat.eq_zero_or_pos (s.count m) with h0 | hp
    · exact absurd htop (List.count_eq_zero.mp h0)
    · exact hp
  -- sum them
  have hself : s.filter (fun i => decide (i < m + 1)) = s :=
    List.filter_eq_self.mpr (fun i hi => by simpa using hr i hi)
  have hsplit := length_filter_succ m s
  rw [hself] at hsplit
  have hlow := two_mul_le_length_filter s m hcount2
  omega

/-- The same bound for the game optimum. -/
theorem two_mul_sub_one_le_gameF {n S : Nat} (hn : 1 ≤ n)
    (hne : ∃ t, ReachIn n S t) : 2 * n - 1 ≤ gameF n S := by
  obtain ⟨s, hlen, hr, hleg, hex, _⟩ := reachIn_gameF hne
  exact Nat.le_trans (two_mul_sub_one_le_length hn hr hleg hex) hlen

/-- **THE LINEAR REGIME, EXACTLY** — Knill's Obs 2.2(i) as a statement
about the game rather than about the row.  With at least as many pebbles
as cells, the game optimum is exactly `2n - 1`: the lower bound above
meets the row's construction. -/
theorem gameF_linear {n S : Nat} (h1 : 1 ≤ n) (h2 : n ≤ S) :
    gameF n S = 2 * n - 1 := by
  rcases S with _ | _ | s
  · exact absurd (Nat.le_trans h1 h2) (by omega)
  · have hn : n = 1 := by omega
    subst hn
    refine Nat.le_antisymm ?_ ?_
    · simpa using gameF_le (reachIn_one 1 (by omega))
    · exact two_mul_sub_one_le_gameF (by omega) ⟨1, reachIn_one 1 (by omega)⟩
  · have hpow : n ≤ 2 ^ (s + 1) := by
      have := succ_le_two_pow s
      omega
    have hne : ∃ t, ReachIn n (s + 2) t := ⟨_, reachIn_Fpre s n h1 hpow⟩
    refine Nat.le_antisymm ?_ (two_mul_sub_one_le_gameF h1 hne)
    have hle := gameF_le_Fpre s n h1 hpow
    rwa [Fpre_linear s n h1 (by omega)] at hle

end RevPebbling.GameLinearLower
