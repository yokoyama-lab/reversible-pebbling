import RevPebbling.RetentionPremium
import RevPebbling.RowExact
import RevPebbling.HalvedDifference
import RevPebbling.CompositionAnchor

/-!
# The near-full half-reach: `gameH n (n-1) = n + 1` (this work, 2026-08-29)

`RetentionPremium` certifies single boards by a verified BFS.  This file
turns the near-full column of that table into an **unconditional family
theorem**: with one pebble fewer than there are cells, the half-reach is

  `gameH n (n - 1) = n + 1`  for every `n ≥ 3`.

Both directions are proved for all `n` at once; nothing here is decided
by `decide` or `native_decide`.

* **Upper bound** (`halfIn_near_full`): the play `0, 1, …, n-2, 0, n-1`.
  It fills the chain up to `n-2` (that is already `n-1` pebbles, the
  whole budget), frees cell `0`, and only then reaches the far end.
* **Lower bound** (`not_halfIn_near_full`): every cell must be toggled
  at least once (legality propagates backwards from the far end), so a
  play has length `≥ n`; a play of length *exactly* `n` toggles each
  cell exactly once and therefore ends with the chain full, i.e. `n`
  pebbles, exceeding the budget `n - 1`.  Hence `≥ n + 1`.

Via `gameT = 2 * gameH` (`HalfReach`) this also fixes the complete
optimum for the whole family, `gameT n (n - 1) = 2n + 2`
(`gameT_near_full`).  For `n ≥ 4`, the generated-row count law then
shows that the first entry beyond the linear prefix is exactly two,
giving the clean optimum `gameF n (n - 1) = 2n + 1`
(`gameF_near_full`) and retention premium `-1` (`premium_near_full`).

Consistency with the BFS-certified values: `gameH 4 3 = 5` and
`gameH 5 4 = 6` of `RetentionPremium` are re-derived from the family
theorem at the end of this file (`gameH_4_3_of_family`,
`gameH_5_4_of_family`), by a route that shares no computation with
`native_decide`.

The numeric oracle (`2026_exact_reversible_pebbling/autoresearch/
retention_premium_oracle.py`) gives `H(n, n-1) = n + 1` for
`n = 3, …, 12`, and no half-reach at all for `n = 2, p = 1` — matching
the hypothesis `3 ≤ n` below (`n = 2` needs both cells pebbled at once).
-/

namespace RevPebbling.NearFull

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.GameCost RevPebbling.GameCompleteCost
open RevPebbling.HalfReach RevPebbling.RetentionPremium
open RevPebbling.CountRecursion RevPebbling.DifferenceMergeProperty
open RevPebbling.KnillObs RevPebbling.HalvedDifference
open RevPebbling.CompositionAnchor RevPebbling.RowExact

-- ------------------------------------------------------------------
-- Prefix boards
-- ------------------------------------------------------------------

/-- The prefix board of length `n`: cells `< k` pebbled, the rest empty. -/
def pb (n k : Nat) : Board :=
  List.replicate k true ++ List.replicate (n - k) false

theorem nth_cons_zero (a : Bool) (t : Board) : nth (a :: t) 0 = a := rfl

theorem nth_cons_succ (a : Bool) (t : Board) (j : Nat) :
    nth (a :: t) (j + 1) = nth t j := rfl

theorem nth_replicate_false : ∀ (m j : Nat), nth (List.replicate m false) j = false
  | 0, _ => rfl
  | m + 1, 0 => by rw [List.replicate_succ]; rfl
  | m + 1, j + 1 => by
      rw [List.replicate_succ, nth_cons_succ]
      exact nth_replicate_false m j

theorem nth_emptyBoard (n j : Nat) : nth (emptyBoard n) j = false :=
  nth_replicate_false n j

theorem ones_replicate_true : ∀ k : Nat, ones (List.replicate k true) = k
  | 0 => rfl
  | k + 1 => by
      have h : ones (List.replicate (k + 1) true) = ones (List.replicate k true) + 1 := by
        rw [List.replicate_succ]
        simp [ones, List.count_cons]
      rw [h, ones_replicate_true k]

theorem nth_replicate_true_append (c : Board) : ∀ (k i : Nat),
    nth (List.replicate k true ++ c) i = if i < k then true else nth c (i - k)
  | 0, i => by simp [nth]
  | k + 1, 0 => by rw [List.replicate_succ]; simp [nth_cons_zero]
  | k + 1, i + 1 => by
      rw [List.replicate_succ, List.cons_append, nth_cons_succ,
        nth_replicate_true_append c k i]
      by_cases h : i < k
      · simp [h, Nat.succ_lt_succ h]
      · have h' : ¬ (i + 1 < k + 1) := by omega
        have : i + 1 - (k + 1) = i - k := by omega
        simp [h, h', this]

theorem nth_pb {n k : Nat} (h : k ≤ n) (i : Nat) :
    nth (pb n k) i = decide (i < k) := by
  unfold pb
  rw [nth_replicate_true_append, nth_replicate_false]
  by_cases hi : i < k <;> simp [hi]

theorem ones_pb (n k : Nat) : ones (pb n k) = k := by
  rw [pb, ones_append, ones_replicate_true, ones_replicate]
  omega

/-- Freeing a pebbled cell drops the count by one. -/
theorem ones_toggle_of_true {b : Board} {i : Nat} (hi : i < b.length)
    (h : nth b i = true) : ones (toggle b i) + 1 = ones b := by
  have h1 := ones_set b i (!(nth b i)) hi
  rw [h] at h1
  simpa [toggle, h] using h1

/-- Pebbling an empty cell raises the count by one. -/
theorem ones_toggle_of_false {b : Board} {i : Nat} (hi : i < b.length)
    (h : nth b i = false) : ones (toggle b i) = ones b + 1 := by
  have h1 := ones_set b i (!(nth b i)) hi
  rw [h] at h1
  simpa [toggle, h] using h1

theorem length_pb {n k : Nat} (h : k ≤ n) : (pb n k).length = n := by
  simp [pb]
  omega

theorem set_replicate_true_append (c : Board) : ∀ (k : Nat) (v : Bool),
    (List.replicate k true ++ (false :: c)).set k v
      = List.replicate k true ++ (v :: c)
  | 0, v => by simp
  | k + 1, v => by
      rw [List.replicate_succ, List.cons_append, List.set_cons_succ,
        set_replicate_true_append c k v, List.cons_append]

theorem toggle_pb {n k : Nat} (h : k < n) : toggle (pb n k) k = pb n (k + 1) := by
  have hnth : nth (pb n k) k = false := by
    rw [nth_pb (Nat.le_of_lt h)]; simp
  have hsplit : List.replicate (n - k) false
      = false :: List.replicate (n - (k + 1)) false := by
    have hk : n - k = (n - (k + 1)) + 1 := by omega
    rw [hk, List.replicate_succ]
  show (pb n k).set k (!(nth (pb n k) k)) = pb n (k + 1)
  rw [hnth]
  simp only [Bool.not_false]
  show (List.replicate k true ++ List.replicate (n - k) false).set k true
      = List.replicate (k + 1) true ++ List.replicate (n - (k + 1)) false
  rw [hsplit, set_replicate_true_append, List.replicate_succ', List.append_assoc]
  rfl

-- ------------------------------------------------------------------
-- The ascending play `0, 1, …, k-1`
-- ------------------------------------------------------------------

theorem exec_range : ∀ {n k : Nat}, k ≤ n →
    execB (emptyBoard n) (List.range k) = pb n k := by
  intro n k
  induction k with
  | zero =>
      intro _
      show execB (emptyBoard n) [] = pb n 0
      simp [pb, emptyBoard, execB]
  | succ k ih =>
      intro h
      rw [List.range_succ, exec_append, ih (by omega)]
      show toggle (pb n k) k = pb n (k + 1)
      exact toggle_pb (by omega)

theorem okMove_pb {n k : Nat} (h : k ≤ n) : okMove (pb n k) k = true := by
  cases k with
  | zero => rfl
  | succ j =>
      show ((j + 1 == 0) || nth (pb n (j + 1)) (j + 1 - 1)) = true
      have : j + 1 - 1 = j := by omega
      rw [this, nth_pb h]
      simp

theorem legal_range : ∀ {n k : Nat}, k ≤ n →
    legalB (emptyBoard n) (List.range k) = true := by
  intro n k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro h
      rw [List.range_succ, legal_append, ih (by omega), exec_range (by omega)]
      show (true && (okMove (pb n k) k && legalB (toggle (pb n k) k) [])) = true
      rw [okMove_pb (by omega)]
      rfl

theorem maxOnes_range : ∀ {n k : Nat}, k ≤ n →
    maxOnes (emptyBoard n) (List.range k) = k := by
  intro n k
  induction k with
  | zero =>
      intro _
      show ones (emptyBoard n) = 0
      exact ones_emptyBoard n
  | succ k ih =>
      intro h
      rw [List.range_succ, maxOnes_append, ih (by omega), exec_range (by omega)]
      have hstep : maxOnes (pb n k) [k]
          = max (ones (pb n k)) (ones (toggle (pb n k) k)) := rfl
      rw [hstep, toggle_pb (by omega), ones_pb, ones_pb]
      omega

-- ------------------------------------------------------------------
-- Upper bound: the play `0, 1, …, n-2, 0, n-1`
-- ------------------------------------------------------------------

/-- The near-full play: fill the chain up to `n-2`, free cell `0`, then
reach the far end. -/
def nearFullPlay (n : Nat) : List Nat := List.range (n - 1) ++ [0, n - 1]

section Upper

variable {n : Nat}

/-- The board just before the two closing moves. -/
private theorem exec_head (h : 3 ≤ n) :
    execB (emptyBoard n) (List.range (n - 1)) = pb n (n - 1) :=
  exec_range (by omega)

private theorem length_pb' (h : 3 ≤ n) : (pb n (n - 1)).length = n :=
  length_pb (by omega)

/-- Freeing cell `0` from the full prefix leaves `n - 2` pebbles. -/
private theorem ones_free (h : 3 ≤ n) :
    ones (toggle (pb n (n - 1)) 0) = n - 2 := by
  have hnth : nth (pb n (n - 1)) 0 = true := by
    rw [nth_pb (by omega)]; simp; omega
  have hlen : (0 : Nat) < (pb n (n - 1)).length := by rw [length_pb' h]; omega
  have h1 := ones_toggle_of_true hlen hnth
  rw [ones_pb] at h1
  omega

private theorem nth_free_ne (h : 3 ≤ n) {j : Nat} (hj : j ≠ 0) :
    nth (toggle (pb n (n - 1)) 0) j = nth (pb n (n - 1)) j :=
  nth_set_ne _ 0 j _ (fun hc => hj hc.symm)

/-- Reaching the far end brings the count back to `n - 1`. -/
private theorem ones_reach (h : 3 ≤ n) :
    ones (toggle (toggle (pb n (n - 1)) 0) (n - 1)) = n - 1 := by
  have hclen : (toggle (pb n (n - 1)) 0).length = n := by
    rw [toggle, length_set]; exact length_pb' h
  have hnth : nth (toggle (pb n (n - 1)) 0) (n - 1) = false := by
    rw [nth_free_ne h (by omega), nth_pb (by omega)]
    simp
  have hlen : (n - 1) < (toggle (pb n (n - 1)) 0).length := by rw [hclen]; omega
  have h1 := ones_toggle_of_false hlen hnth
  rw [ones_free h] at h1
  omega

theorem halfIn_near_full (h : 3 ≤ n) : HalfIn n (n - 1) (n + 1) := by
  refine ⟨nearFullPlay n, ?_, ?_, ?_, ?_, ?_⟩
  · show (List.range (n - 1) ++ [0, n - 1]).length ≤ n + 1
    simp
    omega
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · have := List.mem_range.mp hi; omega
    · simp at hi; rcases hi with hi | hi <;> omega
  · show legalB (emptyBoard n) (List.range (n - 1) ++ [0, n - 1]) = true
    rw [legal_append, legal_range (show n - 1 ≤ n by omega), exec_head h]
    show (true && (okMove (pb n (n - 1)) 0 &&
      (okMove (toggle (pb n (n - 1)) 0) (n - 1) &&
        legalB (toggle (toggle (pb n (n - 1)) 0) (n - 1)) []))) = true
    have hok0 : okMove (pb n (n - 1)) 0 = true := rfl
    have hok1 : okMove (toggle (pb n (n - 1)) 0) (n - 1) = true := by
      have hne : (n - 1 == 0) = false := by simp; omega
      show ((n - 1 == 0) || nth (toggle (pb n (n - 1)) 0) (n - 1 - 1)) = true
      rw [hne, nth_free_ne h (by omega), nth_pb (by omega)]
      simp
      omega
    rw [hok0, hok1]
    rfl
  · show maxOnes (emptyBoard n) (List.range (n - 1) ++ [0, n - 1]) ≤ n - 1
    rw [maxOnes_append, maxOnes_range (show n - 1 ≤ n by omega), exec_head h]
    have hstep : maxOnes (pb n (n - 1)) [0, n - 1]
        = max (ones (pb n (n - 1)))
            (max (ones (toggle (pb n (n - 1)) 0))
              (ones (toggle (toggle (pb n (n - 1)) 0) (n - 1)))) := rfl
    rw [hstep, ones_pb, ones_free h, ones_reach h]
    omega
  · refine ⟨(nearFullPlay n).length, ?_⟩
    rw [List.take_length]
    show nth (execB (emptyBoard n) (List.range (n - 1) ++ [0, n - 1])) (n - 1) = true
    rw [exec_append, exec_head h]
    show nth (toggle (toggle (pb n (n - 1)) 0) (n - 1)) (n - 1) = true
    have hclen : (toggle (pb n (n - 1)) 0).length = n := by
      rw [toggle, length_set]; exact length_pb' h
    have hnth : nth (toggle (pb n (n - 1)) 0) (n - 1) = false := by
      rw [nth_free_ne h (by omega), nth_pb (by omega)]
      simp
    show nth ((toggle (pb n (n - 1)) 0).set (n - 1)
      (!(nth (toggle (pb n (n - 1)) 0) (n - 1)))) (n - 1) = true
    rw [nth_set_eq _ _ _ (by rw [hclen]; omega), hnth]
    rfl

end Upper

-- ------------------------------------------------------------------
-- Lower bound: a play of length `n` would end with the chain full
-- ------------------------------------------------------------------

theorem length_execB : ∀ (s : List Nat) (b : Board), (execB b s).length = b.length
  | [], _ => rfl
  | i :: rest, b => by
      show (execB (toggle b i) rest).length = b.length
      rw [length_execB rest (toggle b i), toggle, length_set]

/-- Legality propagates backwards: a cell can only be toggled after its
predecessor has been. -/
theorem pred_mem_of_mem {n : Nat} {s : List Nat}
    (hleg : legalB (emptyBoard n) s = true) {i : Nat} (hi : i ∈ s) (hpos : 0 < i) :
    i - 1 ∈ s := by
  obtain ⟨A, C, hs, hA⟩ := split_first_occ i s hi
  subst hs
  rw [legal_append, Bool.and_eq_true] at hleg
  have hstep : legalB (execB (emptyBoard n) A) (i :: C)
      = (okMove (execB (emptyBoard n) A) i &&
          legalB (toggle (execB (emptyBoard n) A) i) C) := rfl
  rw [hstep, Bool.and_eq_true] at hleg
  have hok := hleg.2.1
  have hz : (i == 0) = false := by simp; omega
  have hnth : nth (execB (emptyBoard n) A) (i - 1) = true := by
    have : (okMove (execB (emptyBoard n) A) i)
        = ((i == 0) || nth (execB (emptyBoard n) A) (i - 1)) := rfl
    rw [this, hz] at hok
    simpa using hok
  have hin : i - 1 ∈ A := by
    by_contra hcon
    have hne : ∀ j ∈ A, j ≠ i - 1 := by
      intro j hj hji; exact hcon (hji ▸ hj)
    rw [RevPebbling.HalfReach.nth_exec_of_not_mem (i - 1) A (emptyBoard n) hne,
      nth_emptyBoard] at hnth
    exact Bool.noConfusion hnth
  exact List.mem_append_left _ hin

theorem down_closed {n : Nat} {s : List Nat}
    (hleg : legalB (emptyBoard n) s = true) :
    ∀ i : Nat, i ∈ s → ∀ j : Nat, j ≤ i → j ∈ s := by
  intro i
  induction i with
  | zero => intro hi j hj; rw [Nat.le_zero.mp hj]; exact hi
  | succ k ih =>
      intro hi j hj
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · have hk : k ∈ s := by
          have hp := pred_mem_of_mem hleg hi (by omega)
          simpa using hp
        exact ih hk j (by omega)
      · have : j = k + 1 := by omega
        subst this; exact hi

/-- Toggling a cell an odd number of times flips it; an even number of
times leaves it. -/
theorem nth_exec_parity : ∀ (s : List Nat) (b : Board) (v : Nat), v < b.length →
    nth (execB b s) v = (if s.count v % 2 = 1 then !(nth b v) else nth b v)
  | [], b, v, _ => by simp [execB]
  | i :: rest, b, v, hv => by
      have hlen : v < (toggle b i).length := by rw [toggle, length_set]; exact hv
      have hstep : execB b (i :: rest) = execB (toggle b i) rest := rfl
      rw [hstep, nth_exec_parity rest (toggle b i) v hlen]
      by_cases hiv : i = v
      · subst hiv
        have hset : nth (toggle b i) i = !(nth b i) :=
          nth_set_eq _ _ _ hv
        have hcount : (i :: rest).count i = rest.count i + 1 := by
          simp [List.count_cons]
        rw [hset, hcount]
        by_cases hp : rest.count i % 2 = 1
        · have : ¬ ((rest.count i + 1) % 2 = 1) := by omega
          simp [hp, this]
        · have : (rest.count i + 1) % 2 = 1 := by omega
          simp [hp, this]
      · have hset : nth (toggle b i) v = nth b v :=
          nth_set_ne _ _ _ _ hiv
        have hcount : (i :: rest).count v = rest.count v := by
          simp [List.count_cons, hiv]
        rw [hset, hcount]

theorem ones_eq_length_of_all : ∀ (b : Board), (∀ i < b.length, nth b i = true) →
    ones b = b.length
  | [], _ => rfl
  | a :: t, h => by
      have ha : a = true := h 0 (by simp)
      have ht : ∀ i < t.length, nth t i = true := by
        intro i hi
        have := h (i + 1) (by simp; omega)
        rwa [nth_cons_succ] at this
      have hrec := ones_eq_length_of_all t ht
      subst ha
      show ones (true :: t) = (true :: t).length
      have : ones (true :: t) = ones t + 1 := by simp [ones, List.count_cons]
      rw [this, hrec]
      simp

theorem not_halfIn_near_full {n : Nat} (h : 3 ≤ n) : ¬ HalfIn n (n - 1) n := by
  intro hh
  obtain ⟨s, hlen, hrange, hleg, hpk, htop⟩ := halfIn_tight hh
  -- every cell is toggled at least once
  have hlast : n - 1 ∈ s := by
    by_contra hcon
    have hne : ∀ j ∈ s, j ≠ n - 1 := by
      intro j hj hji; exact hcon (hji ▸ hj)
    rw [RevPebbling.HalfReach.nth_exec_of_not_mem (n - 1) s (emptyBoard n) hne,
      nth_emptyBoard] at htop
    exact Bool.noConfusion htop
  have hall : ∀ i, i < n → i ∈ s := by
    intro i hi
    exact down_closed hleg (n - 1) hlast i (by omega)
  -- hence the play has length at least `n`
  have hsub : Finset.range n ⊆ s.toFinset := by
    intro x hx
    rw [List.mem_toFinset]
    exact hall x (Finset.mem_range.mp hx)
  have hsup : s.toFinset ⊆ Finset.range n := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_range.mpr (hrange x hx)
  have hfin : s.toFinset = Finset.range n := Finset.Subset.antisymm hsup hsub
  have hcard : n ≤ s.length := by
    calc n = (Finset.range n).card := by rw [Finset.card_range]
      _ = s.toFinset.card := by rw [hfin]
      _ ≤ s.length := List.toFinset_card_le s
  have hexact : s.length = n := Nat.le_antisymm hlen hcard
  -- a play of that length toggles every cell exactly once
  have hnodup : s.Nodup := by
    have hdlen : s.dedup.length = s.length := by
      rw [← List.card_toFinset, hfin, Finset.card_range, hexact]
    have hdeq : s.dedup = s := (List.dedup_sublist s).eq_of_length hdlen
    rw [← hdeq]
    exact List.nodup_dedup s
  have hcount : ∀ i, i < n → s.count i = 1 := by
    intro i hi
    exact List.count_eq_one_of_mem hnodup (hall i hi)
  -- so the final board is full
  have hblen : (execB (emptyBoard n) s).length = n := by
    rw [length_execB, emptyBoard, List.length_replicate]
  have hfull : ∀ i < (execB (emptyBoard n) s).length,
      nth (execB (emptyBoard n) s) i = true := by
    intro i hi
    rw [hblen] at hi
    have hv : i < (emptyBoard n).length := by
      rw [emptyBoard, List.length_replicate]; exact hi
    rw [nth_exec_parity s (emptyBoard n) i hv, hcount i hi]
    simp [nth_emptyBoard]
  have hones : ones (execB (emptyBoard n) s) = n := by
    rw [ones_eq_length_of_all _ hfull, hblen]
  -- but the budget is `n - 1`
  have hle : ones (execB (emptyBoard n) s) ≤ maxOnes (emptyBoard n) s := by
    have hsplit : maxOnes (emptyBoard n) (s ++ []) =
        max (maxOnes (emptyBoard n) s) (maxOnes (execB (emptyBoard n) s) []) :=
      maxOnes_append _ _ _
    rw [List.append_nil] at hsplit
    have hnil : maxOnes (execB (emptyBoard n) s) [] = ones (execB (emptyBoard n) s) := rfl
    rw [hnil] at hsplit
    omega
  rw [hones] at hle
  omega

-- ------------------------------------------------------------------
-- The family theorem
-- ------------------------------------------------------------------

/-- **The near-full half-reach.**  With one pebble fewer than cells, the
far end is first reached on move `n + 1`. -/
theorem gameH_near_full {n : Nat} (h : 3 ≤ n) : gameH n (n - 1) = n + 1 :=
  gameH_eq_of (halfIn_near_full h) (by simpa using not_halfIn_near_full h)

/-- **The near-full complete optimum**: out and straight back, by
`gameT = 2 * gameH`.  A complete computation exists because the
half-reach itself can be mirrored. -/
theorem gameT_near_full {n : Nat} (h : 3 ≤ n) : gameT n (n - 1) = 2 * n + 2 := by
  have hex : ∃ t, CompleteInAt n (n - 1) t :=
    ⟨2 * (n + 1), completeInAt_of_halfIn (halfIn_near_full h)⟩
  rw [gameT_eq_two_mul_gameH hex, gameH_near_full h]
  omega

-- ------------------------------------------------------------------
-- Clean reach: the first row entry after the linear prefix
-- ------------------------------------------------------------------

theorem near_reach_bound (r : Nat) : r + 4 ≤ 2 ^ (r + 2) := by
  induction r with
  | zero => decide
  | succ r ih =>
      rw [show r + 1 + 2 = (r + 2) + 1 by omega, Nat.pow_succ]
      have hp : 1 ≤ 2 ^ (r + 2) := Nat.one_le_two_pow
      omega

/-- The first generated-row entry after its linear prefix is exactly two. -/
theorem first_after_linear (r : Nat) :
    (rowIter (r + 1))[r + 2]'(by
      rw [rowIter_length]
      have hpow := near_reach_bound r
      apply Nat.lt_sub_of_add_lt
      have hh : r + 3 < 2 ^ (r + 2) :=
        Nat.lt_of_lt_of_le (by omega) hpow
      simpa only [show r + 2 + 1 = r + 3 by omega] using hh) = 2 := by
  obtain ⟨hsort, _⟩ := rowIter_invariant (r + 1)
  have hlen : r + 2 < (rowIter (r + 1)).length := by
    rw [rowIter_length]
    have hpow := near_reach_bound r
    apply Nat.lt_sub_of_add_lt
    have hh : r + 3 < 2 ^ (r + 2) :=
      Nat.lt_of_lt_of_le (by omega) hpow
    simpa only [show r + 2 + 1 = r + 3 by omega] using hh
  have hcount2 : r + 3 ≤ countLe (rowIter (r + 1)) 2 := by
    have hrec := count_recursion_lower r 2 (by omega)
    rw [show 2 / 2 = 1 by omega] at hrec
    have hpos := countLe_pos r 2 (by omega)
    have hone := rowIter_count_one r
    omega
  have hup : (rowIter (r + 1))[r + 2]'hlen ≤ 2 :=
    sorted_getElem_le_of_countLe _ _ _ hsort hlen (by omega)
  have hlo : 2 ≤ (rowIter (r + 1))[r + 2]'hlen := by
    by_contra hc
    have hle : (rowIter (r + 1))[r + 2]'hlen ≤ 1 := by omega
    have hi := index_lt_countLe (rowIter (r + 1)) 1 (r + 2) hsort hlen hle
    rw [rowIter_count_one] at hi
    omega
  omega

/-- The generated row gives the near-full clean cost. -/
theorem Fpre_near_full (r : Nat) :
    Fpre (rowIter (r + 1)) (r + 4) = 2 * (r + 4) + 1 := by
  have hstep := Fpre_step (rowIter (r + 1)) (r + 2)
  have hstep' : Fpre (rowIter (r + 1)) (r + 4) =
      Fpre (rowIter (r + 1)) (r + 3) +
        2 * ((rowIter (r + 1))[r + 2]?.getD 0) := by
    simpa only [show r + 2 + 2 = r + 4 by omega,
      show r + 2 + 1 = r + 3 by omega] using hstep
  have hlin := Fpre_linear (r + 1) (r + 3) (by omega) (by omega)
  have hlen : r + 2 < (rowIter (r + 1)).length := by
    rw [rowIter_length]
    have hpow := near_reach_bound r
    apply Nat.lt_sub_of_add_lt
    have hh : r + 3 < 2 ^ (r + 2) :=
      Nat.lt_of_lt_of_le (by omega) hpow
    simpa only [show r + 2 + 1 = r + 3 by omega] using hh
  have hget : (rowIter (r + 1))[r + 2]? = some 2 := by
    rw [List.getElem?_eq_getElem hlen, first_after_linear]
  rw [hget] at hstep'
  simp only [Option.getD_some] at hstep'
  omega

/-- **Near-full clean optimum.** One pebble short of the linear regime
costs exactly two additional moves. The restriction `4 ≤ n` is sharp:
`n = 3, p = 2` cannot cleanly reach the last cell. -/
theorem gameF_near_full {n : Nat} (hn : 4 ≤ n) :
    gameF n (n - 1) = 2 * n + 1 := by
  let r := n - 4
  have hnform : n = r + 4 := by omega
  have hpform : n - 1 = r + 3 := by omega
  have hsform : n - 3 = r + 1 := by omega
  have hexp : (n - 3) + 1 = r + 2 := by omega
  have hreach : n ≤ 2 ^ ((n - 3) + 1) := by
    rw [hexp, hnform]
    exact near_reach_bound r
  have hrow := gameF_eq_row (n - 3) n (by omega) hreach
  have hspace : (n - 3) + 2 = n - 1 := by omega
  rw [hspace, hpform, hsform, hnform] at hrow
  calc gameF n (n - 1) = gameF (r + 4) (r + 3) := by
        rw [hnform]
        congr 1
    _ = Fpre (rowIter (r + 1)) (r + 4) := hrow
    _ = 2 * (r + 4) + 1 := Fpre_near_full r
    _ = 2 * n + 1 := by rw [hnform]

/-- A compatibility form for callers that already have the clean formula. -/
theorem premium_near_full_of_gameF {n : Nat} (h : 3 ≤ n)
    (hF : gameF n (n - 1) = 2 * n + 1) :
    gameF n (n - 1) + 1 = 2 * gameH n (n - 1) := by
  rw [hF, gameH_near_full h]
  omega

/-- **Near-full retention premium `-1`, for the whole playable clean family.** -/
theorem premium_near_full {n : Nat} (h : 4 ≤ n) :
    gameF n (n - 1) + 1 = 2 * gameH n (n - 1) := by
  rw [gameF_near_full h, gameH_near_full (by omega)]
  omega

/-- Cross-check against `RetentionPremium.gameH_4_3`, which was obtained
by `native_decide` on the verified BFS.  This route shares no
computation with it. -/
theorem gameH_4_3_of_family : gameH 4 3 = 5 := by
  have h := gameH_near_full (n := 4) (by omega)
  show gameH 4 (4 - 1) = 4 + 1
  exact h

/-- Same cross-check at `(5, 4)`. -/
theorem gameH_5_4_of_family : gameH 5 4 = 6 := by
  have h := gameH_near_full (n := 5) (by omega)
  show gameH 5 (5 - 1) = 5 + 1
  exact h

/-- Cross-check the clean family theorem against the independently
BFS-certified value `RetentionPremium.gameF_4_3`. -/
theorem gameF_4_3_of_family : gameF 4 3 = 9 := by
  have h := gameF_near_full (n := 4) (by omega)
  show gameF 4 (4 - 1) = 2 * 4 + 1
  exact h

/-- The same independent cross-check at `(5,4)`. -/
theorem gameF_5_4_of_family : gameF 5 4 = 11 := by
  have h := gameF_near_full (n := 5) (by omega)
  show gameF 5 (5 - 1) = 2 * 5 + 1
  exact h

-- Axiom audit: the family theorem must be free of the compiler axioms
-- that `RetentionPremium` uses for its finite checks.
#print axioms gameH_near_full
#print axioms gameT_near_full
#print axioms gameF_near_full
#print axioms premium_near_full
#print axioms gameH_4_3_of_family
#print axioms gameF_4_3_of_family
#print axioms gameF_5_4_of_family

end RevPebbling.NearFull
