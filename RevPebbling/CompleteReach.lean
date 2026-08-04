import RevPebbling.CompleteCost
import RevPebbling.ReachLimit

/-!
# Královič Thm 3.1, fully general (this work)

`PebblingTheory.kralovic_space_characterisation` checks on the grid
`n ≤ 16, p ≤ 4` that a **complete** computation with `p` pebbles — one
that starts and ends on the empty chain and covers every cell — exists
iff `n ≤ 2^p - 1`.  This file proves it for every `n` and every `p`.

One direction was already general: `PebblingFoundations.complete_bound`
is the middle-vertex induction, and `le_two_pow_sub_one_of_completeIn`
just packages it.  The other direction — the **construction** — is what
this file adds, and it is the item the project notes list as the
remaining "achievability side" of this characterisation.

## The construction

`CompleteIn n p` records a complete computation; by
`PebblingFoundations.coverage` it is enough to demand that the *far end*
is ever pebbled, since a legal computation that reaches a cell has
reached everything below it.

Two moves build every instance:

* `completeIn_of_reachIn` — a clean reach followed by its own reverse
  (`PebblingFoundations.roundtrip_complete`).  This covers `n` cells with
  the peak the reach needed, so it settles everything up to the *reach*
  limit `2^{p-1}`.
* `completeIn_compose` — reach the cell `m-1` with `p` pebbles, stand on
  it, run a complete computation of the `k` cells above with the
  remaining `p-1` (lifted by `LiftAbove.liftAbove`), then retreat by
  reversing the first phase.  Peak stays `p`, because the middle phase
  spends one pebble on the foundation and `p-1` above it.

Splitting `n` at `2^{p-1}` and recursing on `p` turns those into
`completeIn_of_le`, and with the bound the characterisation
`completeIn_iff` is exactly Královič Thm 3.1:

  `CompleteIn n p ↔ n ≤ 2^p - 1`.

Note the contrast with the clean-reach limit `2^{p-1}` (Knill Thm 2.3,
`ReachLimit.reachIn_iff`): returning the board to empty lets `p` pebbles
cover **twice as far, less one**, because the top pebble no longer has to
stay put.
-/

namespace RevPebbling.CompleteReach

open RevPebbling.PebblingFoundations RevPebbling.GameReach
open RevPebbling.LiftAbove RevPebbling.ReachLimit

/-- **A COMPLETE COMPUTATION** in the sense of Královič: `n` cells, empty
to empty, peak at most `p`, every move inside the chain, and the far end
pebbled at some point — whence, by `coverage`, every cell is. -/
def CompleteIn (n p : Nat) : Prop :=
  ∃ s : List Nat, (∀ i ∈ s, i < n) ∧
    legalB (emptyBoard n) s = true ∧
    execB (emptyBoard n) s = emptyBoard n ∧
    maxOnes (emptyBoard n) s ≤ p ∧
    everOn (emptyBoard n) s (n - 1)

/-- Covering the far end covers the whole chain. -/
theorem covers_of_top {n : Nat} {s : List Nat}
    (hleg : legalB (emptyBoard n) s = true)
    (htop : everOn (emptyBoard n) s (n - 1)) :
    ∀ j, j < n → everOn (emptyBoard n) s j :=
  fun j hj => coverage n s (n - 1) hleg htop j (by omega)

/-- **THE IMPOSSIBILITY HALF**, repackaging `complete_bound`: `p` pebbles
cover at most `2^p - 1` cells completely. -/
theorem le_two_pow_sub_one_of_completeIn {n p : Nat} (h : CompleteIn n p) :
    n ≤ 2 ^ p - 1 := by
  obtain ⟨s, _, hleg, hex, hpk, htop⟩ := h
  exact complete_bound p n s n hleg hex hpk (fun j hj => covers_of_top hleg htop j hj)

-- ------------------------------------------------------------------
-- Two `everOn` transfer lemmas
-- ------------------------------------------------------------------

/-- Coverage carries across an append on the right. -/
theorem everOn_append_right {b : Board} {x y : List Nat} {v : Nat}
    (h : everOn (execB b x) y v) : everOn b (x ++ y) v := by
  obtain ⟨k, hk⟩ := h
  refine ⟨x.length + k, ?_⟩
  have hsp : (x ++ y).take (x.length + k) = x ++ y.take k := by
    simp [List.take_append]
  rw [hsp, exec_append]
  exact hk

/-- Coverage carries across a lift: what the play covers above the cut,
the lifted play covers above the cut. -/
theorem everOn_liftAbove {b : Board} {s : List Nat} {v base : Nat}
    (h : everOn (b.drop base) s v) : everOn b (liftAbove base s) (v + base) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have htake : (liftAbove base s).take k = liftAbove base (s.take k) := by
    simp [liftAbove, List.map_take]
  rw [htake, ← nth_drop_add, execB_liftAbove_drop]
  exact hk

-- ------------------------------------------------------------------
-- Building complete computations
-- ------------------------------------------------------------------

/-- **A CLEAN REACH BECOMES A COMPLETE COMPUTATION** by running backwards
afterwards, at the same peak. -/
theorem completeIn_of_reachIn {n p t : Nat} (hn : 1 ≤ n) (h : ReachIn n p t) :
    CompleteIn n p := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  obtain ⟨s, _, hr, hleg, hex, hpk⟩ := h
  have hend : nth (execB (emptyBoard (j + 1)) s) j = true := by
    rw [hex]; exact nth_doneBoard_self j
  obtain ⟨h1, h2, h3, h4⟩ := roundtrip_complete (j + 1) s j hleg hend
  refine ⟨s ++ s.reverse, ?_, h1, h2, ?_, ?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hr i hi
    · exact hr i (by simpa using hi)
  · show maxOnes (List.replicate (j + 1) false) (s ++ s.reverse) ≤ p
    rw [h3]; exact hpk
  · show everOn (List.replicate (j + 1) false) (s ++ s.reverse) j
    exact h4 j (Nat.le_refl _)

/-- **THE COMPOSITION.**  Reach cell `m-1` with `p` pebbles, complete the
`k` cells above it with the remaining `p-1`, then retreat.  Královič's
recursion, as a statement about plays. -/
theorem completeIn_compose {m k p t : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hp : 1 ≤ p) (h1 : ReachIn m p t) (h2 : CompleteIn k (p - 1)) :
    CompleteIn (m + k) p := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨s₁, _, hr1, hleg1, hex1, hpk1⟩ := h1
  obtain ⟨s₂, hr2, hleg2, hex2, hpk2, htop2⟩ := h2
  have hr1' : ∀ i ∈ s₁, i < (emptyBoard (a + 1)).length := by
    intro i hi; rw [emptyBoard_length]; exact hr1 i hi
  -- phase 1: the reach, padded to the full chain
  have hleg1' : legalB (emptyBoard (a + 1 + (j + 1))) s₁ = true := by
    rw [emptyBoard_split, legalB_pad _ _ _ hr1']; exact hleg1
  have hB1 : execB (emptyBoard (a + 1 + (j + 1))) s₁
      = doneBoard (a + 1) ++ emptyBoard (j + 1) := by
    rw [emptyBoard_split, execB_pad _ _ _ hr1', hex1]
  have hpk1' : maxOnes (emptyBoard (a + 1 + (j + 1))) s₁ ≤ p := by
    rw [emptyBoard_split, maxOnes_pad _ _ _ hr1', ones_emptyBoard]
    simpa using hpk1
  have hdrop : (doneBoard (a + 1) ++ emptyBoard (j + 1)).drop (a + 1)
      = emptyBoard (j + 1) := List.drop_left' (doneBoard_length (a + 1))
  have htake : (doneBoard (a + 1) ++ emptyBoard (j + 1)).take (a + 1)
      = doneBoard (a + 1) := List.take_left' (doneBoard_length (a + 1))
  -- phase 2: the complete computation above the foundation
  have hleg2' : legalB (doneBoard (a + 1) ++ emptyBoard (j + 1))
      (liftAbove (a + 1) s₂) = true := by
    refine legalB_liftAbove (a + 1) s₂ _ (Or.inr ?_) ?_
    · simpa using nth_doneBoard_last a (emptyBoard (j + 1))
    · rw [hdrop]; exact hleg2
  have hB2 : execB (doneBoard (a + 1) ++ emptyBoard (j + 1))
      (liftAbove (a + 1) s₂) = doneBoard (a + 1) ++ emptyBoard (j + 1) := by
    have hd := execB_liftAbove_drop (a + 1) s₂
      (doneBoard (a + 1) ++ emptyBoard (j + 1))
    have ht := execB_liftAbove_take (a + 1) s₂
      (doneBoard (a + 1) ++ emptyBoard (j + 1))
    rw [hdrop, hex2] at hd
    rw [htake] at ht
    calc execB (doneBoard (a + 1) ++ emptyBoard (j + 1)) (liftAbove (a + 1) s₂)
        = (execB (doneBoard (a + 1) ++ emptyBoard (j + 1))
              (liftAbove (a + 1) s₂)).take (a + 1)
            ++ (execB (doneBoard (a + 1) ++ emptyBoard (j + 1))
              (liftAbove (a + 1) s₂)).drop (a + 1) :=
          (List.take_append_drop _ _).symm
      _ = doneBoard (a + 1) ++ emptyBoard (j + 1) := by rw [ht, hd]
  have hpk2' : maxOnes (doneBoard (a + 1) ++ emptyBoard (j + 1))
      (liftAbove (a + 1) s₂) ≤ p := by
    have h := maxOnes_liftAbove (a + 1) s₂
      (doneBoard (a + 1) ++ emptyBoard (j + 1))
    rw [htake, hdrop, ones_doneBoard a] at h
    omega
  -- phase 3: the retreat
  have hrev_leg : legalB (doneBoard (a + 1)) s₁.reverse = true := by
    have h := legal_reverse (emptyBoard (a + 1)) s₁ hleg1
    rwa [hex1] at h
  have hrev_ex : execB (doneBoard (a + 1)) s₁.reverse = emptyBoard (a + 1) := by
    have h := exec_reverse_cancel (emptyBoard (a + 1)) s₁
    rwa [hex1] at h
  have hrev_pk : maxOnes (doneBoard (a + 1)) s₁.reverse ≤ p := by
    have h := maxOnes_reverse (emptyBoard (a + 1)) s₁
    rw [hex1] at h
    omega
  have hrrev : ∀ i ∈ s₁.reverse, i < (doneBoard (a + 1)).length := by
    intro i hi
    rw [doneBoard_length]
    exact hr1 i (by simpa using hi)
  have hleg3' : legalB (doneBoard (a + 1) ++ emptyBoard (j + 1)) s₁.reverse
      = true := by
    rw [legalB_pad _ _ _ hrrev]; exact hrev_leg
  have hB3 : execB (doneBoard (a + 1) ++ emptyBoard (j + 1)) s₁.reverse
      = emptyBoard (a + 1 + (j + 1)) := by
    rw [execB_pad _ _ _ hrrev, hrev_ex, ← emptyBoard_split]
  have hpk3' : maxOnes (doneBoard (a + 1) ++ emptyBoard (j + 1)) s₁.reverse
      ≤ p := by
    rw [maxOnes_pad _ _ _ hrrev, ones_emptyBoard]
    omega
  -- assemble
  refine ⟨s₁ ++ liftAbove (a + 1) s₂ ++ s₁.reverse, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · have := hr1 i hi; omega
      · obtain ⟨x, hx, rfl⟩ : ∃ x ∈ s₂, x + (a + 1) = i := by
          simpa [liftAbove] using hi
        have := hr2 x hx
        omega
    · have := hr1 i (by simpa using hi); omega
  · rw [legal_append, legal_append, exec_append, hB1, hleg1', hleg2', hB2,
      hleg3']
    simp
  · rw [exec_append, exec_append, hB1, hB2, hB3]
  · rw [maxOnes_append, maxOnes_append, exec_append, hB1, hB2]
    omega
  · -- the far end is covered during phase 2
    refine everOn_append_left (everOn_append_right ?_)
    rw [hB1]
    have hlift : everOn (doneBoard (a + 1) ++ emptyBoard (j + 1))
        (liftAbove (a + 1) s₂) (j + (a + 1)) := by
      refine everOn_liftAbove ?_
      rw [hdrop]
      simpa using htop2
    have harith : a + 1 + (j + 1) - 1 = j + (a + 1) := by omega
    rw [harith]
    exact hlift

/-- **THE ACHIEVABILITY HALF, fully general.**  Every `n` up to `2^p - 1`
admits a complete computation with `p` pebbles. -/
theorem completeIn_of_le : ∀ (p n : Nat), 1 ≤ p → 1 ≤ n → n ≤ 2 ^ p - 1 →
    CompleteIn n p := by
  intro p
  induction p with
  | zero => intro _ _ h; omega
  | succ p ih =>
      intro n _ hn hle
      have hpow : (1:Nat) ≤ 2 ^ p := Nat.one_le_two_pow
      rcases Nat.lt_or_ge (2 ^ p) n with hbig | hsmall
      · -- beyond the clean-reach limit: reach the midpoint, complete above
        have hp1 : 1 ≤ p := by
          rcases Nat.eq_zero_or_pos p with rfl | h
          · simp at hbig; omega
          · exact h
        have hk1 : 1 ≤ n - 2 ^ p := by omega
        have hk2 : n - 2 ^ p ≤ 2 ^ p - 1 := by
          have hd : (2:Nat) ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; omega
          omega
        have hmid : ∃ t, ReachIn (2 ^ p) (p - 1 + 2) t :=
          (reachIn_iff (2 ^ p) (p - 1) hpow).mpr (by
            rw [show p - 1 + 1 = p by omega])
        obtain ⟨t, ht⟩ := hmid
        rw [show p - 1 + 2 = p + 1 by omega] at ht
        have hcomp := completeIn_compose (m := 2 ^ p) (k := n - 2 ^ p) (p := p + 1)
          hpow hk1 (by omega) ht (by simpa using ih (n - 2 ^ p) hp1 hk1 hk2)
        rwa [show 2 ^ p + (n - 2 ^ p) = n by omega] at hcomp
      · -- within the clean-reach limit: a reach and its own reverse
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · have hn1 : n = 1 := by simp at hsmall; omega
          subst hn1
          exact completeIn_of_reachIn (by omega) reach_one
        · have hreach : ∃ t, ReachIn n (p - 1 + 2) t :=
            (reachIn_iff n (p - 1) hn).mpr (by
              rw [show p - 1 + 1 = p by omega]; exact hsmall)
          obtain ⟨t, ht⟩ := hreach
          rw [show p - 1 + 2 = p + 1 by omega] at ht
          exact completeIn_of_reachIn hn ht

/-- **KRÁLOVIČ THM 3.1, fully general.**  `p` pebbles suffice for a
complete computation on a chain of `n` cells exactly when
`n ≤ 2^p - 1` — twice the clean-reach limit `2^{p-1}`, less one. -/
theorem completeIn_iff (n p : Nat) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    CompleteIn n p ↔ n ≤ 2 ^ p - 1 :=
  ⟨le_two_pow_sub_one_of_completeIn, completeIn_of_le p n hp hn⟩

end RevPebbling.CompleteReach
