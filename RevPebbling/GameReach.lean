import RevPebbling.LiftAbove

/-!
# The game-side cost, and padding (this work, link (1))

Every general theorem of this artifact is about the generated row
`rowIter`; the pebble game itself is connected to it only on a bounded
grid (`PebblingTheory.knill_recursion_agrees_with_game`, `n < 12`,
`S < 5`).  Closing that gap needs the game-side optimum as an object,
which is what this file introduces:

`ReachIn n p t` — the chain of `n` cells can be *cleanly* pebbled (from
the empty board to the board carrying a single pebble on the last cell)
with peak at most `p` and at most `t` moves, by a schedule that stays
inside the chain.

The bounded moves are part of the definition on purpose: they are what
makes a schedule transportable between boards of different widths, and
that transport ("padding") is the content of this file —
`execB_pad`, `legalB_pad`, `maxOnes_pad`.  `LiftAbove` already provides
the opposite primitive, moving a schedule *up* onto a segment above a
foundation, so the two together are the vocabulary for Knill's
constructive half.
-/

namespace RevPebbling.GameReach

open RevPebbling.PebblingFoundations RevPebbling.LiftAbove

/-- The empty chain of `n` cells. -/
def emptyBoard (n : Nat) : Board := List.replicate n false

/-- The chain of `n` cells with a single pebble on the last one. -/
def doneBoard (n : Nat) : Board := (emptyBoard n).set (n - 1) true

@[simp] theorem emptyBoard_length (n : Nat) : (emptyBoard n).length = n := by
  simp [emptyBoard]

@[simp] theorem ones_emptyBoard (n : Nat) : ones (emptyBoard n) = 0 :=
  ones_replicate n

/-- **The game-side cost predicate.**  `n` cells, peak `≤ p`, at most
`t` moves, all of them inside the chain. -/
def ReachIn (n p t : Nat) : Prop :=
  ∃ s : List Nat, s.length ≤ t ∧ (∀ i ∈ s, i < n) ∧
    legalB (emptyBoard n) s = true ∧
    execB (emptyBoard n) s = doneBoard n ∧
    maxOnes (emptyBoard n) s ≤ p

theorem ReachIn.mono {n p t t' : Nat} (h : ReachIn n p t) (ht : t ≤ t') :
    ReachIn n p t' := by
  obtain ⟨s, hlen, hrange, hleg, hex, hpk⟩ := h
  exact ⟨s, Nat.le_trans hlen ht, hrange, hleg, hex, hpk⟩

-- ------------------------------------------------------------------
-- Padding: a schedule does not notice cells beyond its reach
-- ------------------------------------------------------------------

theorem nth_append_left (b c : Board) (i : Nat) (h : i < b.length) :
    nth (b ++ c) i = nth b i := by
  simp [nth, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem toggle_append_left (b c : Board) (i : Nat) (h : i < b.length) :
    toggle (b ++ c) i = toggle b i ++ c := by
  simp only [toggle, nth_append_left b c i h]
  exact List.set_append_left i _ h

theorem ones_append (b c : Board) : ones (b ++ c) = ones b + ones c := by
  simp [ones, List.count_append]

/-- Execution ignores the padding. -/
theorem execB_pad (c : Board) : ∀ (s : List Nat) (b : Board),
    (∀ i ∈ s, i < b.length) → execB (b ++ c) s = execB b s ++ c
  | [], _, _ => rfl
  | i :: rest, b, hr => by
      have hi : i < b.length := hr i (by simp)
      have hlen : (toggle b i).length = b.length := by
        simp [toggle, List.length_set]
      show execB (toggle (b ++ c) i) rest = _
      rw [toggle_append_left b c i hi]
      exact execB_pad c rest (toggle b i) (fun j hj => by
        rw [hlen]; exact hr j (List.mem_cons_of_mem _ hj))

/-- Legality ignores the padding. -/
theorem legalB_pad (c : Board) : ∀ (s : List Nat) (b : Board),
    (∀ i ∈ s, i < b.length) → legalB (b ++ c) s = legalB b s
  | [], _, _ => rfl
  | i :: rest, b, hr => by
      have hi : i < b.length := hr i (by simp)
      have hlen : (toggle b i).length = b.length := by
        simp [toggle, List.length_set]
      have hok : okMove (b ++ c) i = okMove b i := by
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · simp [okMove]
        · simp only [okMove]
          rw [nth_append_left b c (i - 1) (by omega)]
      show (okMove (b ++ c) i && legalB (toggle (b ++ c) i) rest)
        = (okMove b i && legalB (toggle b i) rest)
      rw [hok, toggle_append_left b c i hi,
        legalB_pad c rest (toggle b i) (fun j hj => by
          rw [hlen]; exact hr j (List.mem_cons_of_mem _ hj))]

/-- The peak only grows by the padding's own pebbles. -/
theorem maxOnes_pad (c : Board) : ∀ (s : List Nat) (b : Board),
    (∀ i ∈ s, i < b.length) →
      maxOnes (b ++ c) s = maxOnes b s + ones c
  | [], b, _ => by simp [maxOnes, ones_append]
  | i :: rest, b, hr => by
      have hi : i < b.length := hr i (by simp)
      have hlen : (toggle b i).length = b.length := by
        simp [toggle, List.length_set]
      show max (ones (b ++ c)) (maxOnes (toggle (b ++ c) i) rest) = _
      rw [toggle_append_left b c i hi, ones_append,
        maxOnes_pad c rest (toggle b i) (fun j hj => by
          rw [hlen]; exact hr j (List.mem_cons_of_mem _ hj))]
      show max (ones b + ones c) (maxOnes (toggle b i) rest + ones c)
        = max (ones b) (maxOnes (toggle b i) rest) + ones c
      omega

/-- The empty chain splits as a padded shorter chain. -/
theorem emptyBoard_split (m k : Nat) :
    emptyBoard (m + k) = emptyBoard m ++ emptyBoard k := by
  simp [emptyBoard, ← List.replicate_append_replicate]

/-- **PADDING.**  A schedule for the first `m` cells works unchanged on
a longer empty chain. -/
theorem reach_pad {m k p t : Nat} (h : ReachIn m p t) :
    ∃ s : List Nat, s.length ≤ t ∧ (∀ i ∈ s, i < m) ∧
      legalB (emptyBoard (m + k)) s = true ∧
      execB (emptyBoard (m + k)) s = doneBoard m ++ emptyBoard k ∧
      maxOnes (emptyBoard (m + k)) s ≤ p := by
  obtain ⟨s, hlen, hrange, hleg, hex, hpk⟩ := h
  have hrange' : ∀ i ∈ s, i < (emptyBoard m).length := by
    intro i hi; rw [emptyBoard_length]; exact hrange i hi
  refine ⟨s, hlen, hrange, ?_, ?_, ?_⟩
  · rw [emptyBoard_split, legalB_pad _ s _ hrange']; exact hleg
  · rw [emptyBoard_split, execB_pad _ s _ hrange', hex]
  · rw [emptyBoard_split, maxOnes_pad _ s _ hrange', ones_emptyBoard]
    simpa using hpk

-- ------------------------------------------------------------------
-- Shapes of the two distinguished boards
-- ------------------------------------------------------------------

@[simp] theorem doneBoard_length (n : Nat) : (doneBoard n).length = n := by
  simp [doneBoard]

/-- The finished chain is "empty, then one pebble". -/
theorem doneBoard_succ (j : Nat) : doneBoard (j + 1) = emptyBoard j ++ [true] := by
  simp only [doneBoard, emptyBoard, Nat.add_sub_cancel]
  rw [List.replicate_succ', List.set_append_right _ _ (by simp)]
  simp

theorem ones_doneBoard (j : Nat) : ones (doneBoard (j + 1)) = 1 := by
  rw [doneBoard_succ, ones_append, ones_emptyBoard]
  simp [ones]

/-- The pebble sits on the last cell, and padding on the right does not
move it. -/
theorem nth_doneBoard_last (j : Nat) (c : Board) :
    nth (doneBoard (j + 1) ++ c) j = true := by
  rw [doneBoard_succ, List.append_assoc]
  simp [nth, List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- Finishing a longer chain is finishing its tail. -/
theorem emptyBoard_append_doneBoard (m j : Nat) :
    emptyBoard m ++ doneBoard (j + 1) = doneBoard (m + j + 1) := by
  rw [doneBoard_succ, doneBoard_succ, emptyBoard_split, List.append_assoc]

-- ------------------------------------------------------------------
-- Knill's constructive half, at the level of the game
-- ------------------------------------------------------------------

/-- **THE COMPOSITION THEOREM** (Knill 1995, Thm 2.1, the `≤` half;
LAUR-95-2258 p. 5), as a statement about plays.

To pebble `m + k` cells with `S` pebbles: reach cell `m-1` with `S`
(`h1`), stand on it and reach the far end with the remaining `S-1` by a
*lifted* play (`h3`), then remove the foundation by running a play that
reaches `m` with `S-1` *backwards* (`h2`).  The peak never exceeds `S`
because the two later phases each carry exactly one pebble from another
phase — the foundation during the lift, the finished end during the
retreat.

In terms of costs this is `F(n,S) ≤ F(m,S) + F(n-m,S-1) + F(m,S-1)`,
the recursion whose solution `KnillUnique` identifies with `rowIter`. -/
theorem reach_compose {m k S t₁ t₂ t₃ : Nat} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hS : 1 ≤ S)
    (h1 : ReachIn m S t₁) (h3 : ReachIn k (S - 1) t₃)
    (h2 : ReachIn m (S - 1) t₂) :
    ReachIn (m + k) S (t₁ + t₃ + t₂) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨s₁, hlen1, hr1, hleg1, hex1, hpk1⟩ := h1
  obtain ⟨s₂, hlen2, hr2, hleg2, hex2, hpk2⟩ := h2
  obtain ⟨s₃, hlen3, hr3, hleg3, hex3, hpk3⟩ := h3
  have hr1' : ∀ i ∈ s₁, i < (emptyBoard (a + 1)).length := by
    intro i hi; rw [emptyBoard_length]; exact hr1 i hi
  -- phase 1: the short play, padded
  have hleg1' : legalB (emptyBoard (a + 1 + (j + 1))) s₁ = true := by
    rw [emptyBoard_split, legalB_pad _ _ _ hr1']; exact hleg1
  have hB1 : execB (emptyBoard (a + 1 + (j + 1))) s₁
      = doneBoard (a + 1) ++ emptyBoard (j + 1) := by
    rw [emptyBoard_split, execB_pad _ _ _ hr1', hex1]
  have hpk1' : maxOnes (emptyBoard (a + 1 + (j + 1))) s₁ ≤ S := by
    rw [emptyBoard_split, maxOnes_pad _ _ _ hr1', ones_emptyBoard]
    simpa using hpk1
  -- the board after phase 1, split at the cut
  have hdrop : (doneBoard (a + 1) ++ emptyBoard (j + 1)).drop (a + 1)
      = emptyBoard (j + 1) := by
    exact List.drop_left' (doneBoard_length (a + 1))
  have htake : (doneBoard (a + 1) ++ emptyBoard (j + 1)).take (a + 1)
      = doneBoard (a + 1) := by
    exact List.take_left' (doneBoard_length (a + 1))
  -- phase 2: the lifted play
  have hleg2' : legalB (doneBoard (a + 1) ++ emptyBoard (j + 1))
      (liftAbove (a + 1) s₃) = true := by
    refine legalB_liftAbove (a + 1) s₃ _ (Or.inr ?_) ?_
    · simpa using nth_doneBoard_last a (emptyBoard (j + 1))
    · rw [hdrop]; exact hleg3
  have hB2 : execB (doneBoard (a + 1) ++ emptyBoard (j + 1))
      (liftAbove (a + 1) s₃) = doneBoard (a + 1) ++ doneBoard (j + 1) := by
    have hd := execB_liftAbove_drop (a + 1) s₃
      (doneBoard (a + 1) ++ emptyBoard (j + 1))
    have ht := execB_liftAbove_take (a + 1) s₃
      (doneBoard (a + 1) ++ emptyBoard (j + 1))
    rw [hdrop, hex3] at hd
    rw [htake] at ht
    calc execB (doneBoard (a + 1) ++ emptyBoard (j + 1)) (liftAbove (a + 1) s₃)
        = (execB (doneBoard (a + 1) ++ emptyBoard (j + 1))
              (liftAbove (a + 1) s₃)).take (a + 1)
            ++ (execB (doneBoard (a + 1) ++ emptyBoard (j + 1))
              (liftAbove (a + 1) s₃)).drop (a + 1) :=
          (List.take_append_drop _ _).symm
      _ = doneBoard (a + 1) ++ doneBoard (j + 1) := by rw [ht, hd]
  have hpk2' : maxOnes (doneBoard (a + 1) ++ emptyBoard (j + 1))
      (liftAbove (a + 1) s₃) ≤ S := by
    have h := maxOnes_liftAbove (a + 1) s₃
      (doneBoard (a + 1) ++ emptyBoard (j + 1))
    rw [htake, hdrop, ones_doneBoard a] at h
    omega
  -- phase 3: the retreat, a reversed play
  have hrev_leg : legalB (doneBoard (a + 1)) s₂.reverse = true := by
    have h := legal_reverse (emptyBoard (a + 1)) s₂ hleg2
    rwa [hex2] at h
  have hrev_ex : execB (doneBoard (a + 1)) s₂.reverse = emptyBoard (a + 1) := by
    have h := exec_reverse_cancel (emptyBoard (a + 1)) s₂
    rwa [hex2] at h
  have hrev_pk : maxOnes (doneBoard (a + 1)) s₂.reverse ≤ S - 1 := by
    have h := maxOnes_reverse (emptyBoard (a + 1)) s₂
    rw [hex2] at h
    omega
  have hrrev : ∀ i ∈ s₂.reverse, i < (doneBoard (a + 1)).length := by
    intro i hi
    rw [doneBoard_length]
    exact hr2 i (by simpa using hi)
  have hleg3' : legalB (doneBoard (a + 1) ++ doneBoard (j + 1)) s₂.reverse
      = true := by
    rw [legalB_pad _ _ _ hrrev]; exact hrev_leg
  have hB3 : execB (doneBoard (a + 1) ++ doneBoard (j + 1)) s₂.reverse
      = doneBoard (a + 1 + (j + 1)) := by
    rw [execB_pad _ _ _ hrrev, hrev_ex]
    have : a + 1 + (j + 1) = a + 1 + j + 1 := by omega
    rw [this]
    exact emptyBoard_append_doneBoard (a + 1) j
  have hpk3' : maxOnes (doneBoard (a + 1) ++ doneBoard (j + 1)) s₂.reverse
      ≤ S := by
    rw [maxOnes_pad _ _ _ hrrev, ones_doneBoard j]
    omega
  -- assemble
  refine ⟨s₁ ++ liftAbove (a + 1) s₃ ++ s₂.reverse, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, liftAbove_length, List.length_reverse]
    omega
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · have := hr1 i hi; omega
      · obtain ⟨x, hx, rfl⟩ : ∃ x ∈ s₃, x + (a + 1) = i := by
          simpa [liftAbove] using hi
        have := hr3 x hx
        omega
    · have := hr2 i (by simpa using hi); omega
  · rw [legal_append, legal_append, exec_append, hB1, hleg1', hleg2', hB2,
      hleg3']
    simp
  · rw [exec_append, exec_append, hB1, hB2, hB3]
  · rw [maxOnes_append, maxOnes_append, exec_append, hB1, hB2]
    have h1 := hpk1'
    have h2 := hpk2'
    have h3 := hpk3'
    omega

-- ------------------------------------------------------------------
-- Tests: the predicate is inhabited, and the composition fires
-- ------------------------------------------------------------------

/-- One cell, one pebble, one move. -/
theorem reach_one : ReachIn 1 1 1 :=
  ⟨[0], by decide, by decide, by decide, by decide, by decide⟩

/-- Two cells with two pebbles in three moves, obtained from
`reach_compose` — the smallest instance of Knill's construction
(`F(2,2) ≤ F(1,2) + F(1,1) + F(1,1)`). -/
theorem reach_two : ReachIn 2 2 3 := by
  have h1 : ReachIn 1 2 1 := by
    obtain ⟨s, hlen, hr, hleg, hex, hpk⟩ := reach_one
    exact ⟨s, hlen, hr, hleg, hex, by omega⟩
  have h := reach_compose (m := 1) (k := 1) (S := 2) (by omega) (by omega)
    (by omega) h1 (by simpa using reach_one) (by simpa using reach_one)
  simpa using h

end RevPebbling.GameReach
