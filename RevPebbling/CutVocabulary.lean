import RevPebbling.PeakRestriction

/-!
# The vocabulary of a trajectory (this work, link (1), `≥` side, step (C))

Knill's `≥` half names four things about an optimal play and then argues
about them: the times `t_b`, `t_e` bounding a window, the quantity
`m(S,t)` — the lowest pebbled cell at time `t` — and the time `t_m` at
which `m` is largest **inside the window**.  This module gives those
names to the artifact:

* `loAt n s k` — the lowest pebbled cell at time `k` (Knill's `m(S,t)`),
  `0` when the board is empty;
* `window a b` — the times `k` with `a ≤ k ≤ b`;
* `cutAt n s a b` — the largest `loAt` over that window (Knill's `m`);
* `cutTime n s a b` — the first time in the window attaining it (`t_m`).

The point of the window is that `midX`, the artifact's existing "middle
vertex", takes the maximum over the *whole* trace.  On a play that
cleanly reaches the top cell the lowest pebble is eventually `n - 1`, so
`midX = n - 1` and cutting there leaves nothing above: the recursion
makes no progress.  Restricting to a window is what keeps the cut cell
usable, and `cutAt_mono` records that a narrower window never cuts
higher.

The payoff is `maxOnes_shiftAbove_cutAt`: combined with step (B)
(`PeakRestriction`) the cut cell is now **constructed** rather than
hypothesised — for any play and any time `a`, cutting at `cutAt n s 0 a`
drops the peak of the part above the cut by one, with no side condition.

`cutAt_univ` checks the vocabulary against the existing one: over the
whole trace `cutAt` *is* `midX`.
-/

namespace RevPebbling.CutVocabulary

open RevPebbling.PebblingFoundations

-- ------------------------------------------------------------------
-- Length bookkeeping: a play never changes the width of the board.
-- ------------------------------------------------------------------

theorem toggle_length (b : Board) (i : Nat) : (toggle b i).length = b.length := by
  simp [toggle]

theorem execB_length : ∀ (b : Board) (s : List Nat),
    (execB b s).length = b.length
  | _, [] => rfl
  | b, i :: rest => by
      show (execB (toggle b i) rest).length = b.length
      rw [execB_length (toggle b i) rest, toggle_length]

@[simp] theorem cfg_length (n : Nat) (s : List Nat) (k : Nat) :
    (cfg n s k).length = n := by
  unfold cfg
  rw [execB_length]
  simp

-- ------------------------------------------------------------------
-- The vocabulary.
-- ------------------------------------------------------------------

/-- Knill's `m(S,t)`: the lowest pebbled cell at time `k`, or `0` if the
board is empty at that time. -/
def loAt (n : Nat) (s : List Nat) (k : Nat) : Nat :=
  (firstOn (cfg n s k)).getD 0

/-- The times `k` with `a ≤ k ≤ b`. -/
def window (a b : Nat) : List Nat :=
  (List.range (b + 1 - a)).map (fun i => a + i)

/-- Knill's `m`: the largest lowest-pebble index over the window
`[a, b]`.  Unlike `midX` this is *windowed*, which is what keeps it
strictly inside the board on a play that reaches the top. -/
def cutAt (n : Nat) (s : List Nat) (a b : Nat) : Nat :=
  natMax ((window a b).map (loAt n s))

/-- Knill's `t_m`: the first time of the window at which `cutAt` is
attained.  Meaningful when `cutAt ≠ 0`; see `cutTime_spec`. -/
def cutTime (n : Nat) (s : List Nat) (a b : Nat) : Nat :=
  ((window a b).find? (fun k => decide (loAt n s k = cutAt n s a b))).getD a

theorem mem_window {a b k : Nat} : k ∈ window a b ↔ a ≤ k ∧ k ≤ b := by
  simp only [window, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨k - a, by omega, by omega⟩

-- ------------------------------------------------------------------
-- What the window maximum does.
-- ------------------------------------------------------------------

theorem loAt_le_cutAt {n a b k : Nat} {s : List Nat}
    (h1 : a ≤ k) (h2 : k ≤ b) : loAt n s k ≤ cutAt n s a b := by
  apply le_natMax_of_mem
  exact List.mem_map.mpr ⟨k, mem_window.mpr ⟨h1, h2⟩, rfl⟩

/-- **THE CUT CELL DOMINATES ITS WINDOW.**  This is exactly the shape of
hypothesis that step (B) (`PeakRestriction.maxOnes_shiftAbove_le_window`)
consumes. -/
theorem cutAt_dominates {n a b : Nat} {s : List Nat} :
    ∀ k w, a ≤ k → k ≤ b → firstOn (cfg n s k) = some w → w ≤ cutAt n s a b := by
  intro k w h1 h2 hf
  have h := loAt_le_cutAt (n := n) (s := s) h1 h2
  unfold loAt at h
  rw [hf] at h
  simpa using h

theorem cutAt_attained (n : Nat) (s : List Nat) (a b : Nat) :
    cutAt n s a b = 0 ∨
      ∃ k, a ≤ k ∧ k ≤ b ∧ loAt n s k = cutAt n s a b := by
  rcases natMax_attained ((window a b).map (loAt n s)) with h0 | hmem
  · exact Or.inl h0
  · obtain ⟨k, hk, hval⟩ := List.mem_map.mp hmem
    obtain ⟨h1, h2⟩ := mem_window.mp hk
    exact Or.inr ⟨k, h1, h2, hval⟩

/-- `cutTime` really is a time of the window attaining `cutAt`. -/
theorem cutTime_spec {n a b : Nat} {s : List Nat} (h : cutAt n s a b ≠ 0) :
    a ≤ cutTime n s a b ∧ cutTime n s a b ≤ b
      ∧ loAt n s (cutTime n s a b) = cutAt n s a b := by
  rcases cutAt_attained n s a b with h0 | ⟨k, hk1, hk2, hkv⟩
  · exact absurd h0 h
  cases hfind : (window a b).find?
      (fun j => decide (loAt n s j = cutAt n s a b)) with
  | none =>
      exfalso
      have hno := List.find?_eq_none.mp hfind k (mem_window.mpr ⟨hk1, hk2⟩)
      simp [hkv] at hno
  | some j =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hp := List.find?_some hfind
      obtain ⟨h1, h2⟩ := mem_window.mp hmem
      have hct : cutTime n s a b = j := by unfold cutTime; rw [hfind]; rfl
      rw [hct]
      exact ⟨h1, h2, by simpa using hp⟩

-- ------------------------------------------------------------------
-- The cut cell stays inside the board, and shrinks with the window.
-- ------------------------------------------------------------------

theorem natMax_lt {l : List Nat} {c : Nat} (hc : 0 < c)
    (h : ∀ x ∈ l, x < c) : natMax l < c := by
  rcases natMax_attained l with h0 | hmem
  · omega
  · exact h _ hmem

theorem loAt_lt {n : Nat} (hn : 0 < n) (s : List Nat) (k : Nat) :
    loAt n s k < n := by
  unfold loAt
  cases hf : firstOn (cfg n s k) with
  | none => simpa [hf] using hn
  | some w =>
      obtain ⟨hon, _⟩ := firstOn_spec _ w hf
      have hw := nth_true_lt_length hon
      rw [cfg_length] at hw
      simpa [hf] using hw

/-- The cut cell is a cell of the board. -/
theorem cutAt_lt {n : Nat} (hn : 0 < n) (s : List Nat) (a b : Nat) :
    cutAt n s a b < n := by
  refine natMax_lt hn ?_
  intro x hx
  obtain ⟨k, _, hkv⟩ := List.mem_map.mp hx
  rw [← hkv]
  exact loAt_lt hn s k

/-- **A NARROWER WINDOW NEVER CUTS HIGHER.**  This is why the window
matters: shrinking it can only lower the cut cell. -/
theorem cutAt_mono {n : Nat} {s : List Nat} {a b a' b' : Nat}
    (h1 : a' ≤ a) (h2 : b ≤ b') : cutAt n s a b ≤ cutAt n s a' b' := by
  rcases cutAt_attained n s a b with h0 | ⟨k, hk1, hk2, hkv⟩
  · omega
  · rw [← hkv]; exact loAt_le_cutAt (by omega) (by omega)

/-- The vocabulary agrees with the existing one: over the whole trace the
windowed maximum is the artifact's middle vertex. -/
theorem cutAt_univ (n : Nat) (s : List Nat) :
    cutAt n s 0 s.length = midX n s := by
  unfold cutAt midX loAt window
  simp

-- ------------------------------------------------------------------
-- The payoff: step (B) with the cut cell constructed rather than given.
-- ------------------------------------------------------------------

/-- **THE CUT IS CONSTRUCTIVE.**  For any play and any time `a`, cutting
at `cutAt n s 0 a` drops the peak of the part above the cut by one — no
side condition, no dominating cell supplied from outside.  This is step
(B) ∘ step (C). -/
theorem maxOnes_shiftAbove_cutAt {n P a : Nat} {s : List Nat}
    (hpeak : maxOnes (List.replicate n false) (s.take a) ≤ P + 1) :
    maxOnes (List.replicate (n - (cutAt n s 0 a + 1)) false)
      (shiftAbove (cutAt n s 0 a) (s.take a)) ≤ P :=
  PeakRestriction.maxOnes_shiftAbove_le_window hpeak
    (fun k w hk hf => cutAt_dominates k w (Nat.zero_le _) hk hf)

end RevPebbling.CutVocabulary
