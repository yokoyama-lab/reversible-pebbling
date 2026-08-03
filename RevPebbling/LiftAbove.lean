import RevPebbling.PebblingFoundations

/-!
# Lifting a play onto a segment above a foundation (this work, route β)

`PebblingFoundations` has the *projection* `shiftAbove` (moves above a
cut, re-indexed down) with `execB_shiftAbove` / `legalB_shiftAbove`.
Those serve the impossibility direction.

Knill's Theorem 2.1 needs the opposite operation for its `≤` half (the
constructive one, p.5 of LAUR-95-2258): a play on a short chain has to
be *lifted* onto the segment sitting above an already-pebbled
foundation, so that

  s₁ (reach m with S) ++ lift m s₃ (reach n−m from m with S−1)
                       ++ reverse s₂ (unreach m with S−1)

is a play on the long chain.  This file provides that primitive and its
three basic laws (execution, legality, peak).  `bennett_general`
already uses exactly this shape for the binary schedule — its `base`
argument and its `(base = 0 ∨ nth b (base−1) = true)` precondition are
the special case where the lifted play is `bin` — so the laws here are
the general version of what makes that theorem work.
-/

namespace RevPebbling.LiftAbove

open RevPebbling.PebblingFoundations

/-- Re-index a play so that cell `0` becomes cell `base`. -/
def liftAbove (base : Nat) (s : List Nat) : List Nat := s.map (· + base)

@[simp] theorem liftAbove_nil (base : Nat) : liftAbove base [] = [] := rfl

@[simp] theorem liftAbove_cons (base i : Nat) (s : List Nat) :
    liftAbove base (i :: s) = (i + base) :: liftAbove base s := rfl

@[simp] theorem liftAbove_length (base : Nat) (s : List Nat) :
    (liftAbove base s).length = s.length := by
  simp [liftAbove]

theorem liftAbove_append (base : Nat) (s t : List Nat) :
    liftAbove base (s ++ t) = liftAbove base s ++ liftAbove base t := by
  simp [liftAbove]

/-- Setting a cell at or above the cut, seen from above the cut. -/
theorem drop_set_add (b : Board) (base i : Nat) (v : Bool) :
    (b.set (i + base) v).drop base = (b.drop base).set i v := by
  induction base generalizing b i with
  | zero => simp
  | succ base ih =>
      cases b with
      | nil => simp
      | cons hd tl =>
          have h : i + (base + 1) = (i + base) + 1 := by omega
          simp only [h, List.set_cons_succ, List.drop_succ_cons]
          exact ih tl i

/-- Reading a cell at or above the cut, seen from above the cut. -/
theorem nth_drop_add (b : Board) (base i : Nat) :
    nth (b.drop base) i = nth b (i + base) := by
  simp [nth, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]

/-- Toggling above the cut commutes with dropping. -/
theorem drop_toggle_add (b : Board) (base i : Nat) :
    (toggle b (i + base)).drop base = toggle (b.drop base) i := by
  simp only [toggle, drop_set_add, nth_drop_add]

/-- **Execution law.**  Above the foundation, a lifted play does what
the original play does. -/
theorem execB_liftAbove_drop (base : Nat) :
    ∀ (s : List Nat) (b : Board),
      (execB b (liftAbove base s)).drop base = execB (b.drop base) s
  | [], _ => rfl
  | i :: rest, b => by
      show (execB (toggle b (i + base)) (liftAbove base rest)).drop base = _
      rw [execB_liftAbove_drop base rest (toggle b (i + base)),
        drop_toggle_add]
      rfl

/-- Setting a cell at or above the cut leaves the prefix alone. -/
theorem take_set_add (b : Board) (base i : Nat) (v : Bool) :
    (b.set (i + base) v).take base = b.take base := by
  induction base generalizing b i with
  | zero => simp
  | succ base ih =>
      cases b with
      | nil => simp
      | cons hd tl =>
          have h : i + (base + 1) = (i + base) + 1 := by omega
          simp only [h, List.set_cons_succ, List.take_succ_cons]
          rw [ih tl i]

/-- Toggling above the cut leaves the prefix alone. -/
theorem take_toggle_add (b : Board) (base i : Nat) :
    (toggle b (i + base)).take base = b.take base := by
  simp only [toggle]
  exact take_set_add b base i _

/-- **Foundation law.**  A lifted play never touches the cells below
the cut, so the foundation it stands on survives. -/
theorem execB_liftAbove_take (base : Nat) :
    ∀ (s : List Nat) (b : Board),
      (execB b (liftAbove base s)).take base = b.take base
  | [], _ => rfl
  | i :: rest, b => by
      show (execB (toggle b (i + base)) (liftAbove base rest)).take base = _
      rw [execB_liftAbove_take base rest (toggle b (i + base)),
        take_toggle_add]

/-- A toggle at or above the cut does not disturb any cell below it.
This is what keeps the foundation alive during the lifted play. -/
theorem nth_toggle_below (b : Board) (base i j : Nat) (hj : j < base) :
    nth (toggle b (i + base)) j = nth b j := by
  have hne : i + base ≠ j := by omega
  simp only [toggle, nth, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne hne]

/-- **Legality law.**  A lifted play is legal provided the foundation
cell just below the cut carries a pebble (or the cut is at the very
left end).  The foundation is what licenses the play's first move,
which in the short chain was free. -/
theorem legalB_liftAbove (base : Nat) :
    ∀ (s : List Nat) (b : Board),
      (base = 0 ∨ nth b (base - 1) = true) →
      legalB (b.drop base) s = true →
      legalB b (liftAbove base s) = true
  | [], _, _, _ => rfl
  | i :: rest, b, hbase, hleg => by
      have hok2 : okMove (b.drop base) i = true ∧
          legalB (toggle (b.drop base) i) rest = true := by
        simpa [legalB, Bool.and_eq_true] using hleg
      have hok : okMove b (i + base) = true := by
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · simp only [Nat.zero_add, okMove, Bool.or_eq_true, beq_iff_eq]
          rcases hbase with h | h
          · left; exact h
          · right; exact h
        · have h1 : nth (b.drop base) (i - 1) = true := by
            have hm := hok2.1
            simp only [okMove, Bool.or_eq_true, beq_iff_eq] at hm
            rcases hm with h | h
            · omega
            · exact h
          rw [nth_drop_add] at h1
          have h2 : i - 1 + base = i + base - 1 := by omega
          rw [h2] at h1
          simp only [okMove, Bool.or_eq_true]
          right; exact h1
      have hbase' : base = 0 ∨ nth (toggle b (i + base)) (base - 1) = true := by
        rcases Nat.eq_zero_or_pos base with hb | hb
        · left; exact hb
        · rcases hbase with h | h
          · left; exact h
          · right
            rw [nth_toggle_below b base i (base - 1) (by omega)]
            exact h
      have hleg' : legalB ((toggle b (i + base)).drop base) rest = true := by
        rw [drop_toggle_add]; exact hok2.2
      show (okMove b (i + base) &&
        legalB (toggle b (i + base)) (liftAbove base rest)) = true
      rw [hok, Bool.true_and]
      exact legalB_liftAbove base rest (toggle b (i + base)) hbase' hleg'

/-- **Peak law.**  The pebbles below the cut are carried along as a
constant offset, so the peak of a lifted play splits into the standing
cost of the foundation plus the peak of the original play.  This is the
accounting behind "the base is shared", i.e. behind the `p + q - 1` of
the submultiplicativity lemma. -/
theorem maxOnes_liftAbove (base : Nat) :
    ∀ (s : List Nat) (b : Board),
      maxOnes b (liftAbove base s)
        ≤ ones (b.take base) + maxOnes (b.drop base) s
  | [], b => by
      have hb := ones_take_drop b base
      simp only [liftAbove_nil, maxOnes]
      omega
  | i :: rest, b => by
      have ih := maxOnes_liftAbove base rest (toggle b (i + base))
      rw [take_toggle_add, drop_toggle_add] at ih
      have hb : ones (b.take base) + ones (b.drop base) = ones b :=
        ones_take_drop b base
      show max (ones b) (maxOnes (toggle b (i + base)) (liftAbove base rest))
        ≤ ones (b.take base) + max (ones (b.drop base))
            (maxOnes (toggle (b.drop base) i) rest)
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · have := Nat.le_max_left (ones (b.drop base))
          (maxOnes (toggle (b.drop base) i) rest)
        omega
      · have := Nat.le_max_right (ones (b.drop base))
          (maxOnes (toggle (b.drop base) i) rest)
        omega

end RevPebbling.LiftAbove
