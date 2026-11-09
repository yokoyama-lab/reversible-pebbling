import ErasurePebbling.Basic

/-!
# Boards given by a characteristic function

`mk n f = (List.range n).map f` is the board of length `n` whose cell
`i` carries a pebble iff `f i`.  Every board that the explicit
constructions of this development pass through is of this form, and
the lemmas here let toggles, pebble counts and availability be read
off `f` pointwise, so that the case analyses reduce to `omega`.
-/

namespace ErasurePebbling

open RevPebbling.PebblingFoundations

def mk (n : Nat) (f : Nat → Bool) : Board := (List.range n).map f

@[simp] theorem length_mk (n : Nat) (f : Nat → Bool) : (mk n f).length = n := by
  simp [mk]

@[simp] theorem mk_zero (f : Nat → Bool) : mk 0 f = [] := rfl

@[simp] theorem ones_nil : ones [] = 0 := rfl

theorem getElem?_mk (n : Nat) (f : Nat → Bool) (i : Nat) :
    (mk n f)[i]? = if i < n then some (f i) else none := by
  simp [mk, List.getElem?_map]
  split <;> simp_all

theorem nth_mk (n : Nat) (f : Nat → Bool) (i : Nat) :
    nth (mk n f) i = if i < n then f i else false := by
  rw [nth, List.getD_eq_getElem?_getD, getElem?_mk]
  split <;> rfl

theorem nth_mk_of_lt {n : Nat} {f : Nat → Bool} {i : Nat} (h : i < n) :
    nth (mk n f) i = f i := by
  rw [nth_mk, if_pos h]

theorem mk_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i, i < n → f i = g i) :
    mk n f = mk n g := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_mk, getElem?_mk]
  split
  · rw [h i ‹_›]
  · rfl

/-- Pointwise description of a toggle. -/
theorem toggle_mk {n : Nat} (f : Nat → Bool) {i : Nat} (hi : i < n) :
    toggle (mk n f) i = mk n (fun j => if j = i then !f i else f j) := by
  apply List.ext_getElem?
  intro j
  rw [toggle, nth_mk_of_lt hi, List.getElem?_set, getElem?_mk, getElem?_mk]
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [hj, Ne.symm hj]

theorem mk_succ (n : Nat) (f : Nat → Bool) : mk (n + 1) f = mk n f ++ [f n] := by
  simp [mk, List.range_succ]

theorem ones_append (x y : Board) : ones (x ++ y) = ones x + ones y := by
  simp [ones, List.count_append]

theorem ones_mk_succ (n : Nat) (f : Nat → Bool) :
    ones (mk (n + 1) f) = ones (mk n f) + (if f n then 1 else 0) := by
  have h : ones [f n] = if f n then 1 else 0 := by cases f n <;> rfl
  rw [mk_succ, ones_append, h]

theorem ones_mk_zero (f : Nat → Bool) : ones (mk 0 f) = 0 := rfl

theorem empty_eq_mk (n : Nat) : empty n = mk n (fun _ => false) := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_mk, empty, List.getElem?_replicate]

theorem target_eq_mk (n : Nat) (hn : 1 ≤ n) : target n = mk n (fun i => decide (i = n - 1)) := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_mk, target]
  by_cases h : i = n - 1
  · subst h
    have h1 : n - 1 < n := by omega
    simp [List.getElem?_set, h1]
  · simp [h, List.getElem?_replicate, Ne.symm h]

/-- Pebble count of a run `[s, s+a)`. -/
theorem ones_run (n s a : Nat) :
    ones (mk n (fun i => decide (s ≤ i ∧ i < s + a))) = min n (s + a) - min n s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ones_mk_succ, ih]
      by_cases h : s ≤ n ∧ n < s + a
      · rw [if_pos (by simpa using h)]; omega
      · rw [if_neg (by simpa using h)]; omega

/-- Adding one isolated cell `t` to a characteristic function. -/
theorem ones_or_single (n : Nat) (f : Nat → Bool) (t : Nat) :
    ones (mk n (fun i => f i || decide (i = t))) =
      ones (mk n f) + (if t < n ∧ f t = false then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ones_mk_succ, ones_mk_succ, ih]
      by_cases ht : n = t
      · subst ht
        cases h : f n <;> simp [h]
      · have this : (decide (n = t)) = false := by simpa using ht
        simp only [this, Bool.or_false]
        by_cases hlt : t < n
        · by_cases hft : f t = false
          · have e1 : ((if t < n ∧ f t = false then 1 else 0 : Nat)) = 1 := if_pos ⟨hlt, hft⟩
            have e2 : ((if t < n + 1 ∧ f t = false then 1 else 0 : Nat)) = 1 :=
              if_pos ⟨by omega, hft⟩
            rw [e1, e2]; split <;> omega
          · have e1 : ((if t < n ∧ f t = false then 1 else 0 : Nat)) = 0 :=
              if_neg (fun h => hft h.2)
            have e2 : ((if t < n + 1 ∧ f t = false then 1 else 0 : Nat)) = 0 :=
              if_neg (fun h => hft h.2)
            rw [e1, e2]; split <;> omega
        · have e1 : ((if t < n ∧ f t = false then 1 else 0 : Nat)) = 0 :=
            if_neg (fun h => hlt h.1)
          have e2 : ((if t < n + 1 ∧ f t = false then 1 else 0 : Nat)) = 0 :=
            if_neg (fun h => by have := h.1; omega)
          rw [e1, e2]; split <;> omega

theorem ones_mk_le_of_imp {n : Nat} {f g : Nat → Bool}
    (h : ∀ i, i < n → f i = true → g i = true) : ones (mk n f) ≤ ones (mk n g) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ones_mk_succ, ones_mk_succ]
      have ih' := ih (fun i hi => h i (by omega))
      by_cases hf : f n = true
      · rw [if_pos hf, if_pos (h n (by omega) hf)]; omega
      · rw [if_neg hf]; omega

/-- Pebble count of a board `mk` never exceeds the length. -/
theorem ones_mk_le (n : Nat) (f : Nat → Bool) : ones (mk n f) ≤ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [ones_mk_succ]; split <;> omega

/-- Availability in a `mk` board. -/
theorem okMove_mk (n : Nat) (f : Nat → Bool) (i : Nat) :
    okMove (mk n f) i = (i == 0 || (if i - 1 < n then f (i - 1) else false)) := by
  rw [okMove, nth_mk]

end ErasurePebbling
