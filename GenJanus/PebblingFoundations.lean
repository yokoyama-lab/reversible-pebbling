import Std

/-!
# General formal foundations of the reversible pebble game on chains

Unlike the bounded `native_decide` results elsewhere, this file proves
GENERAL (unbounded) theorems about the clean-reach reversible pebble
game: boards are `List Bool`, a move toggles one cell, and a move on
cell `i` is legal iff `i = 0` or cell `i-1` is pebbled (cell 0 is
source-adjacent).

Main results:

* `legal_reverse` / `exec_reverse_cancel` / `maxOnes_reverse` — the
  time-reversal symmetry of the game, proved once and for all;
* `bennett_general` — Bennett's binary recursive schedule is legal,
  places exactly one pebble at the end of a `2^k` segment, and never
  holds more than `k+1` extra pebbles, for EVERY `k` and every ambient
  board satisfying the natural frame conditions;
* `reach_two_pow` — the achievability half of the reach
  characterisation: for every `p ≥ 1` a chain of length `2^(p-1)` can
  be cleanly reached with peak `p` (Bennett 1973/1989; the matching
  impossibility half, Knill 1995 Thm 2.3, is checked exhaustively in
  `PebblingTheory.lean` and remains future work as a general proof).
-/

namespace GenJanus.PebblingFoundations

abbrev Board := List Bool

def nth (b : Board) (i : Nat) : Bool := b.getD i false

def ones (b : Board) : Nat := b.count true

def toggle (b : Board) (i : Nat) : Board := b.set i (!(nth b i))

def okMove (b : Board) (i : Nat) : Bool := i == 0 || nth b (i - 1)

def execB (b : Board) (s : List Nat) : Board := s.foldl toggle b

def legalB : Board → List Nat → Bool
  | _, [] => true
  | b, i :: rest => okMove b i && legalB (toggle b i) rest

/-- Maximum pebble count over the whole trace (including start). -/
def maxOnes : Board → List Nat → Nat
  | b, [] => ones b
  | b, i :: rest => max (ones b) (maxOnes (toggle b i) rest)

-- ------------------------------------------------------------------
-- Small board lemmas (self-contained инductions)
-- ------------------------------------------------------------------

theorem set_ge_length (b : Board) (i : Nat) (v : Bool) (h : b.length ≤ i) :
    b.set i v = b := by
  induction b generalizing i with
  | nil => rfl
  | cons a t ih =>
      cases i with
      | zero => simp at h
      | succ j => simp [List.set, ih j (by simpa using h)]

theorem nth_ge_length (b : Board) (i : Nat) (h : b.length ≤ i) :
    nth b i = false := by
  induction b generalizing i with
  | nil => rfl
  | cons a t ih =>
      cases i with
      | zero => simp at h
      | succ j => simpa [nth] using ih j (by simpa using h)

theorem nth_set_eq (b : Board) (i : Nat) (v : Bool) (h : i < b.length) :
    nth (b.set i v) i = v := by
  induction b generalizing i with
  | nil => simp at h
  | cons a t ih =>
      cases i with
      | zero => rfl
      | succ j => simpa [nth, List.set] using ih j (by simpa using h)

theorem nth_set_ne (b : Board) (i j : Nat) (v : Bool) (h : i ≠ j) :
    nth (b.set i v) j = nth b j := by
  induction b generalizing i j with
  | nil => rfl
  | cons a t ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl h
          | succ _ => rfl
      | succ i' =>
          cases j with
          | zero => rfl
          | succ j' =>
              simpa [nth, List.set] using
                ih i' j' (fun hc => h (by simpa using congrArg Nat.succ hc))

theorem set_set_same (b : Board) (i : Nat) (v w : Bool) :
    (b.set i v).set i w = b.set i w := by
  induction b generalizing i with
  | nil => rfl
  | cons a t ih =>
      cases i with
      | zero => rfl
      | succ j => simp [List.set, ih]

theorem set_nth_self (b : Board) (i : Nat) : b.set i (nth b i) = b := by
  induction b generalizing i with
  | nil => rfl
  | cons a t ih =>
      cases i with
      | zero => rfl
      | succ j => exact congrArg (List.cons a) (ih j)

theorem set_comm (b : Board) (i j : Nat) (v w : Bool) (h : i ≠ j) :
    (b.set i v).set j w = (b.set j w).set i v := by
  induction b generalizing i j with
  | nil => rfl
  | cons a t ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl h
          | succ _ => rfl
      | succ i' =>
          cases j with
          | zero => rfl
          | succ j' =>
              simp [List.set,
                ih i' j' (fun hc => h (by simpa using congrArg Nat.succ hc))]

theorem length_set (b : Board) (i : Nat) (v : Bool) :
    (b.set i v).length = b.length := by
  simp

theorem ones_set (b : Board) (i : Nat) (v : Bool) (h : i < b.length) :
    ones (b.set i v) + (if nth b i then 1 else 0)
      = ones b + (if v then 1 else 0) := by
  induction b generalizing i with
  | nil => simp at h
  | cons a t ih =>
      cases i with
      | zero =>
          cases a <;> cases v <;> simp [ones, nth, List.count_cons] <;> omega
      | succ j =>
          have := ih j (by simpa using h)
          cases a <;> simp [ones, nth, List.set, List.count_cons] at this ⊢
            <;> omega

-- ------------------------------------------------------------------
-- Toggle and reversal symmetry
-- ------------------------------------------------------------------

theorem toggle_toggle (b : Board) (i : Nat) : toggle (toggle b i) i = b := by
  by_cases h : i < b.length
  · simp [toggle, nth_set_eq _ _ _ h, set_set_same, set_nth_self]
  · have hb := set_ge_length b i (!(nth b i)) (Nat.le_of_not_lt h)
    simp [toggle, hb]

theorem okMove_toggle_self (b : Board) (i : Nat) :
    okMove (toggle b i) i = okMove b i := by
  cases i with
  | zero => rfl
  | succ j =>
      have : nth (toggle b (j + 1)) j = nth b j := by
        by_cases h : j + 1 < b.length
        · exact nth_set_ne b (j + 1) j _ (by omega)
        · have := set_ge_length b (j + 1) (!(nth b (j + 1)))
            (Nat.le_of_not_lt h)
          simp [toggle, this]
      simp [okMove, this]

theorem exec_append (b : Board) (x y : List Nat) :
    execB b (x ++ y) = execB (execB b x) y := by
  simp [execB, List.foldl_append]

theorem legal_append (b : Board) (x y : List Nat) :
    legalB b (x ++ y) = (legalB b x && legalB (execB b x) y) := by
  induction x generalizing b with
  | nil => simp [legalB, execB]
  | cons i rest ih =>
      simp [legalB, execB, ih, Bool.and_assoc]

theorem exec_reverse_cancel (b : Board) (s : List Nat) :
    execB (execB b s) s.reverse = b := by
  induction s generalizing b with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.reverse_cons]
      have hx : execB b (i :: rest) = execB (toggle b i) rest := rfl
      rw [hx, exec_append, ih (toggle b i)]
      simp [execB, toggle_toggle]

theorem legal_reverse (b : Board) (s : List Nat)
    (h : legalB b s = true) : legalB (execB b s) s.reverse = true := by
  induction s generalizing b with
  | nil => simp [legalB]
  | cons i rest ih =>
      simp only [legalB, Bool.and_eq_true] at h
      simp only [List.reverse_cons]
      have hx : execB b (i :: rest) = execB (toggle b i) rest := rfl
      rw [hx, legal_append, ih (toggle b i) h.2, exec_reverse_cancel]
      simp [legalB, okMove_toggle_self, h.1]

theorem ones_le_maxOnes (b : Board) (s : List Nat) :
    ones b ≤ maxOnes b s := by
  cases s with
  | nil => exact Nat.le_refl _
  | cons i rest => exact Nat.le_max_left _ _

theorem maxOnes_append (b : Board) (x y : List Nat) :
    maxOnes b (x ++ y) = max (maxOnes b x) (maxOnes (execB b x) y) := by
  induction x generalizing b with
  | nil =>
      have h := ones_le_maxOnes b y
      simp only [List.nil_append, maxOnes]
      have hx : execB b [] = b := rfl
      rw [hx]
      omega
  | cons i rest ih =>
      have hx : execB b (i :: rest) = execB (toggle b i) rest := rfl
      simp only [List.cons_append, maxOnes, hx, ih]
      omega

theorem maxOnes_le_iff (b : Board) (s : List Nat) (p : Nat) :
    maxOnes b s ≤ p ↔ (ones b ≤ p ∧ maxOnes b s ≤ p) := by
  constructor
  · intro h
    refine ⟨?_, h⟩
    induction s generalizing b with
    | nil => simpa [maxOnes] using h
    | cons i rest _ => simp [maxOnes] at h; omega
  · exact fun h => h.2

theorem maxOnes_reverse (b : Board) (s : List Nat) :
    maxOnes (execB b s) s.reverse = maxOnes b s := by
  induction s generalizing b with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.reverse_cons]
      have hx : execB b (i :: rest) = execB (toggle b i) rest := rfl
      rw [hx, maxOnes_append, ih (toggle b i), exec_reverse_cancel]
      have h1 : maxOnes (toggle b i) [i]
          = max (ones (toggle b i)) (ones b) := by
        simp [maxOnes, toggle_toggle]
      rw [h1]
      have h2 := ones_le_maxOnes (toggle b i) rest
      simp only [maxOnes]
      omega

-- ------------------------------------------------------------------
-- Bennett's binary schedule: GENERAL correctness
-- ------------------------------------------------------------------

/-- Binary Bennett schedule for the segment [base, base + 2^k):
advance to the midpoint, advance the second half, uncompute the
midpoint.  Places a single pebble at base + 2^k - 1. -/
def bin (base : Nat) : Nat → List Nat
  | 0 => [base]
  | k + 1 =>
      bin base k ++ (bin (base + 2 ^ k) k ++ (bin base k).reverse)

theorem bennett_general : ∀ (k base : Nat) (b : Board),
    base + 2 ^ k ≤ b.length →
    (base = 0 ∨ nth b (base - 1) = true) →
    (∀ j, base ≤ j → j < base + 2 ^ k → nth b j = false) →
    legalB b (bin base k) = true ∧
    execB b (bin base k) = b.set (base + 2 ^ k - 1) true ∧
    maxOnes b (bin base k) ≤ ones b + (k + 1) := by
  intro k
  induction k with
  | zero =>
      intro base b hlen hpred hseg
      have hlen' : base + 1 ≤ b.length := by simpa using hlen
      have hm : base < b.length := by omega
      have hfalse : nth b base = false :=
        hseg base (Nat.le_refl _) (by simp)
      have hok : okMove b base = true := by
        cases hpred with
        | inl h => simp [okMove, h]
        | inr h => simp [okMove, h]
      have htog : toggle b base = b.set base true := by
        simp [toggle, hfalse]
      have hones : ones (b.set base true) = ones b + 1 := by
        have h0 := ones_set b base true hm
        rw [hfalse] at h0
        simpa using h0
      refine ⟨by simp [bin, legalB, hok],
              by simpa [bin, execB] using htog, ?_⟩
      have : maxOnes b (bin base 0) = max (ones b) (ones b + 1) := by
        simp [bin, maxOnes, htog, hones]
      rw [this]
      omega
  | succ k ih =>
      intro base b hlen hpred hseg
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
        rw [Nat.pow_succ]; omega
      have h2k : 0 < 2 ^ k := Nat.two_pow_pos k
      have hmlen : base + 2 ^ k - 1 < b.length := by omega
      have hMlen : base + 2 ^ (k + 1) - 1 < b.length := by omega
      have hA := ih base b (by omega) hpred
        (fun j h1 h2 => hseg j h1 (by omega))
      have hpredB : base + 2 ^ k = 0 ∨
          nth (b.set (base + 2 ^ k - 1) true) (base + 2 ^ k - 1) = true :=
        Or.inr (nth_set_eq b _ true hmlen)
      have hsegB : ∀ j, base + 2 ^ k ≤ j → j < base + 2 ^ k + 2 ^ k →
          nth (b.set (base + 2 ^ k - 1) true) j = false := fun j h1 h2 => by
        rw [nth_set_ne b _ j true (by omega)]
        exact hseg j (by omega) (by omega)
      have hB := ih (base + 2 ^ k) (b.set (base + 2 ^ k - 1) true)
        (by simp; omega) hpredB hsegB
      have hpredC : base = 0 ∨
          nth (b.set (base + 2 ^ (k + 1) - 1) true) (base - 1) = true := by
        cases hpred with
        | inl h => exact Or.inl h
        | inr h =>
            refine Or.inr ?_
            rw [nth_set_ne b _ (base - 1) true (by omega)]
            exact h
      have hsegC : ∀ j, base ≤ j → j < base + 2 ^ k →
          nth (b.set (base + 2 ^ (k + 1) - 1) true) j = false :=
        fun j h1 h2 => by
          rw [nth_set_ne b _ j true (by omega)]
          exact hseg j h1 (by omega)
      have hC := ih base (b.set (base + 2 ^ (k + 1) - 1) true)
        (by simp; omega) hpredC hsegC
      have hc0set : (b.set (base + 2 ^ (k + 1) - 1) true).set
            (base + 2 ^ k - 1) true
          = (b.set (base + 2 ^ k - 1) true).set
            (base + 2 ^ (k + 1) - 1) true :=
        set_comm b _ _ true true (by omega)
      have hexecC : execB (b.set (base + 2 ^ (k + 1) - 1) true)
            (bin base k)
          = (b.set (base + 2 ^ k - 1) true).set
            (base + 2 ^ (k + 1) - 1) true := by
        rw [hC.2.1, hc0set]
      have hMeq : base + 2 ^ k + 2 ^ k - 1 = base + 2 ^ (k + 1) - 1 := by
        omega
      have hexecB : execB (b.set (base + 2 ^ k - 1) true)
            (bin (base + 2 ^ k) k)
          = (b.set (base + 2 ^ k - 1) true).set
            (base + 2 ^ (k + 1) - 1) true := by
        rw [hB.2.1, hMeq]
      have honesb1 : ones (b.set (base + 2 ^ k - 1) true) = ones b + 1 := by
        have h0 := ones_set b (base + 2 ^ k - 1) true hmlen
        rw [hseg _ (by omega) (by omega)] at h0
        simpa using h0
      have honesc0 : ones (b.set (base + 2 ^ (k + 1) - 1) true)
          = ones b + 1 := by
        have h0 := ones_set b (base + 2 ^ (k + 1) - 1) true hMlen
        rw [hseg _ (by omega) (by omega)] at h0
        simpa using h0
      refine ⟨?_, ?_, ?_⟩
      · simp only [bin, legal_append, hA.1, hA.2.1, Bool.true_and]
        simp only [hB.1, Bool.true_and, hexecB]
        rw [← hexecC]
        simpa using legal_reverse _ (bin base k) hC.1
      · simp only [bin, exec_append, hA.2.1]
        rw [hexecB, ← hexecC, exec_reverse_cancel]
      · simp only [bin, maxOnes_append, exec_append, hA.2.1]
        rw [hexecB, ← hexecC, maxOnes_reverse]
        have p1 := hA.2.2
        have p2 := hB.2.2
        have p3 := hC.2.2
        rw [honesb1] at p2
        rw [honesc0] at p3
        omega

theorem nth_replicate (n j : Nat) :
    nth (List.replicate n false) j = false := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
      cases j with
      | zero => rfl
      | succ j' => simpa [nth, List.replicate] using ih j'

theorem ones_replicate (n : Nat) : ones (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [ones, List.replicate, List.count_cons] using ih

/-- GENERAL achievability half of the reach characterisation
(Bennett 1973/1989): a chain of length 2^(p-1) can be cleanly reached
with peak p pebbles, for every p ≥ 1. -/
theorem reach_two_pow (p : Nat) (hp : 1 ≤ p) :
    legalB (List.replicate (2 ^ (p - 1)) false) (bin 0 (p - 1)) = true ∧
    execB (List.replicate (2 ^ (p - 1)) false) (bin 0 (p - 1))
      = (List.replicate (2 ^ (p - 1)) false).set (2 ^ (p - 1) - 1) true ∧
    maxOnes (List.replicate (2 ^ (p - 1)) false) (bin 0 (p - 1)) ≤ p := by
  have h := bennett_general (p - 1) 0 (List.replicate (2 ^ (p - 1)) false)
    (by simp) (Or.inl rfl)
    (fun j _ _ => nth_replicate _ j)
  refine ⟨h.1, by simpa using h.2.1, ?_⟩
  have := h.2.2
  rw [ones_replicate] at this
  omega


-- ------------------------------------------------------------------
-- Variant bridge (constructive core): reverse-append a half-reach to
-- obtain a complete round trip with the SAME peak.  This is the
-- general `T ≤ 2·(half-reach)` direction of the reach/complete bridge.
-- ------------------------------------------------------------------

/-- For any legal computation `s` from `b`, the round trip
`s ++ s.reverse` is legal, returns to `b`, and has exactly the same peak
pebble count as `s`.  Appending the reverse of a minimal half-reach
(empty → some board with node n pebbled) thus yields a complete
computation (empty → covered → empty) of twice the length at no extra
space -- the constructive half of Kr\'alovi\v{c}'s symmetry
(Lemma 3.2). -/
theorem reverse_append_roundtrip (b : Board) (s : List Nat)
    (h : legalB b s = true) :
    legalB b (s ++ s.reverse) = true ∧
    execB b (s ++ s.reverse) = b ∧
    maxOnes b (s ++ s.reverse) = maxOnes b s := by
  refine ⟨?_, ?_, ?_⟩
  · rw [legal_append, h, Bool.true_and]
    exact legal_reverse b s h
  · rw [exec_append]; exact exec_reverse_cancel b s
  · rw [maxOnes_append, maxOnes_reverse, Nat.max_self]

end GenJanus.PebblingFoundations
