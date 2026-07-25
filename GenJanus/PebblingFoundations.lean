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
  be cleanly reached with peak `p` (Bennett 1973/1989);
* `complete_bound` / `reach_impossible_general` — the matching
  impossibility half (Knill 1995 Thm 2.3), fully general: a complete
  computation with peak P covers at most 2^P - 1 cells
  (middle-vertex induction through the unconditional restriction
  lemmas), hence a clean reach of cell v with peak p has
  v + 1 ≤ 2^(p-1).  Together the two halves characterise the game
  exactly: reach(p) = 2^(p-1).
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


-- ------------------------------------------------------------------
-- Prefix coverage and roundtrip completeness (this work, 追記20):
-- entry infrastructure for the general impossibility side of
-- Knill Thm 2.3.  Roadmap (Královič Lemma 4.2/4.3 adapted to clean
-- reach; see notes/research-plan 追記20):
--   (a) prefix coverage: a legal computation that ever pebbles v
--       from a v-empty prefix must ever pebble every j ≤ v  [PROVED]
--   (b) roundtrip: a clean reach K yields the complete computation
--       K ++ rev(K) with the same peak, covering all of 1..n [PROVED]
--   (c) middle-vertex induction: any complete computation of Ch(m)
--       with peak ≤ p has m ≤ 2^p - 1                      [future]
--   (d) corollary via the junction board {n} forcing the middle
--       vertex to n: clean reach n with peak p ⇒ n ≤ 2^{p-1} [future]
-- ------------------------------------------------------------------

/-- Node v is pebbled at some point (including the start) of the
trace of `s` from `b`. -/
def everOn (b : Board) (s : List Nat) (v : Nat) : Prop :=
  ∃ k, nth (execB b (s.take k)) v = true

theorem everOn_start {b : Board} {s : List Nat} {v : Nat}
    (h : nth b v = true) : everOn b s v :=
  ⟨0, by simpa [execB] using h⟩

theorem everOn_cons {b : Board} {i : Nat} {s : List Nat} {v : Nat}
    (h : everOn (toggle b i) s v) : everOn b (i :: s) v := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by simpa [execB] using hk⟩

/-- Single descent step: if v was unpebbled at the start and is ever
pebbled, then (unless v = 0) node v-1 is also ever pebbled. -/
theorem everOn_descend :
    ∀ (s : List Nat) (b : Board) (v : Nat), legalB b s = true →
      nth b v = false → everOn b s v → v = 0 ∨ everOn b s (v - 1) := by
  intro s
  induction s with
  | nil =>
      intro b v _ hb hev
      obtain ⟨k, hk⟩ := hev
      simp [execB] at hk
      rw [hb] at hk
      exact absurd hk (by simp)
  | cons i rest ih =>
      intro b v hleg hb hev
      have hok : okMove b i = true ∧ legalB (toggle b i) rest = true := by
        simpa [legalB, Bool.and_eq_true] using hleg
      by_cases hiv : i = v
      · subst hiv
        rcases (by simpa [okMove, Bool.or_eq_true] using hok.1 :
            (i == 0) = true ∨ nth b (i - 1) = true) with h0 | hprev
        · exact Or.inl (by simpa using h0)
        · exact Or.inr (everOn_start hprev)
      · have hb' : nth (toggle b i) v = false := by
          rw [show nth (toggle b i) v = nth b v from
            nth_set_ne b i v _ hiv]
          exact hb
        have hev' : everOn (toggle b i) rest v := by
          obtain ⟨k, hk⟩ := hev
          match k with
          | 0 =>
              simp [execB] at hk
              rw [hb] at hk
              exact absurd hk (by simp)
          | k + 1 =>
              exact ⟨k, by simpa [execB] using hk⟩
        rcases ih (toggle b i) v hok.2 hb' hev' with h0 | hcov
        · exact Or.inl h0
        · exact Or.inr (everOn_cons hcov)

/-- PREFIX COVERAGE: from the empty board, a legal computation that
ever pebbles v ever pebbles every j ≤ v. -/
theorem coverage (n : Nat) (s : List Nat) (v : Nat)
    (hleg : legalB (List.replicate n false) s = true)
    (hv : everOn (List.replicate n false) s v) :
    ∀ j, j ≤ v → everOn (List.replicate n false) s j := by
  induction v with
  | zero =>
      intro j hj
      have : j = 0 := by omega
      subst this
      exact hv
  | succ v ihv =>
      intro j hj
      have hstep := everOn_descend s (List.replicate n false) (v + 1)
        hleg (nth_replicate n (v + 1)) hv
      rcases hstep with h0 | hcov
      · omega
      · simp at hcov
        rcases Nat.lt_or_ge j (v + 1) with hlt | hge
        · exact ihv hcov j (by omega)
        · have : j = v + 1 := by omega
          subst this
          exact hv

/-- everOn is monotone under appending further moves. -/
theorem everOn_append_left {b : Board} {s t : List Nat} {v : Nat}
    (h : everOn b s v) : everOn b (s ++ t) v := by
  obtain ⟨k, hk⟩ := h
  refine ⟨min k s.length, ?_⟩
  rw [List.take_append_of_le_length (Nat.min_le_right k s.length)]
  rcases Nat.le_total k s.length with hle | hge
  · rwa [Nat.min_eq_left hle]
  · rw [Nat.min_eq_right hge, List.take_of_length_le (Nat.le_refl _)]
    rwa [List.take_of_length_le hge] at hk

/-- ROUNDTRIP COMPLETENESS: a legal computation from the empty board
that ends with node v pebbled yields, by appending its own reverse, a
COMPLETE computation -- legal, returning to empty, covering every
node ≤ v -- with exactly the same peak. -/
theorem roundtrip_complete (n : Nat) (s : List Nat) (v : Nat)
    (hleg : legalB (List.replicate n false) s = true)
    (hend : nth (execB (List.replicate n false) s) v = true) :
    legalB (List.replicate n false) (s ++ s.reverse) = true ∧
    execB (List.replicate n false) (s ++ s.reverse) =
      List.replicate n false ∧
    maxOnes (List.replicate n false) (s ++ s.reverse) =
      maxOnes (List.replicate n false) s ∧
    (∀ j, j ≤ v → everOn (List.replicate n false) (s ++ s.reverse) j) := by
  obtain ⟨h1, h2, h3⟩ := reverse_append_roundtrip _ s hleg
  refine ⟨h1, h2, h3, ?_⟩
  intro j hj
  have hv : everOn (List.replicate n false) s v :=
    ⟨s.length, by simpa [List.take_of_length_le (Nat.le_refl _)] using hend⟩
  exact everOn_append_left (coverage n s v hleg hv j hj)

-- ------------------------------------------------------------------
-- Restriction lemmas (roadmap step (c), 追記31): a legal computation
-- restricts to the cells above x (moves > x, shifted so that x+1
-- becomes the new free left end) and to the cells below x (moves < x)
-- UNCONDITIONALLY: legality, execution, and coverage all commute with
-- the restriction.  These are the workhorses for the middle-vertex
-- induction of the general impossibility side of Knill Thm 2.3.
-- ------------------------------------------------------------------

/-- Moves strictly above x, re-indexed so cell x+1 becomes cell 0. -/
def shiftAbove (x : Nat) (s : List Nat) : List Nat :=
  (s.filter (fun i => decide (x < i))).map (fun i => i - (x + 1))

/-- Moves strictly below x. -/
def keepBelow (x : Nat) (s : List Nat) : List Nat :=
  s.filter (fun i => decide (i < x))

theorem drop_set_lt (b : Board) (m i : Nat) (v : Bool) (h : i < m) :
    (b.set i v).drop m = b.drop m := by
  induction b generalizing m i with
  | nil => rfl
  | cons a t ih =>
      cases m with
      | zero => omega
      | succ m' =>
          cases i with
          | zero => rfl
          | succ i' => simpa [List.set] using ih m' i' (by omega)

theorem drop_set_ge (b : Board) (m i : Nat) (v : Bool) (h : m ≤ i) :
    (b.set i v).drop m = (b.drop m).set (i - m) v := by
  induction b generalizing m i with
  | nil => simp
  | cons a t ih =>
      cases m with
      | zero => simp
      | succ m' =>
          cases i with
          | zero => omega
          | succ i' =>
              have := ih m' i' (by omega)
              simpa [List.set, Nat.succ_sub_succ] using this

theorem take_set_lt (b : Board) (m i : Nat) (v : Bool) (h : i < m) :
    (b.set i v).take m = (b.take m).set i v := by
  induction b generalizing m i with
  | nil => simp
  | cons a t ih =>
      cases m with
      | zero => omega
      | succ m' =>
          cases i with
          | zero => rfl
          | succ i' => simpa [List.set] using ih m' i' (by omega)

theorem take_set_ge (b : Board) (m i : Nat) (v : Bool) (h : m ≤ i) :
    (b.set i v).take m = b.take m := by
  induction b generalizing m i with
  | nil => rfl
  | cons a t ih =>
      cases m with
      | zero => rfl
      | succ m' =>
          cases i with
          | zero => omega
          | succ i' => simpa [List.set] using ih m' i' (by omega)

theorem nth_drop (b : Board) (m i : Nat) :
    nth (b.drop m) i = nth b (m + i) := by
  induction b generalizing m with
  | nil => simp [nth]
  | cons a t ih =>
      cases m with
      | zero => simp
      | succ m' => simpa [nth, Nat.succ_add] using ih m'

theorem nth_take (b : Board) (m i : Nat) (h : i < m) :
    nth (b.take m) i = nth b i := by
  induction b generalizing m i with
  | nil => simp [nth]
  | cons a t ih =>
      cases m with
      | zero => omega
      | succ m' =>
          cases i with
          | zero => rfl
          | succ i' => simpa [nth] using ih m' i' (by omega)

/-- Toggling at or below x leaves the part above x unchanged. -/
theorem drop_toggle_low (b : Board) (x i : Nat) (h : i ≤ x) :
    (toggle b i).drop (x + 1) = b.drop (x + 1) :=
  drop_set_lt b (x + 1) i _ (by omega)

/-- Toggling above x is toggling the shifted cell of the dropped
board. -/
theorem drop_toggle_high (b : Board) (x i : Nat) (h : x < i) :
    (toggle b i).drop (x + 1) = toggle (b.drop (x + 1)) (i - (x + 1)) := by
  unfold toggle
  rw [drop_set_ge b (x + 1) i _ (by omega), nth_drop]
  have : x + 1 + (i - (x + 1)) = i := by omega
  rw [this]

/-- Toggling at or above x leaves the part below x unchanged. -/
theorem take_toggle_high (b : Board) (x i : Nat) (h : x ≤ i) :
    (toggle b i).take x = b.take x :=
  take_set_ge b x i _ h

/-- Toggling below x is toggling the same cell of the taken board. -/
theorem take_toggle_low (b : Board) (x i : Nat) (h : i < x) :
    (toggle b i).take x = toggle (b.take x) i := by
  unfold toggle
  rw [take_set_lt b x i _ h, nth_take b x i h]

/-- Execution commutes with the above-x restriction (no legality
needed). -/
theorem execB_shiftAbove (x : Nat) :
    ∀ (s : List Nat) (b : Board),
      (execB b s).drop (x + 1) = execB (b.drop (x + 1)) (shiftAbove x s)
  | [], _ => rfl
  | i :: rest, b => by
      show (execB (toggle b i) rest).drop (x + 1) = _
      by_cases h : x < i
      · have hs : shiftAbove x (i :: rest)
            = (i - (x + 1)) :: shiftAbove x rest := by
          simp [shiftAbove, h]
        rw [hs, execB_shiftAbove x rest (toggle b i),
            drop_toggle_high b x i h]
        rfl
      · have hs : shiftAbove x (i :: rest) = shiftAbove x rest := by
          simp [shiftAbove, h]
        rw [hs, execB_shiftAbove x rest (toggle b i),
            drop_toggle_low b x i (by omega)]

/-- Execution commutes with the below-x restriction. -/
theorem execB_keepBelow (x : Nat) :
    ∀ (s : List Nat) (b : Board),
      (execB b s).take x = execB (b.take x) (keepBelow x s)
  | [], _ => rfl
  | i :: rest, b => by
      show (execB (toggle b i) rest).take x = _
      by_cases h : i < x
      · have hs : keepBelow x (i :: rest) = i :: keepBelow x rest := by
          simp [keepBelow, h]
        rw [hs, execB_keepBelow x rest (toggle b i),
            take_toggle_low b x i h]
        rfl
      · have hs : keepBelow x (i :: rest) = keepBelow x rest := by
          simp [keepBelow, h]
        rw [hs, execB_keepBelow x rest (toggle b i),
            take_toggle_high b x i (by omega)]

/-- LEGALITY of the above-x restriction: moves on cell x+1 become
free (new left end), higher moves keep their support. -/
theorem legalB_shiftAbove (x : Nat) :
    ∀ (s : List Nat) (b : Board), legalB b s = true →
      legalB (b.drop (x + 1)) (shiftAbove x s) = true
  | [], _, _ => rfl
  | i :: rest, b, hleg => by
      have hok : okMove b i = true ∧ legalB (toggle b i) rest = true := by
        simpa [legalB, Bool.and_eq_true] using hleg
      by_cases h : x < i
      · have hs : shiftAbove x (i :: rest)
            = (i - (x + 1)) :: shiftAbove x rest := by
          simp [shiftAbove, h]
        rw [hs]
        have htail := legalB_shiftAbove x rest (toggle b i) hok.2
        rw [drop_toggle_high b x i h] at htail
        have hoknew : okMove (b.drop (x + 1)) (i - (x + 1)) = true := by
          by_cases hx1 : i = x + 1
          · subst hx1; simp [okMove]
          · have hi2 : i - (x + 1) ≠ 0 := by omega
            have := hok.1
            rcases (by simpa [okMove, Bool.or_eq_true] using this :
                (i == 0) = true ∨ nth b (i - 1) = true) with h0 | hprev
            · simp at h0; omega
            · have harith : x + 1 + (i - (x + 1) - 1) = i - 1 := by omega
              simp only [okMove, Bool.or_eq_true]
              right
              rw [nth_drop, harith]
              exact hprev
        simp [legalB, hoknew, htail]
      · have hs : shiftAbove x (i :: rest) = shiftAbove x rest := by
          simp [shiftAbove, h]
        rw [hs]
        have htail := legalB_shiftAbove x rest (toggle b i) hok.2
        rwa [drop_toggle_low b x i (by omega)] at htail

/-- LEGALITY of the below-x restriction: supports of low moves live
below x, and high moves do not disturb them. -/
theorem legalB_keepBelow (x : Nat) :
    ∀ (s : List Nat) (b : Board), legalB b s = true →
      legalB (b.take x) (keepBelow x s) = true
  | [], _, _ => rfl
  | i :: rest, b, hleg => by
      have hok : okMove b i = true ∧ legalB (toggle b i) rest = true := by
        simpa [legalB, Bool.and_eq_true] using hleg
      by_cases h : i < x
      · have hs : keepBelow x (i :: rest) = i :: keepBelow x rest := by
          simp [keepBelow, h]
        rw [hs]
        have htail := legalB_keepBelow x rest (toggle b i) hok.2
        rw [take_toggle_low b x i h] at htail
        have hoknew : okMove (b.take x) i = true := by
          cases i with
          | zero => simp [okMove]
          | succ j =>
              have := hok.1
              rcases (by simpa [okMove, Bool.or_eq_true] using this :
                  (j + 1 == 0) = true ∨ nth b j = true) with h0 | hprev
              · simp at h0
              · simp only [okMove, Bool.or_eq_true]
                right
                rw [show j + 1 - 1 = j from rfl, nth_take b x j (by omega)]
                exact hprev
        simp [legalB, hoknew, htail]
      · have hs : keepBelow x (i :: rest) = keepBelow x rest := by
          simp [keepBelow, h]
        rw [hs]
        have htail := legalB_keepBelow x rest (toggle b i) hok.2
        rwa [take_toggle_high b x i (by omega)] at htail

/-- Pebble counts split across the cut: ones = ones(take) + ones(drop). -/
theorem ones_take_drop :
    ∀ (b : Board) (m : Nat), ones (b.take m) + ones (b.drop m) = ones b
  | _, 0 => by simp [ones]
  | [], _ + 1 => by simp [ones]
  | a :: t, m + 1 => by
      have := ones_take_drop t m
      cases a <;> simp [ones, List.count_cons] at this ⊢ <;> omega

/-- A filter of a prefix is a prefix of the filter. -/
theorem filter_take_prefix (p : Nat → Bool) :
    ∀ (s : List Nat) (k : Nat),
      ∃ j, (s.filter p).take j = (s.take k).filter p
  | _, 0 => ⟨0, by simp⟩
  | [], _ + 1 => ⟨0, by simp⟩
  | i :: rest, k + 1 => by
      obtain ⟨j, hj⟩ := filter_take_prefix p rest k
      cases hp : p i with
      | true =>
          exact ⟨j + 1, by simp [hp, hj]⟩
      | false =>
          exact ⟨j, by simp [hp, hj]⟩

/-- A prefix of the trace corresponds to a prefix of the restricted
trace (above form). -/
theorem shiftAbove_take_prefix (x : Nat) (s : List Nat) (k : Nat) :
    ∃ j, (shiftAbove x s).take j = shiftAbove x (s.take k) := by
  obtain ⟨j, hj⟩ := filter_take_prefix (fun i => decide (x < i)) s k
  refine ⟨j, ?_⟩
  unfold shiftAbove
  rw [← List.map_take, hj]

/-- COVERAGE transfers to the above-x restriction. -/
theorem everOn_shiftAbove {b : Board} {s : List Nat} {v x : Nat}
    (hv : x < v) (h : everOn b s v) :
    everOn (b.drop (x + 1)) (shiftAbove x s) (v - (x + 1)) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨j, hj⟩ := shiftAbove_take_prefix x s k
  refine ⟨j, ?_⟩
  rw [hj, ← execB_shiftAbove, nth_drop]
  have : x + 1 + (v - (x + 1)) = v := by omega
  rw [this]
  exact hk

/-- COVERAGE transfers to the below-x restriction. -/
theorem everOn_keepBelow {b : Board} {s : List Nat} {v x : Nat}
    (hv : v < x) (h : everOn b s v) :
    everOn (b.take x) (keepBelow x s) v := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨j, hj⟩ := filter_take_prefix (fun i => decide (i < x)) s k
  refine ⟨j, ?_⟩
  show nth (execB (b.take x) ((keepBelow x s).take j)) v = true
  rw [show (keepBelow x s).take j = keepBelow x (s.take k) from hj,
      ← execB_keepBelow, nth_take _ _ _ hv]
  exact hk

-- ------------------------------------------------------------------
-- Middle-vertex machinery (roadmap steps (d)-(f), 追記32): helper
-- lemmas for the general impossibility theorem.
-- ------------------------------------------------------------------

/-- Every prefix pebble count is bounded by the peak. -/
theorem ones_prefix_le_maxOnes :
    ∀ (s : List Nat) (b : Board) (k : Nat),
      ones (execB b (s.take k)) ≤ maxOnes b s
  | [], b, k => by simp [execB, maxOnes]
  | i :: rest, b, 0 => by
      simpa [execB] using ones_le_maxOnes b (i :: rest)
  | i :: rest, b, k + 1 => by
      have := ones_prefix_le_maxOnes rest (toggle b i) k
      show ones (execB (toggle b i) (rest.take k)) ≤ _
      exact Nat.le_trans this (Nat.le_max_right _ _)

/-- Conversely, the peak is bounded by any uniform prefix bound. -/
theorem maxOnes_le_of_prefixes :
    ∀ (s : List Nat) (b : Board) (K : Nat),
      (∀ k, ones (execB b (s.take k)) ≤ K) → maxOnes b s ≤ K
  | [], b, K, h => by
      show ones b ≤ K
      simpa [execB] using h 0
  | i :: rest, b, K, h => by
      show max (ones b) (maxOnes (toggle b i) rest) ≤ K
      have h0 : ones b ≤ K := by simpa [execB] using h 0
      have h1 : maxOnes (toggle b i) rest ≤ K := by
        apply maxOnes_le_of_prefixes
        intro k
        simpa [execB] using h (k + 1)
      omega

theorem nth_true_lt_length {b : Board} {v : Nat} (h : nth b v = true) :
    v < b.length := by
  by_cases hlt : v < b.length
  · exact hlt
  · rw [nth_ge_length b v (by omega)] at h
    exact absurd h (by simp)

theorem ones_pos_of_nth' :
    ∀ (b : Board) (v : Nat), nth b v = true → 1 ≤ ones b
  | [], v, h => by simp [nth] at h
  | a :: t, 0, h => by
      have ha : a = true := h
      subst ha
      simp [ones]
  | a :: t, v + 1, h => by
      have := ones_pos_of_nth' t v (by simpa [nth] using h)
      cases a <;> simp [ones] at this ⊢ <;> omega

theorem ones_pos_of_nth {b : Board} {v : Nat} (h : nth b v = true) :
    1 ≤ ones b := ones_pos_of_nth' b v h

/-- Cells untouched by the move list keep their value on every
prefix. -/
theorem nth_exec_of_not_mem :
    ∀ (t : List Nat) (b : Board) (x : Nat), x ∉ t →
      nth (execB b t) x = nth b x
  | [], _, _, _ => rfl
  | i :: rest, b, x, hx => by
      have hxi : x ≠ i := fun hc => hx (hc ▸ List.mem_cons_self ..)
      have hrest : x ∉ rest := fun hc => hx (List.mem_cons_of_mem _ hc)
      show nth (execB (toggle b i) rest) x = nth b x
      rw [nth_exec_of_not_mem rest (toggle b i) x hrest]
      exact nth_set_ne b i x _ (fun hc => hxi hc.symm)

/-- Last-occurrence split: any list containing x splits as
u₁ ++ x :: u₂ with x ∉ u₂. -/
theorem last_occurrence_split {x : Nat} :
    ∀ {u : List Nat}, x ∈ u →
      ∃ u₁ u₂, u = u₁ ++ x :: u₂ ∧ x ∉ u₂ := by
  intro u
  induction u with
  | nil => intro h; exact absurd h (by simp)
  | cons i rest ih =>
      intro h
      by_cases hr : x ∈ rest
      · obtain ⟨u₁, u₂, heq, hnot⟩ := ih hr
        exact ⟨i :: u₁, u₂, by rw [heq]; rfl, hnot⟩
      · have hxi : x = i := by
          rcases List.mem_cons.mp h with h1 | h2
          · exact h1
          · exact absurd h2 hr
        exact ⟨[], rest, by rw [hxi]; rfl, hr⟩

/-- A prefix that is pointwise unpebbled is literally the empty
board. -/
theorem take_all_false_replicate' :
    ∀ (b : Board) (x : Nat), x ≤ b.length →
      (∀ j, j < x → nth b j = false) →
      b.take x = List.replicate x false
  | _, 0, _, _ => by simp
  | [], x + 1, hlen, _ => by simp at hlen
  | a :: t, x + 1, hlen, h => by
      have ha : a = false := h 0 (by omega)
      subst ha
      have ht := take_all_false_replicate' t x (by simpa using hlen)
        (fun j hj => by simpa [nth] using h (j + 1) (by omega))
      simp [List.replicate_succ, ht]

theorem take_all_false_replicate {b : Board} {x : Nat}
    (hlen : x ≤ b.length) (h : ∀ j, j < x → nth b j = false) :
    b.take x = List.replicate x false :=
  take_all_false_replicate' b x hlen h

/-- One pebble at or beyond the cut is invisible to the taken part:
ones (b.take x) < ones b whenever cell x is pebbled. -/
theorem ones_take_lt_of_nth {b : Board} {x : Nat}
    (h : nth b x = true) : ones (b.take x) + 1 ≤ ones b := by
  have hsplit := ones_take_drop b x
  have hdrop : nth (b.drop x) 0 = true := by
    rw [nth_drop]
    simpa using h
  have := ones_pos_of_nth hdrop
  omega

/-- Converse prefix correspondence: every prefix of a filtered list
is the filter of some prefix. -/
theorem filter_take_surj (p : Nat → Bool) :
    ∀ (s : List Nat) (j : Nat),
      ∃ k, (s.filter p).take j = (s.take k).filter p
  | [], j => ⟨0, by simp⟩
  | i :: rest, j => by
      cases hp : p i with
      | true =>
          match j with
          | 0 => exact ⟨0, by simp⟩
          | j + 1 =>
              obtain ⟨k, hk⟩ := filter_take_surj p rest j
              exact ⟨k + 1, by simp [hp, hk]⟩
      | false =>
          obtain ⟨k, hk⟩ := filter_take_surj p rest j
          exact ⟨k + 1, by simp [hp, hk]⟩

/-- Index of the first pebble, if any. -/
def firstOn : Board → Option Nat
  | [] => none
  | true :: _ => some 0
  | false :: t => (firstOn t).map (· + 1)

theorem firstOn_spec :
    ∀ (b : Board) (v : Nat), firstOn b = some v →
      nth b v = true ∧ ∀ j, j < v → nth b j = false
  | [], v, h => by simp [firstOn] at h
  | true :: t, v, h => by
      have hv : v = 0 := by simpa [firstOn] using h.symm
      subst hv
      exact ⟨rfl, by omega⟩
  | false :: t, v, h => by
      simp only [firstOn, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, hwv⟩ := h
      obtain ⟨h1, h2⟩ := firstOn_spec t w hw
      subst hwv
      refine ⟨by simpa [nth] using h1, ?_⟩
      intro j hj
      cases j with
      | zero => rfl
      | succ j' => simpa [nth] using h2 j' (by omega)

theorem firstOn_none :
    ∀ (b : Board), firstOn b = none → ∀ v, nth b v = false
  | [], _, v => by simp [nth]
  | true :: t, h, v => by simp [firstOn] at h
  | false :: t, h, v => by
      simp only [firstOn, Option.map_eq_none_iff] at h
      cases v with
      | zero => rfl
      | succ v' => simpa [nth] using firstOn_none t h v'

theorem firstOn_isSome_of_nth {b : Board} {v : Nat}
    (h : nth b v = true) : (firstOn b).isSome = true := by
  cases hf : firstOn b with
  | none => rw [firstOn_none b hf v] at h; exact absurd h (by simp)
  | some w => rfl

/-- Max of a list of naturals. -/
def natMax (l : List Nat) : Nat := l.foldl max 0

theorem foldl_max_ge_init : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
  | [], _ => Nat.le_refl _
  | i :: rest, a => by
      have := foldl_max_ge_init rest (max a i)
      show a ≤ (i :: rest).foldl max a
      simp only [List.foldl_cons]
      omega

theorem le_natMax_of_mem : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ natMax l := by
  intro l
  suffices h : ∀ (l : List Nat) (c a : Nat), a ∈ l → a ≤ l.foldl max c by
    intro a ha; exact h l 0 a ha
  intro l
  induction l with
  | nil => intro c a ha; exact absurd ha (by simp)
  | cons i rest ih =>
      intro c a ha
      rcases List.mem_cons.mp ha with rfl | hrest
      · simp only [List.foldl_cons]
        exact Nat.le_trans (Nat.le_max_right c a) (foldl_max_ge_init rest _)
      · simpa using ih (max c i) a hrest

theorem natMax_attained :
    ∀ (l : List Nat), natMax l = 0 ∨ natMax l ∈ l := by
  suffices h : ∀ (l : List Nat) (c : Nat),
      l.foldl max c = c ∨ l.foldl max c ∈ l by
    intro l; exact (h l 0).imp id id
  intro l
  induction l with
  | nil => intro c; exact Or.inl rfl
  | cons i rest ih =>
      intro c
      simp only [List.foldl_cons]
      rcases ih (max c i) with h1 | h2
      · rw [h1]
        rcases Nat.le_total c i with hci | hic
        · rw [Nat.max_eq_right hci]
          exact Or.inr (List.mem_cons_self ..)
        · rw [Nat.max_eq_left hic]
          exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ h2)

theorem legal_take {b : Board} {s : List Nat} (a : Nat)
    (h : legalB b s = true) : legalB b (s.take a) = true := by
  rw [← List.take_append_drop a s, legal_append, Bool.and_eq_true] at h
  exact h.1

theorem maxOnes_take_le (b : Board) (s : List Nat) (a : Nat) :
    maxOnes b (s.take a) ≤ maxOnes b s := by
  apply maxOnes_le_of_prefixes
  intro k
  rw [List.take_take]
  exact ones_prefix_le_maxOnes s b (min k a)

theorem ones_zero_of_firstOn_none :
    ∀ (b : Board), firstOn b = none → ones b = 0
  | [], _ => rfl
  | true :: t, h => by simp [firstOn] at h
  | false :: t, h => by
      simp only [firstOn, Option.map_eq_none_iff] at h
      simpa [ones] using ones_zero_of_firstOn_none t h

theorem drop_replicate (n m : Nat) (v : Bool) :
    (List.replicate n v).drop m = List.replicate (n - m) v := by
  induction n generalizing m with
  | zero => simp
  | succ n' ih =>
      cases m with
      | zero => simp
      | succ m' => simpa [List.replicate_succ] using ih m'

-- ------------------------------------------------------------------
-- The middle vertex and the general impossibility theorem
-- (roadmap steps (d)-(f)): a complete computation of a chain with
-- peak P covers at most 2^P - 1 cells, hence clean reach with peak p
-- stops at cell 2^(p-1) - 1 (Knill 1995 Thm 2.3, impossibility half,
-- now GENERAL).
-- ------------------------------------------------------------------

/-- Trace configuration after k moves. -/
def cfg (n : Nat) (s : List Nat) (k : Nat) : Board :=
  execB (List.replicate n false) (s.take k)

theorem cfg_clip (n : Nat) (s : List Nat) (k : Nat) :
    cfg n s k = cfg n s (min k s.length) := by
  unfold cfg
  rcases Nat.le_total k s.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le h,
        List.take_of_length_le (Nat.le_refl _)]

/-- The middle vertex: the largest first-pebbled index over the whole
trace. -/
def midX (n : Nat) (s : List Nat) : Nat :=
  natMax ((List.range (s.length + 1)).map
    (fun k => (firstOn (cfg n s k)).getD 0))

theorem midX_ge (n : Nat) (s : List Nat) (k : Nat) :
    (firstOn (cfg n s k)).getD 0 ≤ midX n s := by
  rw [cfg_clip]
  apply le_natMax_of_mem
  apply List.mem_map.mpr
  refine ⟨min k s.length, ?_, rfl⟩
  simp [List.mem_range]
  omega

theorem midX_attained (n : Nat) (s : List Nat) :
    midX n s = 0 ∨
    ∃ k, k ≤ s.length ∧ (firstOn (cfg n s k)).getD 0 = midX n s := by
  rcases natMax_attained ((List.range (s.length + 1)).map
      (fun k => (firstOn (cfg n s k)).getD 0)) with h0 | hmem
  · exact Or.inl h0
  · obtain ⟨k, hk, hval⟩ := List.mem_map.mp hmem
    have hk' := List.mem_range.mp hk
    exact Or.inr ⟨k, by omega, hval⟩

/-- Every nonempty configuration has a pebble at or below the middle
vertex. -/
theorem cfg_low_pebble {n : Nat} {s : List Nat} (k : Nat) {w : Nat}
    (hw : nth (cfg n s k) w = true) :
    ∃ u, u ≤ midX n s ∧ nth (cfg n s k) u = true := by
  cases hf : firstOn (cfg n s k) with
  | none =>
      rw [firstOn_none _ hf w] at hw
      exact absurd hw (by simp)
  | some u =>
      obtain ⟨h1, _⟩ := firstOn_spec _ u hf
      refine ⟨u, ?_, h1⟩
      have := midX_ge n s k
      rw [hf] at this
      simpa using this

theorem take_append_exact :
    ∀ (l₁ l₂ : List Nat) (m : Nat),
      (l₁ ++ l₂).take (l₁.length + m) = l₁ ++ l₂.take m
  | [], l₂, m => by simp
  | i :: t, l₂, m => by
      simp only [List.cons_append, List.length_cons]
      rw [show t.length + 1 + m = (t.length + m) + 1 from by omega]
      simp [take_append_exact t l₂ m]

/-- LEFT EXTRACTION (roadmap step (e)): if some trace configuration
has cell x pebbled with all lower cells empty, then chain x admits a
COMPLETE computation whose peak is strictly below the peak of s. -/
theorem left_extraction {n : Nat} {s : List Nat} {x a P : Nat}
    (hleg : legalB (List.replicate n false) s = true)
    (hpeak : maxOnes (List.replicate n false) s ≤ P)
    (hx : nth (cfg n s a) x = true)
    (hlow : ∀ j, j < x → nth (cfg n s a) j = false) :
    ∃ t : List Nat,
      legalB (List.replicate x false) t = true ∧
      execB (List.replicate x false) t = List.replicate x false ∧
      maxOnes (List.replicate x false) t + 1 ≤ P ∧
      (∀ j, j < x → everOn (List.replicate x false) t j) := by
  have hP1 : 1 ≤ P := by
    have h1 := ones_pos_of_nth hx
    have h2 : ones (cfg n s a) ≤ maxOnes (List.replicate n false) s :=
      ones_prefix_le_maxOnes s (List.replicate n false) a
    omega
  match x with
  | 0 =>
      refine ⟨[], rfl, rfl, ?_, by intro j hj; omega⟩
      show ones (List.replicate 0 false) + 1 ≤ P
      simpa [ones] using hP1
  | x + 1 =>
      -- u := s.take a, split at the LAST occurrence of the move x+1
      have hlegu : legalB (List.replicate n false) (s.take a) = true :=
        legal_take a hleg
      have hxlt : x + 1 < (cfg n s a).length := nth_true_lt_length hx
      by_cases hmem : (x + 1) ∈ s.take a
      case neg =>
        exfalso
        have := nth_exec_of_not_mem (s.take a)
          (List.replicate n false) (x + 1) hmem
        rw [show execB (List.replicate n false) (s.take a) = cfg n s a
              from rfl, hx, nth_replicate] at this
        exact absurd this (by simp)
      case pos =>
      obtain ⟨u₁, u₂, hsplit, hnotin⟩ := last_occurrence_split hmem
      have hlegu' := hlegu
      rw [hsplit, legal_append, Bool.and_eq_true] at hlegu'
      have hokd : okMove (execB (List.replicate n false) u₁) (x + 1) = true ∧
          legalB (toggle (execB (List.replicate n false) u₁) (x + 1)) u₂
            = true := by
        simpa [legalB, Bool.and_eq_true] using hlegu'.2
      -- names: c₁ = board before the last x+1 move, d = just after
      have hca : cfg n s a
          = execB (toggle (execB (List.replicate n false) u₁) (x + 1)) u₂ := by
        show execB (List.replicate n false) (s.take a) = _
        rw [hsplit, exec_append]
        rfl
      have hdon : nth (toggle (execB (List.replicate n false) u₁) (x + 1))
          (x + 1) = true := by
        have := nth_exec_of_not_mem u₂
          (toggle (execB (List.replicate n false) u₁) (x + 1)) (x + 1) hnotin
        rw [← hca] at this
        rw [← this]
        exact hx
      have hprev : nth (execB (List.replicate n false) u₁) x = true := by
        simpa [okMove] using hokd.1
      -- restriction to the cells below x+1
      have hb0 : (toggle (execB (List.replicate n false) u₁) (x + 1)).take
          (x + 1) = (execB (List.replicate n false) u₁).take (x + 1) :=
        take_toggle_high _ (x + 1) (x + 1) (Nat.le_refl _)
      have hlegR : legalB ((toggle (execB (List.replicate n false) u₁)
            (x + 1)).take (x + 1)) (keepBelow (x + 1) u₂) = true :=
        legalB_keepBelow (x + 1) u₂ _ hokd.2
      have hexecR : execB ((toggle (execB (List.replicate n false) u₁)
            (x + 1)).take (x + 1)) (keepBelow (x + 1) u₂)
          = List.replicate (x + 1) false := by
        rw [← execB_keepBelow, ← hca]
        exact take_all_false_replicate (by omega) hlow
      -- t₁ reaches the top cell x of the restricted chain from empty
      have hlegT : legalB (List.replicate (x + 1) false)
          ((keepBelow (x + 1) u₂).reverse) = true := by
        have := legal_reverse _ _ hlegR
        rwa [hexecR] at this
      have hexecT : execB (List.replicate (x + 1) false)
          ((keepBelow (x + 1) u₂).reverse)
          = (toggle (execB (List.replicate n false) u₁) (x + 1)).take
              (x + 1) := by
        have := exec_reverse_cancel ((toggle (execB (List.replicate n false)
          u₁) (x + 1)).take (x + 1)) (keepBelow (x + 1) u₂)
        rwa [hexecR] at this
      have hendT : nth (execB (List.replicate (x + 1) false)
          ((keepBelow (x + 1) u₂).reverse)) x = true := by
        rw [hexecT, hb0, nth_take _ _ _ (by omega)]
        exact hprev
      -- peak of the restricted computation is < P
      have hpeakR : maxOnes ((toggle (execB (List.replicate n false) u₁)
            (x + 1)).take (x + 1)) (keepBelow (x + 1) u₂) + 1 ≤ P := by
        have hpre : ∀ j, ones (execB ((toggle (execB (List.replicate n
            false) u₁) (x + 1)).take (x + 1))
              ((keepBelow (x + 1) u₂).take j)) ≤ P - 1 := by
          intro j
          obtain ⟨k, hk⟩ := filter_take_surj
            (fun i => decide (i < x + 1)) u₂ j
          have hkB : (keepBelow (x + 1) u₂).take j
              = keepBelow (x + 1) (u₂.take k) := hk
          rw [hkB, ← execB_keepBelow]
          -- e := execB d (u₂.take k) is a global prefix configuration
          have hnotk : (x + 1) ∉ u₂.take k :=
            fun hc => hnotin (List.take_subset k u₂ hc)
          have heon : nth (execB (toggle (execB (List.replicate n false)
              u₁) (x + 1)) (u₂.take k)) (x + 1) = true := by
            rw [nth_exec_of_not_mem _ _ _ hnotk]
            exact hdon
          have hcut := ones_take_lt_of_nth heon
          have hglob : ones (execB (toggle (execB (List.replicate n false)
              u₁) (x + 1)) (u₂.take k)) ≤ P := by
            have he : execB (toggle (execB (List.replicate n false) u₁)
                (x + 1)) (u₂.take k)
                = execB (List.replicate n false)
                    ((s.take a).take (u₁.length + (k + 1))) := by
              rw [hsplit, take_append_exact, exec_append]
              rfl
            rw [he]
            calc ones (execB (List.replicate n false)
                  ((s.take a).take (u₁.length + (k + 1))))
                ≤ maxOnes (List.replicate n false) (s.take a) :=
                  ones_prefix_le_maxOnes _ _ _
              _ ≤ maxOnes (List.replicate n false) s :=
                  maxOnes_take_le _ _ _
              _ ≤ P := hpeak
          omega
        have := maxOnes_le_of_prefixes (keepBelow (x + 1) u₂) _ (P - 1) hpre
        omega
      have hpeakT : maxOnes (List.replicate (x + 1) false)
          ((keepBelow (x + 1) u₂).reverse) + 1 ≤ P := by
        have := maxOnes_reverse ((toggle (execB (List.replicate n false)
          u₁) (x + 1)).take (x + 1)) (keepBelow (x + 1) u₂)
        rw [hexecR] at this
        omega
      -- assemble the roundtrip
      obtain ⟨hL, hE, hM, hC⟩ := roundtrip_complete (x + 1)
        ((keepBelow (x + 1) u₂).reverse) x hlegT hendT
      refine ⟨(keepBelow (x + 1) u₂).reverse
        ++ ((keepBelow (x + 1) u₂).reverse).reverse, hL, hE, ?_, ?_⟩
      · rw [hM]; exact hpeakT
      · intro j hj
        exact hC j (by omega)

/-- Local: powers of two are positive. -/
theorem one_le_two_pow : ∀ (k : Nat), 1 ≤ 2 ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => by
      rw [Nat.pow_succ]
      have := one_le_two_pow k
      omega

/-- THE GENERAL COMPLETE-COMPUTATION BOUND (roadmap step (f)): a
complete computation (empty to empty) of peak at most P covers at
most 2^P - 1 cells.  Middle-vertex induction on P. -/
theorem complete_bound :
    ∀ (P n : Nat) (s : List Nat) (m : Nat),
      legalB (List.replicate n false) s = true →
      execB (List.replicate n false) s = List.replicate n false →
      maxOnes (List.replicate n false) s ≤ P →
      (∀ j, j < m → everOn (List.replicate n false) s j) →
      m ≤ 2 ^ P - 1 := by
  intro P
  induction P with
  | zero =>
      intro n s m _ _ hpeak hcov
      by_cases hm : m = 0
      · omega
      · exfalso
        obtain ⟨k, hk⟩ := hcov 0 (by omega)
        have h1 := ones_pos_of_nth hk
        have h2 := ones_prefix_le_maxOnes s (List.replicate n false) k
        omega
  | succ P ih =>
      intro n s m hleg hexec hpeak hcov
      by_cases hm : m = 0
      · have := one_le_two_pow (P + 1); omega
      -- the middle vertex
      have hxbound : midX n s ≤ 2 ^ P - 1 := by
        rcases midX_attained n s with h0 | ⟨a, _, hval⟩
        · rw [h0]; omega
        · by_cases hx0 : midX n s = 0
          · rw [hx0]; omega
          · cases hf : firstOn (cfg n s a) with
            | none => rw [hf] at hval; simp at hval; omega
            | some w =>
                rw [hf] at hval
                simp at hval
                rw [← hval]
                obtain ⟨hon, hlow⟩ := firstOn_spec _ w hf
                obtain ⟨t, hL, hE, hM, hC⟩ :=
                  left_extraction hleg hpeak hon hlow
                exact ih w t w hL hE (by omega) (fun j hj => hC j hj)
      -- the right side: cells above the middle vertex
      have hright : m - (midX n s + 1) ≤ 2 ^ P - 1 := by
        apply ih (n - (midX n s + 1)) (shiftAbove (midX n s) s)
        · have := legalB_shiftAbove (midX n s) s _ hleg
          rwa [drop_replicate] at this
        · have := execB_shiftAbove (midX n s) s (List.replicate n false)
          rw [hexec, drop_replicate] at this
          exact this.symm
        · -- peak of the restriction drops by one: every nonempty
          -- configuration keeps a pebble at or below the middle vertex
          have hpre : ∀ j, ones (execB (List.replicate
              (n - (midX n s + 1)) false)
                ((shiftAbove (midX n s) s).take j)) ≤ P := by
            intro j
            obtain ⟨k, hk⟩ := filter_take_surj
              (fun i => decide (midX n s < i)) s j
            have hsj : (shiftAbove (midX n s) s).take j
                = shiftAbove (midX n s) (s.take k) := by
              unfold shiftAbove
              rw [← List.map_take, hk]
            rw [hsj, ← drop_replicate n (midX n s + 1) false,
                ← execB_shiftAbove]
            cases hf : firstOn (cfg n s k) with
            | none =>
                have hz := ones_zero_of_firstOn_none _ hf
                have := ones_take_drop (cfg n s k) (midX n s + 1)
                show ones ((cfg n s k).drop (midX n s + 1)) ≤ P
                omega
            | some w =>
                obtain ⟨hon, _⟩ := firstOn_spec _ w hf
                have hwx : w ≤ midX n s := by
                  have := midX_ge n s k
                  rw [hf] at this
                  simpa using this
                have htk : nth ((cfg n s k).take (midX n s + 1)) w
                    = true := by
                  rw [nth_take _ _ _ (by omega)]
                  exact hon
                have h1 := ones_pos_of_nth htk
                have h2 := ones_take_drop (cfg n s k) (midX n s + 1)
                have h3 : ones (cfg n s k) ≤ P + 1 :=
                  Nat.le_trans (ones_prefix_le_maxOnes s _ k) hpeak
                show ones ((cfg n s k).drop (midX n s + 1)) ≤ P
                omega
          exact maxOnes_le_of_prefixes _ _ P hpre
        · intro j hj
          have hcv := hcov (midX n s + 1 + j) (by omega)
          have := everOn_shiftAbove
            (x := midX n s) (by omega) hcv
          rw [drop_replicate] at this
          have harith : midX n s + 1 + j - (midX n s + 1) = j := by omega
          rwa [harith] at this
      have hpow := one_le_two_pow P
      have hpow2 : 2 ^ (P + 1) = 2 * 2 ^ P := by
        rw [Nat.pow_succ]; omega
      omega

/-- KNILL THM 2.3, IMPOSSIBILITY HALF, GENERAL: a legal computation
from the empty board with peak at most p whose final configuration
has cell v pebbled and all lower cells empty (in particular a CLEAN
REACH of cell v) satisfies v + 1 ≤ 2^(p-1).  Together with
`reach_two_pow` this characterises the reach of the reversible pebble
game exactly: reach(p) = 2^(p-1). -/
theorem reach_impossible_general {n p v : Nat} {s : List Nat}
    (hleg : legalB (List.replicate n false) s = true)
    (hpeak : maxOnes (List.replicate n false) s ≤ p)
    (hon : nth (execB (List.replicate n false) s) v = true)
    (hmin : ∀ j, j < v → nth (execB (List.replicate n false) s) j = false) :
    v + 1 ≤ 2 ^ (p - 1) := by
  have hcfg : cfg n s s.length = execB (List.replicate n false) s := by
    show execB (List.replicate n false) (s.take s.length) = _
    rw [List.take_of_length_le (Nat.le_refl _)]
  obtain ⟨t, hL, hE, hM, hC⟩ := left_extraction hleg hpeak
    (a := s.length) (by rw [hcfg]; exact hon)
    (by intro j hj; rw [hcfg]; exact hmin j hj)
  have hb := complete_bound (p - 1) v t v hL hE (by omega)
    (fun j hj => hC j hj)
  have := one_le_two_pow (p - 1)
  omega

end GenJanus.PebblingFoundations
