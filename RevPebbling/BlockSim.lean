import RevPebbling.RowExact
import RevPebbling.GrowthRate
import RevPebbling.GrowthCertified
import RevPebbling.GrowthClosedForm
import RevPebbling.Dispersion4731Growth

/-!
# Block simulation, and `Submult` (this work)

`GrowthRate.Submult fRow : f_{p+q-1} ≤ f_p · f_q` is the last unproved
hypothesis that the growth-rate results depend on (the letter's Lemma 1).
This file proves it.

## The construction

Read a chain of `N · L` cells as `N` **blocks** of `L` cells, where a
block counts as "pebbled" exactly when its top cell is.  A play `a` on
`N` cells then drives a play on `N · L` cells: every move of `a` on
super-cell `i` becomes a whole inner play `b`, lifted to block `i` —
forwards when the block has to be built, backwards when it has to be
cleared (`dirPlay`, `expand`).

Four laws, each an induction along the outer play (`length_expand`,
`exec_expand`, `legal_expand`, `maxOnes_expand`):

* the length multiplies, `|expand| = |a| · |b|`;
* the composite lands on the blow-up of wherever `a` lands;
* it is legal, because the foundation of block `i` is the top cell of
  block `i - 1`, which is exactly what `okMove` asks of the outer play;
* **the peaks add, minus one**: while the inner play runs in block `i`,
  the other blocks hold one pebble each and there are at most
  `(outer peak) - 1` of them, since the configuration with `i` on is one
  of the ones the outer peak ranges over.

That last point is the whole content of `p + q - 1`, and it is what
`LiftAbove.maxOnes_liftAbove` was stated for.

Taking `N = 2^{p-1}` and `L = 2^{q-1}` gives a play on `2^{p+q-2}` cells
— the reach limit for `p + q - 1` pebbles — of length `f_p · f_q`, and
`RowExact.gameF_eq_fRow_all` turns that into `Submult fRow`.

## Sanity

The four laws were checked outside Lean on 3500 random triples (outer
start board, outer play, inner play), and the construction reproduces
`f_p · f_q` exactly on every optimal pair with `p + q - 1 ≤ 6`.  The
bound is tight at `p = q = 2`, where `f_3 = 9 = 3 · 3`.
-/

namespace RevPebbling.BlockSim

open RevPebbling.PebblingFoundations RevPebbling.GameReach RevPebbling.GameCost
open RevPebbling.LiftAbove RevPebbling.RowExact RevPebbling.RowMax
open RevPebbling.ReachLimit RevPebbling.GrowthRate RevPebbling.CutUpper
open RevPebbling.GameLinearLower RevPebbling.CountRecursion

-- ------------------------------------------------------------------
-- Reading and writing across a concatenation
-- ------------------------------------------------------------------

theorem nth_append_left (P R : Board) {j : Nat} (hj : j < P.length) :
    nth (P ++ R) j = nth P j := by
  simp [nth, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem nth_append_right (P R : Board) (j : Nat) :
    nth (P ++ R) (j + P.length) = nth R j := by
  simp [nth, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_left _ _)]

/-- A lifted play does to the right half what it did on its own. -/
theorem exec_lift_append (P R : Board) (s : List Nat) :
    execB (P ++ R) (liftAbove P.length s) = P ++ execB R s := by
  have ht := execB_liftAbove_take P.length s (P ++ R)
  have hd := execB_liftAbove_drop P.length s (P ++ R)
  rw [List.take_left] at ht
  rw [List.drop_left] at hd
  calc execB (P ++ R) (liftAbove P.length s)
      = (execB (P ++ R) (liftAbove P.length s)).take P.length
        ++ (execB (P ++ R) (liftAbove P.length s)).drop P.length :=
        (List.take_append_drop _ _).symm
    _ = P ++ execB R s := by rw [ht, hd]

/-- …and it is legal there, provided the left half ends on a pebble. -/
theorem legal_lift_append (P R : Board) (s : List Nat)
    (hf : P.length = 0 ∨ nth P (P.length - 1) = true)
    (h : legalB R s = true) :
    legalB (P ++ R) (liftAbove P.length s) = true := by
  refine legalB_liftAbove P.length s (P ++ R) ?_ ?_
  · rcases Nat.eq_zero_or_pos P.length with h0 | hpos
    · exact Or.inl h0
    · rcases hf with h | h1
      · exact Or.inl h
      · right
        rw [nth_append_left P R (by omega)]
        exact h1
  · rw [List.drop_left]; exact h

/-- …and its peak is the standing cost of the left half plus its own. -/
theorem maxOnes_lift_append (P R : Board) (s : List Nat) :
    maxOnes (P ++ R) (liftAbove P.length s) ≤ ones P + maxOnes R s := by
  have h := maxOnes_liftAbove P.length s (P ++ R)
  rwa [List.take_left, List.drop_left] at h

-- ------------------------------------------------------------------
-- Blocks
-- ------------------------------------------------------------------

/-- The block a super-cell expands to: `L` cells, pebbled at the top
exactly when the super-cell is on. -/
def blk (L : Nat) (v : Bool) : Board := if v then doneBoard L else emptyBoard L

/-- **THE BLOW-UP.**  Each super-cell of the outer board becomes a
block. -/
def blow (L : Nat) : Board → Board
  | [] => []
  | v :: t => blk L v ++ blow L t

@[simp] theorem blow_nil (L : Nat) : blow L [] = [] := rfl

@[simp] theorem blow_cons (L : Nat) (v : Bool) (t : Board) :
    blow L (v :: t) = blk L v ++ blow L t := rfl

@[simp] theorem blk_length (L : Nat) (v : Bool) : (blk L v).length = L := by
  cases v <;> simp [blk, doneBoard, emptyBoard]

theorem ones_blk (hL : 1 ≤ L) (v : Bool) :
    ones (blk L v) = if v then 1 else 0 := by
  cases v with
  | false => simp [blk]
  | true =>
      obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
      simpa [blk] using ones_doneBoard j

theorem blow_length (L : Nat) : ∀ c : Board, (blow L c).length = c.length * L
  | [] => by simp
  | v :: t => by
      rw [blow_cons, List.length_append, blk_length, blow_length L t,
        List.length_cons, Nat.succ_mul]
      omega

theorem ones_blow (hL : 1 ≤ L) : ∀ c : Board, ones (blow L c) = ones c
  | [] => rfl
  | v :: t => by
      rw [blow_cons, ones_append, ones_blk hL, ones_blow hL t]
      cases v <;> simp [ones] <;> omega

theorem blow_append (L : Nat) : ∀ c d : Board,
    blow L (c ++ d) = blow L c ++ blow L d
  | [], _ => rfl
  | v :: t, d => by
      rw [List.cons_append, blow_cons, blow_cons, blow_append L t d,
        List.append_assoc]

theorem blow_emptyBoard (L : Nat) : ∀ N : Nat,
    blow L (emptyBoard N) = emptyBoard (N * L)
  | 0 => by simp [emptyBoard]
  | N + 1 => by
      show blow L (List.replicate (N + 1) false) = _
      rw [List.replicate_succ]
      show blk L false ++ blow L (emptyBoard N) = _
      rw [blow_emptyBoard L N]
      show emptyBoard L ++ emptyBoard (N * L) = emptyBoard ((N + 1) * L)
      rw [← emptyBoard_split, Nat.succ_mul]
      congr 1
      omega

theorem blow_doneBoard (hL : 1 ≤ L) : ∀ N : Nat,
    blow L (doneBoard N) = doneBoard (N * L)
  | 0 => by rw [Nat.zero_mul]; rfl
  | j + 1 => by
      obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
      have hd : doneBoard (j + 1) = emptyBoard j ++ [true] := doneBoard_succ j
      rw [hd, blow_append, blow_emptyBoard]
      show emptyBoard (j * (m + 1)) ++ (blk (m + 1) true ++ blow (m + 1) []) = _
      rw [blow_nil, List.append_nil]
      show emptyBoard (j * (m + 1)) ++ doneBoard (m + 1)
        = doneBoard ((j + 1) * (m + 1))
      rw [emptyBoard_append_doneBoard, Nat.succ_mul]
      congr 1

/-- The top cell of block `i` mirrors super-cell `i`. -/
theorem nth_blow_top (hL : 1 ≤ L) : ∀ (c : Board) (i : Nat), i < c.length →
    nth (blow L c) (i * L + (L - 1)) = nth c i
  | [], _, h => by simp at h
  | v :: t, 0, _ => by
      rw [blow_cons]
      have hlt : 0 * L + (L - 1) < (blk L v).length := by
        rw [blk_length]; omega
      rw [nth_append_left _ _ hlt]
      cases v with
      | false =>
          show nth (emptyBoard L) (0 * L + (L - 1)) = nth (false :: t) 0
          rw [nth_emptyBoard]
          simp [nth]
      | true =>
          obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
          show nth (doneBoard (m + 1)) (0 * (m + 1) + m) = nth (true :: t) 0
          rw [show 0 * (m + 1) + m = m from by omega]
          rw [nth_doneBoard (m + 1) m (by omega)]
          simp [nth]
  | v :: t, i + 1, h => by
      have h' : i < t.length := by simp at h; omega
      rw [blow_cons]
      have hidx : (i + 1) * L + (L - 1) = (i * L + (L - 1)) + (blk L v).length := by
        rw [blk_length]; cases L with
        | zero => omega
        | succ m => simp [Nat.succ_mul]; omega
      rw [hidx, nth_append_right, nth_blow_top hL t i h']
      simp [nth]

/-- Splitting the blow-up at block `i`. -/
theorem blow_split (L : Nat) {c : Board} {i : Nat} (hi : i < c.length) :
    blow L c = blow L (c.take i) ++ (blk L (nth c i) ++ blow L (c.drop (i + 1))) := by
  have hd : c.drop i = c[i] :: c.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hn : nth c i = c[i] := by
    rw [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  calc blow L c
      = blow L (c.take i ++ c.drop i) := by rw [List.take_append_drop]
    _ = blow L (c.take i) ++ blow L (c.drop i) := blow_append L _ _
    _ = _ := by rw [hd, hn]; rfl

theorem take_toggle_self (c : Board) (i : Nat) : (toggle c i).take i = c.take i := by
  rw [toggle, List.take_set]
  exact set_ge_length _ _ _ (by simp)

theorem drop_toggle_succ (c : Board) (i : Nat) :
    (toggle c i).drop (i + 1) = c.drop (i + 1) := by
  simp [toggle, List.drop_set]

theorem nth_toggle_self (c : Board) {i : Nat} (hi : i < c.length) :
    nth (toggle c i) i = !nth c i := by
  have hi' : i < (toggle c i).length := by simp [toggle]; omega
  rw [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  show (c.set i (!nth c i))[i] = !nth c i
  simp

@[simp] theorem toggle_length (c : Board) (i : Nat) :
    (toggle c i).length = c.length := by simp [toggle]

-- ------------------------------------------------------------------
-- The expansion of a play
-- ------------------------------------------------------------------

/-- The inner play a move on super-cell `i` becomes: forwards to build
the block, backwards to clear it. -/
def dirPlay (c : Board) (i : Nat) (b : List Nat) : List Nat :=
  if nth c i then b.reverse else b

/-- **BLOCK SUBSTITUTION.**  Every move of the outer play becomes an
inner play, lifted to the block it acts on. -/
def expand (L : Nat) (b : List Nat) : Board → List Nat → List Nat
  | _, [] => []
  | c, i :: rest =>
      liftAbove (i * L) (dirPlay c i b) ++ expand L b (toggle c i) rest

@[simp] theorem expand_nil (L : Nat) (b : List Nat) (c : Board) :
    expand L b c [] = [] := rfl

@[simp] theorem expand_cons (L : Nat) (b : List Nat) (c : Board)
    (i : Nat) (rest : List Nat) :
    expand L b c (i :: rest)
      = liftAbove (i * L) (dirPlay c i b) ++ expand L b (toggle c i) rest := rfl

@[simp] theorem dirPlay_length (c : Board) (i : Nat) (b : List Nat) :
    (dirPlay c i b).length = b.length := by
  unfold dirPlay; split <;> simp

/-- **THE LENGTHS MULTIPLY.** -/
theorem length_expand (L : Nat) (b : List Nat) : ∀ (a : List Nat) (c : Board),
    (expand L b c a).length = a.length * b.length
  | [], _ => by simp
  | i :: rest, c => by
      rw [expand_cons, List.length_append, liftAbove_length, dirPlay_length,
        length_expand L b rest (toggle c i), List.length_cons, Nat.succ_mul]
      omega

theorem mem_expand (L : Nat) (b : List Nat) (hrb : ∀ j ∈ b, j < L) :
    ∀ (a : List Nat) (c : Board), ∀ x ∈ expand L b c a,
      ∃ i ∈ a, ∃ j, j < L ∧ x = j + i * L
  | [], _, x, hx => by simp at hx
  | i :: rest, c, x, hx => by
      rcases List.mem_append.mp hx with h | h
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        refine ⟨i, by simp, j, ?_, rfl⟩
        unfold dirPlay at hj
        split at hj
        · exact hrb j (List.mem_reverse.mp hj)
        · exact hrb j hj
      · obtain ⟨i', hi', j, hj, hx'⟩ := mem_expand L b hrb rest (toggle c i) x h
        exact ⟨i', by simp [hi'], j, hj, hx'⟩

-- ------------------------------------------------------------------
-- The single move
-- ------------------------------------------------------------------

section Move

variable {L : Nat} {b : List Nat}

/-- The inner play, in whichever direction, moves the block from its
current state to the other one. -/
theorem exec_dirPlay (hL : 1 ≤ L)
    (hb : execB (emptyBoard L) b = doneBoard L) (v : Bool) :
    execB (blk L v) (dirPlay ([v]) 0 b) = blk L (!v) := by
  have h0 : nth ([v] : Board) 0 = v := by simp [nth]
  cases v with
  | false =>
      show execB (blk L false) (dirPlay [false] 0 b) = blk L true
      rw [dirPlay, h0]
      simpa [blk] using hb
  | true =>
      show execB (blk L true) (dirPlay [true] 0 b) = blk L false
      rw [dirPlay, h0]
      have h := exec_reverse_cancel (emptyBoard L) b
      rw [hb] at h
      simpa [blk] using h

/-- The inner play is legal in whichever direction. -/
theorem legal_dirPlay (hlegb : legalB (emptyBoard L) b = true)
    (hb : execB (emptyBoard L) b = doneBoard L) (v : Bool) :
    legalB (blk L v) (dirPlay ([v]) 0 b) = true := by
  have h0 : nth ([v] : Board) 0 = v := by simp [nth]
  cases v with
  | false =>
      show legalB (blk L false) (dirPlay [false] 0 b) = true
      rw [dirPlay, h0]
      simpa [blk] using hlegb
  | true =>
      show legalB (blk L true) (dirPlay [true] 0 b) = true
      rw [dirPlay, h0]
      have h := legal_reverse (emptyBoard L) b hlegb
      rw [hb] at h
      simpa [blk] using h

/-- The inner play has the same peak in whichever direction. -/
theorem maxOnes_dirPlay (hb : execB (emptyBoard L) b = doneBoard L) (v : Bool) :
    maxOnes (blk L v) (dirPlay ([v]) 0 b) = maxOnes (emptyBoard L) b := by
  have h0 : nth ([v] : Board) 0 = v := by simp [nth]
  cases v with
  | false =>
      show maxOnes (blk L false) (dirPlay [false] 0 b) = _
      rw [dirPlay, h0]
      simp [blk]
  | true =>
      show maxOnes (blk L true) (dirPlay [true] 0 b) = _
      rw [dirPlay, h0]
      have h := maxOnes_reverse (emptyBoard L) b
      rw [hb] at h
      simpa [blk] using h

theorem dirPlay_eq (c : Board) (i : Nat) (b : List Nat) :
    dirPlay c i b = dirPlay ([nth c i]) 0 b := by
  unfold dirPlay
  simp [nth]

end Move

-- ------------------------------------------------------------------
-- The four laws
-- ------------------------------------------------------------------

section Laws

variable {L : Nat} {b : List Nat}

/-- **THE COMPOSITE LANDS ON THE BLOW-UP.** -/
theorem exec_expand (hL : 1 ≤ L) (hrb : ∀ j ∈ b, j < L)
    (hb : execB (emptyBoard L) b = doneBoard L) :
    ∀ (a : List Nat) (c : Board), (∀ i ∈ a, i < c.length) →
      execB (blow L c) (expand L b c a) = blow L (execB c a)
  | [], _, _ => rfl
  | i :: rest, c, hr => by
      have hi : i < c.length := hr i (by simp)
      have hstep : execB (blow L c) (liftAbove (i * L) (dirPlay c i b))
          = blow L (toggle c i) := by
        have hP : (blow L (c.take i)).length = i * L := by
          rw [blow_length, List.length_take, Nat.min_eq_left (by omega)]
        rw [blow_split L hi, ← hP, exec_lift_append]
        have hpad : execB (blk L (nth c i) ++ blow L (c.drop (i + 1)))
            (dirPlay c i b)
            = execB (blk L (nth c i)) (dirPlay c i b)
              ++ blow L (c.drop (i + 1)) := by
          refine execB_pad _ _ _ ?_
          intro j hj
          rw [blk_length]
          unfold dirPlay at hj
          split at hj
          · exact hrb j (List.mem_reverse.mp hj)
          · exact hrb j hj
        rw [hpad, dirPlay_eq c i b, exec_dirPlay hL hb]
        rw [blow_split L (c := toggle c i) (i := i) (by simpa using hi),
          take_toggle_self, drop_toggle_succ, nth_toggle_self c hi,
          ← List.append_assoc]
      rw [expand_cons, exec_append, hstep]
      exact exec_expand hL hrb hb rest (toggle c i)
        (fun j hj => by simpa using hr j (by simp [hj]))

/-- **THE COMPOSITE IS LEGAL.**  The foundation of block `i` is the top
cell of block `i - 1`, which is what the outer `okMove` provides. -/
theorem legal_expand (hL : 1 ≤ L) (hrb : ∀ j ∈ b, j < L)
    (hlegb : legalB (emptyBoard L) b = true)
    (hb : execB (emptyBoard L) b = doneBoard L) :
    ∀ (a : List Nat) (c : Board), (∀ i ∈ a, i < c.length) →
      legalB c a = true → legalB (blow L c) (expand L b c a) = true
  | [], _, _, _ => rfl
  | i :: rest, c, hr, hleg => by
      have hi : i < c.length := hr i (by simp)
      have hok : okMove c i = true ∧ legalB (toggle c i) rest = true := by
        simpa [legalB, Bool.and_eq_true] using hleg
      have hP : (blow L (c.take i)).length = i * L := by
        rw [blow_length, List.length_take, Nat.min_eq_left (by omega)]
      have hstep : legalB (blow L c) (liftAbove (i * L) (dirPlay c i b)) = true := by
        rw [blow_split L hi, ← hP]
        refine legal_lift_append _ _ _ ?_ ?_
        · -- the foundation
          rcases Nat.eq_zero_or_pos i with rfl | hipos
          · left; rw [hP]; omega
          · right
            have hprev : nth c (i - 1) = true := by
              have := hok.1
              simp only [okMove, Bool.or_eq_true, beq_iff_eq] at this
              rcases this with h | h
              · omega
              · exact h
            have hlen : (i - 1) < (c.take i).length := by
              rw [List.length_take, Nat.min_eq_left (by omega)]; omega
            have htop := nth_blow_top hL (c.take i) (i - 1) hlen
            have hval : nth (c.take i) (i - 1) = true := by
              rw [nth_take c i (i - 1) (by omega)]
              exact hprev
            rw [hval] at htop
            have hidx : i * L - 1 = (i - 1) * L + (L - 1) := by
              obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
              obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
              simp [Nat.succ_mul]
            rw [hP, hidx]
            exact htop
        · -- legality inside the block
          refine legalB_pad _ _ _ ?_ |>.trans ?_
          · intro j hj
            rw [blk_length]
            unfold dirPlay at hj
            split at hj
            · exact hrb j (List.mem_reverse.mp hj)
            · exact hrb j hj
          · rw [dirPlay_eq c i b]; exact legal_dirPlay hlegb hb _
      have hexec : execB (blow L c) (liftAbove (i * L) (dirPlay c i b))
          = blow L (toggle c i) := by
        have := exec_expand (b := b) hL hrb hb [i] c (by simpa using hi)
        simpa [execB] using this
      rw [expand_cons, legal_append, hstep, hexec, Bool.true_and]
      exact legal_expand hL hrb hlegb hb rest (toggle c i)
        (fun j hj => by simpa using hr j (by simp [hj])) hok.2

/-- **THE PEAKS ADD, MINUS ONE.**  While the inner play runs in block
`i`, the other blocks carry one pebble each, and there are at most
`(outer peak) - 1` of them. -/
theorem maxOnes_expand (hL : 1 ≤ L) (hrb : ∀ j ∈ b, j < L)
    (hb : execB (emptyBoard L) b = doneBoard L)
    (hQ : 1 ≤ maxOnes (emptyBoard L) b) :
    ∀ (a : List Nat) (c : Board), (∀ i ∈ a, i < c.length) →
      maxOnes (blow L c) (expand L b c a) + 1
        ≤ maxOnes c a + maxOnes (emptyBoard L) b
  | [], c, _ => by
      show ones (blow L c) + 1 ≤ ones c + _
      rw [ones_blow hL]
      omega
  | i :: rest, c, hr => by
      have hi : i < c.length := hr i (by simp)
      have hP : (blow L (c.take i)).length = i * L := by
        rw [blow_length, List.length_take, Nat.min_eq_left (by omega)]
      -- the head: the other blocks plus the inner peak
      have hhead : maxOnes (blow L c) (liftAbove (i * L) (dirPlay c i b))
          ≤ ones (c.take i) + ones (c.drop (i + 1))
            + maxOnes (emptyBoard L) b := by
        rw [blow_split L hi, ← hP]
        refine Nat.le_trans (maxOnes_lift_append _ _ _) ?_
        rw [ones_blow hL]
        have hpad : maxOnes (blk L (nth c i) ++ blow L (c.drop (i + 1)))
            (dirPlay c i b)
            = maxOnes (blk L (nth c i)) (dirPlay c i b)
              + ones (blow L (c.drop (i + 1))) := by
          refine maxOnes_pad _ _ _ ?_
          intro j hj
          rw [blk_length]
          unfold dirPlay at hj
          split at hj
          · exact hrb j (List.mem_reverse.mp hj)
          · exact hrb j hj
        rw [hpad, ones_blow hL, dirPlay_eq c i b, maxOnes_dirPlay hb]
        omega
      -- one of `c` and `toggle c i` has super-cell `i` on
      have hsplitc : ones c = ones (c.take i)
          + (if nth c i then 1 else 0) + ones (c.drop (i + 1)) := by
        have h1 := ones_take_drop c i
        have hd : c.drop i = c[i] :: c.drop (i + 1) := List.drop_eq_getElem_cons hi
        have hn : nth c i = c[i] := by
          rw [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
        rw [hd] at h1
        rw [hn]
        cases hv : c[i] <;> simp [ones, hv] at h1 ⊢ <;> omega
      have hsplitt : ones (toggle c i) = ones (c.take i)
          + (if nth (toggle c i) i then 1 else 0) + ones (c.drop (i + 1)) := by
        have h1 := ones_take_drop (toggle c i) i
        have hi' : i < (toggle c i).length := by simpa using hi
        have hd : (toggle c i).drop i = (toggle c i)[i] :: (toggle c i).drop (i + 1) :=
          List.drop_eq_getElem_cons hi'
        have hn : nth (toggle c i) i = (toggle c i)[i] := by
          rw [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
        rw [hd] at h1
        rw [hn, take_toggle_self, drop_toggle_succ] at *
        cases hv : (toggle c i)[i] <;> simp [ones, hv] at h1 ⊢ <;> omega
      have hflip : nth (toggle c i) i = !nth c i := nth_toggle_self c hi
      have hone : ones (c.take i) + ones (c.drop (i + 1)) + 1
          ≤ max (ones c) (ones (toggle c i)) := by
        rw [hflip] at hsplitt
        cases hv : nth c i <;> simp [hv] at hsplitc hsplitt <;> omega
      -- the tail
      have htail := maxOnes_expand hL hrb hb hQ rest (toggle c i)
        (fun j hj => by simpa using hr j (by simp [hj]))
      have hexec : execB (blow L c) (liftAbove (i * L) (dirPlay c i b))
          = blow L (toggle c i) := by
        have := exec_expand (b := b) hL hrb hb [i] c (by simpa using hi)
        simpa [execB] using this
      have hones : ones (toggle c i) ≤ maxOnes (toggle c i) rest :=
        ones_le_maxOnes _ _
      have hmono : max (ones c) (ones (toggle c i))
          ≤ max (ones c) (maxOnes (toggle c i) rest) :=
        Nat.max_le.mpr ⟨Nat.le_max_left _ _,
          Nat.le_trans hones (Nat.le_max_right _ _)⟩
      have hmax2 := Nat.le_max_right (ones c) (maxOnes (toggle c i) rest)
      rw [expand_cons, maxOnes_append, hexec]
      show max (maxOnes (blow L c) (liftAbove (i * L) (dirPlay c i b)))
        (maxOnes (blow L (toggle c i)) (expand L b (toggle c i) rest)) + 1
        ≤ max (ones c) (maxOnes (toggle c i) rest) + maxOnes (emptyBoard L) b
      rcases Nat.le_total (maxOnes (blow L c) (liftAbove (i * L) (dirPlay c i b)))
        (maxOnes (blow L (toggle c i)) (expand L b (toggle c i) rest)) with h | h
      · rw [Nat.max_eq_right h]; omega
      · rw [Nat.max_eq_left h]; omega

end Laws

-- ------------------------------------------------------------------
-- Submultiplicativity
-- ------------------------------------------------------------------

/-- **BLOCK SIMULATION AS A REACH.**  `N` blocks of `L` cells, driven by
a play for `N` cells with `p` pebbles and one for `L` cells with `q`. -/
theorem reachIn_block {N L p q ta tb : Nat} (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hA : ReachIn N p ta) (hB : ReachIn L q tb) :
    ReachIn (N * L) (p + q - 1) (ta * tb) := by
  obtain ⟨a, hla, hra, hlega, hexa, hpka⟩ := hA
  obtain ⟨b, hlb, hrb, hlegb, hexb, hpkb⟩ := hB
  have hlenN : (emptyBoard N).length = N := by simp
  have hra' : ∀ i ∈ a, i < (emptyBoard N).length := by
    intro i hi; rw [hlenN]; exact hra i hi
  have hQ : 1 ≤ maxOnes (emptyBoard L) b := by
    obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
    have h := ones_prefix_le_maxOnes b (emptyBoard (m + 1)) b.length
    rw [List.take_of_length_le (Nat.le_refl _), hexb, ones_doneBoard] at h
    omega
  refine ⟨expand L b (emptyBoard N) a, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_expand]
    exact Nat.mul_le_mul hla hlb
  · intro x hx
    obtain ⟨i, hi, j, hj, rfl⟩ := mem_expand L b hrb a (emptyBoard N) x hx
    have := hra i hi
    calc j + i * L < L + i * L := by omega
      _ = (i + 1) * L := by rw [Nat.succ_mul]; omega
      _ ≤ N * L := Nat.mul_le_mul_right L (by omega)
  · have h := legal_expand hL hrb hlegb hexb a (emptyBoard N) hra' hlega
    rwa [blow_emptyBoard] at h
  · have h := exec_expand hL hrb hexb a (emptyBoard N) hra'
    rw [hexa, blow_emptyBoard, blow_doneBoard hL N] at h
    exact h
  · have h := maxOnes_expand hL hrb hexb hQ a (emptyBoard N) hra'
    rw [blow_emptyBoard] at h
    omega

/-- **THE COST IS SUBMULTIPLICATIVE, AT THE LEVEL OF THE GAME.** -/
theorem gameF_block {N L p q : Nat} (hL : 1 ≤ L) (hq : 1 ≤ q)
    (h1 : ∃ t, ReachIn N p t) (h2 : ∃ t, ReachIn L q t) :
    gameF (N * L) (p + q - 1) ≤ gameF N p * gameF L q :=
  gameF_le (reachIn_block hL hq (reachIn_gameF h1) (reachIn_gameF h2))

/-- **`Submult fRow`, PROVED** — the letter's Lemma 1.  Read `2^{p+q-2}`
cells as `2^{p-1}` blocks of `2^{q-1}`: the outer play costs `f_p` and
each of its moves costs `f_q`, while the peaks add minus one. -/
theorem submult_fRow : Submult fRow := by
  intro p q hp hq
  rcases Nat.lt_or_ge p 2 with hp1 | hp2
  · have : p = 1 := by omega
    subst this
    have : fRow 1 = 1 := rfl
    rw [this, Nat.one_mul, show 1 + q - 1 = q from by omega]
  rcases Nat.lt_or_ge q 2 with hq1 | hq2
  · have : q = 1 := by omega
    subst this
    have : fRow 1 = 1 := rfl
    rw [this, Nat.mul_one, show p + 1 - 1 = p from by omega]
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 2 := ⟨p - 2, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 2 := ⟨q - 2, by omega⟩
  have hNL : 2 ^ (s + 1) * 2 ^ (t + 1) = 2 ^ (s + t + 2) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hlvl : s + 2 + (t + 2) - 1 = s + t + 3 := by omega
  have h1 : ∃ x, ReachIn (2 ^ (s + 1)) (s + 2) x :=
    (reachIn_iff (2 ^ (s + 1)) s (two_pow_ge_one (s + 1))).mpr (Nat.le_refl _)
  have h2 : ∃ x, ReachIn (2 ^ (t + 1)) (t + 2) x :=
    (reachIn_iff (2 ^ (t + 1)) t (two_pow_ge_one (t + 1))).mpr (Nat.le_refl _)
  have hblock := gameF_block (N := 2 ^ (s + 1)) (L := 2 ^ (t + 1))
    (p := s + 2) (q := t + 2) (two_pow_ge_one (t + 1)) (by omega) h1 h2
  rw [hNL, hlvl] at hblock
  have e1 : gameF (2 ^ (s + 1)) (s + 2) = fRow (s + 2) := gameF_eq_fRow_all s
  have e2 : gameF (2 ^ (t + 1)) (t + 2) = fRow (t + 2) := gameF_eq_fRow_all t
  have e3 : gameF (2 ^ (s + t + 2)) (s + t + 3) = fRow (s + t + 3) := by
    have := gameF_eq_fRow_all (s + t + 1)
    simpa using this
  rw [e1, e2, e3] at hblock
  rw [hlvl]
  exact hblock

-- ------------------------------------------------------------------
-- The growth rate, with nothing carried
-- ------------------------------------------------------------------

open RevPebbling.GrowthClosedForm RevPebbling.GrowthCertified
open RevPebbling.Dispersion4731Growth

/-- **THE GROWTH RATE OF SPACE-OPTIMAL REVERSIBLE PEBBLING**, as a real
number with no hypothesis attached.  `GrowthRate.growth` takes
submultiplicativity and positivity as arguments; both are now theorems.

We call this number the **Knill constant**: `f_p = F(2^{p-1}, p)` is
Knill's space-optimal cost, and `c` is its growth rate.  The name is
attached to THIS object, which provably exists (Fekete's lemma on
`log f_p`, which is subadditive by `submult_fRow`) and which the
development brackets as `2.5170648368938161205 ≤ c ≤ 2.5174407`.  It is
NOT attached to `2^{1+κ*} = 2.5170648368938161206…`, which is the
CONJECTURED value of `c` (`CriticalRoot`, `rocq/KappaStar.v`). -/
noncomputable def c : ℝ := growth submult_fRow pos_fRow

/-- `c ≤ 2.6106` — the published upper bound, unconditional. -/
theorem c_le_2_6106 : c ≤ 26106 / 10000 :=
  RevPebbling.GrowthCertified.growth_le_2_6106 submult_fRow

/-- `c ≤ 2√2` — the closed-form upper bound, unconditional. -/
theorem c_le_two_sqrt_two : c ≤ 2 * Real.sqrt 2 :=
  growth_le_two_sqrt_two submult_fRow

/-- `2.51706472 ≤ c` — the dispersion lower bound, unconditional. -/
theorem c_ge_2_51706472 : (251706472 / 100000000 : ℝ) ≤ c :=
  growth_ge_2_51706472 submult_fRow

end RevPebbling.BlockSim
