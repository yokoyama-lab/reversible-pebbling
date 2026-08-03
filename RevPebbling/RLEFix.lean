import RevPebbling.MergeFixUnique

/-!
# Run-length arithmetic and a verified checker for the row equation
(this work, link (3))

`MergeFixUnique` reduces "is this row the generated row?" to "does it
satisfy the row equation?".  This file makes that question *checkable
on run-length data*, which is the form in which large rows exist (row
60 has `2^59` entries but only 13.1 M runs).

Three simulation lemmas, all unconditional except where noted:

* `expand_rleMerge` : run-level merge simulates `smerge` — if `v ≤ w`
  the whole run `(v,c)` may be emitted at once, because sortedness
  makes every remaining entry at least `v`.  This is the only lemma
  that needs the runs to be value-sorted;
* `expand_rleZipAdd` : run-level pointwise addition simulates
  `zipWith (+)`, splitting at the shorter run;
* `expand_normRuns` : normalisation (drop empty runs, fuse adjacent
  equal values) preserves the expansion.

`checkFix` puts them together into a `Bool` that a fast external
generator's output can be run through: `mergeFix_of_checkFix` says a
`true` answer *proves* the row equation, and
`eq_rowIter_of_checkFix` then identifies the expansion with
`rowIter`.  Only soundness is proved (a `false` answer means nothing),
which is all a certificate checker needs.
-/

namespace RevPebbling.RLEFix

open RevPebbling.DifferenceMergeProperty RevPebbling.MergeFixUnique

/-- A run-length encoded list: `(value, count)` runs. -/
abbrev Runs := List (Nat × Nat)

/-- The list a run-length encoding stands for. -/
def expand : Runs → List Nat
  | [] => []
  | (v, c) :: A => List.replicate c v ++ expand A

@[simp] theorem expand_nil : expand [] = [] := rfl

@[simp] theorem expand_cons (v c : Nat) (A : Runs) :
    expand ((v, c) :: A) = List.replicate c v ++ expand A := rfl

/-- The values of the runs, in order. -/
abbrev vals (A : Runs) : List Nat := A.map Prod.fst

/-- Value-sorted runs (the shape every generated row has). -/
abbrev RunsSorted (A : Runs) : Prop := NDec (vals A)

theorem mem_expand_imp : ∀ {A : Runs} {z : Nat}, z ∈ expand A → z ∈ vals A
  | [], _, h => by simp at h
  | (v, c) :: A, z, h => by
      simp only [expand_cons, List.mem_append] at h
      rcases h with hrep | htail
      · have := List.eq_of_mem_replicate hrep
        simp [vals, this]
      · exact List.mem_cons_of_mem _ (mem_expand_imp htail)

theorem head_le_of_sorted {v c : Nat} {A : Runs}
    (h : RunsSorted ((v, c) :: A)) : ∀ z ∈ expand A, v ≤ z := by
  intro z hz
  have hz' := mem_expand_imp hz
  cases h with
  | cons hhead _ => exact hhead z hz'

theorem sorted_tail {v c : Nat} {A : Runs}
    (h : RunsSorted ((v, c) :: A)) : RunsSorted A := by
  cases h with | cons _ ht => exact ht

-- ------------------------------------------------------------------
-- Emitting a whole run of a sorted merge
-- ------------------------------------------------------------------

/-- A run at or below everything in `b` comes out of the merge whole. -/
theorem smerge_replicate_left : ∀ (c v : Nat) (a b : List Nat),
    (∀ z ∈ b, v ≤ z) →
    smerge (List.replicate c v ++ a) b = List.replicate c v ++ smerge a b
  | 0, _, _, _, _ => by simp
  | _ + 1, _, _, [], _ => by rw [smerge_nil_right, smerge_nil_right]
  | c + 1, v, a, y :: ys, hb => by
      have hvy : v ≤ y := hb y (by simp)
      simp only [List.replicate_succ, List.cons_append]
      rw [smerge_cons_cons, if_pos hvy,
        smerge_replicate_left c v a (y :: ys) hb]

/-- A run strictly below everything in `a` comes out of the merge
whole (the merge prefers the left argument on ties, so this side needs
a strict inequality). -/
theorem smerge_replicate_right : ∀ (d w : Nat) (a b : List Nat),
    (∀ z ∈ a, ¬ z ≤ w) →
    smerge a (List.replicate d w ++ b) = List.replicate d w ++ smerge a b
  | 0, _, _, _, _ => by simp
  | _ + 1, _, [], _, _ => by rw [smerge_nil_left, smerge_nil_left]
  | d + 1, w, x :: xs, b, ha => by
      have hxw : ¬ x ≤ w := ha x (by simp)
      simp only [List.replicate_succ, List.cons_append]
      rw [smerge_cons_cons, if_neg hxw,
        smerge_replicate_right d w (x :: xs) b ha]

-- ------------------------------------------------------------------
-- Run-level merge
-- ------------------------------------------------------------------

/-- Sorted merge on run-length data: emit the smaller-valued run whole. -/
def rleMerge : Runs → Runs → Runs
  | [], B => B
  | A, [] => A
  | (v, c) :: A, (w, d) :: B =>
      if v ≤ w then (v, c) :: rleMerge A ((w, d) :: B)
      else (w, d) :: rleMerge ((v, c) :: A) B
  termination_by A B => A.length + B.length

theorem rleMerge_nil_left (B : Runs) : rleMerge [] B = B := by rw [rleMerge]

theorem rleMerge_nil_right : ∀ (A : Runs), rleMerge A [] = A
  | [] => by rw [rleMerge]
  | _ :: _ => by rw [rleMerge] <;> simp

theorem rleMerge_cons_cons (v c w d : Nat) (A B : Runs) :
    rleMerge ((v, c) :: A) ((w, d) :: B)
      = if v ≤ w then (v, c) :: rleMerge A ((w, d) :: B)
        else (w, d) :: rleMerge ((v, c) :: A) B := by
  rw [rleMerge]

/-- **RUN-LEVEL MERGE SIMULATES `smerge`.** -/
theorem expand_rleMerge : ∀ (A B : Runs), RunsSorted A → RunsSorted B →
    expand (rleMerge A B) = smerge (expand A) (expand B)
  | [], B, _, _ => by rw [rleMerge_nil_left, expand_nil, smerge_nil_left]
  | (v, c) :: A, [], _, _ => by
      rw [rleMerge_nil_right, expand_nil, smerge_nil_right]
  | (v, c) :: A, (w, d) :: B, hA, hB => by
      rw [rleMerge_cons_cons]
      by_cases hvw : v ≤ w
      · -- the whole run `(v,c)` precedes everything in `B`
        have hbound : ∀ z ∈ List.replicate d w ++ expand B, v ≤ z := by
          intro z hz
          rcases List.mem_append.mp hz with hrep | htail
          · rw [List.eq_of_mem_replicate hrep]; exact hvw
          · exact Nat.le_trans hvw (head_le_of_sorted hB z htail)
        have ih := expand_rleMerge A ((w, d) :: B) (sorted_tail hA) hB
        simp only [expand_cons] at ih ⊢
        rw [if_pos hvw]
        simp only [expand_cons]
        rw [ih, smerge_replicate_left c v (expand A)
          (List.replicate d w ++ expand B) hbound]
      · -- symmetric: the whole run `(w,d)` precedes everything in `A`
        have hbound : ∀ z ∈ List.replicate c v ++ expand A, ¬ z ≤ w := by
          intro z hz
          rcases List.mem_append.mp hz with hrep | htail
          · rw [List.eq_of_mem_replicate hrep]; exact hvw
          · have := head_le_of_sorted hA z htail
            omega
        have ih := expand_rleMerge ((v, c) :: A) B hA (sorted_tail hB)
        simp only [expand_cons] at ih ⊢
        rw [if_neg hvw]
        simp only [expand_cons]
        rw [ih, smerge_replicate_right d w
          (List.replicate c v ++ expand A) (expand B) hbound]
  termination_by A B => A.length + B.length

/-- Tail-recursive merge: emitted runs are accumulated in reverse. -/
def rleMergeTR : Runs → Runs → Runs → Runs
  | acc, [], B => acc.reverseAux B
  | acc, (v, c) :: A, [] => acc.reverseAux ((v, c) :: A)
  | acc, (v, c) :: A, (w, d) :: B =>
      if v ≤ w then rleMergeTR ((v, c) :: acc) A ((w, d) :: B)
      else rleMergeTR ((w, d) :: acc) ((v, c) :: A) B
  termination_by _ A B => A.length + B.length

theorem rleMergeTR_eq : ∀ (acc A B : Runs),
    rleMergeTR acc A B = acc.reverse ++ rleMerge A B
  | acc, [], B => by rw [rleMergeTR, rleMerge_nil_left, List.reverseAux_eq]
  | acc, (v, c) :: A, [] => by
      rw [rleMergeTR, rleMerge_nil_right, List.reverseAux_eq]
  | acc, (v, c) :: A, (w, d) :: B => by
      rw [rleMergeTR, rleMerge_cons_cons]
      by_cases hvw : v ≤ w
      · rw [if_pos hvw, if_pos hvw, rleMergeTR_eq ((v, c) :: acc) A ((w, d) :: B)]
        simp
      · rw [if_neg hvw, if_neg hvw, rleMergeTR_eq ((w, d) :: acc) ((v, c) :: A) B]
        simp
  termination_by _ A B => A.length + B.length

/-- The implementation the compiler uses (see the `csimp` lemma). -/
def rleMergeFast (A B : Runs) : Runs := rleMergeTR [] A B

@[csimp] theorem rleMerge_eq_fast : @rleMerge = @rleMergeFast := by
  funext A B
  rw [rleMergeFast, rleMergeTR_eq]
  simp

-- ------------------------------------------------------------------
-- Run-level pointwise addition
-- ------------------------------------------------------------------

/-- Pointwise sum on run-length data: split at the shorter run. -/
def rleZipAdd : Runs → Runs → Runs
  | [], _ => []
  | _, [] => []
  | (v, c) :: A, (w, d) :: B =>
      if c ≤ d then (v + w, c) :: rleZipAdd A ((w, d - c) :: B)
      else (v + w, d) :: rleZipAdd ((v, c - d) :: A) B
  termination_by A B => A.length + B.length

theorem rleZipAdd_nil_left (B : Runs) : rleZipAdd [] B = [] := by rw [rleZipAdd]

theorem rleZipAdd_nil_right : ∀ (A : Runs), rleZipAdd A [] = []
  | [] => by rw [rleZipAdd]
  | _ :: _ => by rw [rleZipAdd] <;> simp

theorem rleZipAdd_cons_cons (v c w d : Nat) (A B : Runs) :
    rleZipAdd ((v, c) :: A) ((w, d) :: B)
      = if c ≤ d then (v + w, c) :: rleZipAdd A ((w, d - c) :: B)
        else (v + w, d) :: rleZipAdd ((v, c - d) :: A) B := by
  rw [rleZipAdd]

/-- Zipping two runs, the left one being the shorter. -/
theorem zipWith_replicate_le : ∀ (c d v w : Nat) (a b : List Nat), c ≤ d →
    List.zipWith (· + ·) (List.replicate c v ++ a) (List.replicate d w ++ b)
      = List.replicate c (v + w)
          ++ List.zipWith (· + ·) a (List.replicate (d - c) w ++ b)
  | 0, d, _, _, _, _, _ => by simp
  | c + 1, d + 1, v, w, a, b, h => by
      simp only [List.replicate_succ, List.cons_append,
        List.zipWith_cons_cons, List.cons.injEq, true_and,
        Nat.succ_sub_succ]
      exact zipWith_replicate_le c d v w a b (by omega)

/-- Zipping two runs, the right one being the shorter. -/
theorem zipWith_replicate_ge : ∀ (c d v w : Nat) (a b : List Nat), d ≤ c →
    List.zipWith (· + ·) (List.replicate c v ++ a) (List.replicate d w ++ b)
      = List.replicate d (v + w)
          ++ List.zipWith (· + ·) (List.replicate (c - d) v ++ a) b
  | _, 0, _, _, _, _, _ => by simp
  | c + 1, d + 1, v, w, a, b, h => by
      simp only [List.replicate_succ, List.cons_append,
        List.zipWith_cons_cons, List.cons.injEq, true_and,
        Nat.succ_sub_succ]
      exact zipWith_replicate_ge c d v w a b (by omega)

/-- **RUN-LEVEL ADDITION SIMULATES `zipWith (+)`.** -/
theorem expand_rleZipAdd : ∀ (A B : Runs),
    expand (rleZipAdd A B) = List.zipWith (· + ·) (expand A) (expand B)
  | [], B => by rw [rleZipAdd_nil_left, expand_nil]; simp
  | (v, c) :: A, [] => by rw [rleZipAdd_nil_right, expand_nil]; simp
  | (v, c) :: A, (w, d) :: B => by
      rw [rleZipAdd_cons_cons]
      by_cases hcd : c ≤ d
      · rw [if_pos hcd, expand_cons, expand_cons, expand_cons,
          expand_rleZipAdd A ((w, d - c) :: B), expand_cons,
          zipWith_replicate_le c d v w (expand A) (expand B) hcd]
      · have hdc : d ≤ c := by omega
        rw [if_neg hcd, expand_cons, expand_cons, expand_cons,
          expand_rleZipAdd ((v, c - d) :: A) B, expand_cons,
          zipWith_replicate_ge c d v w (expand A) (expand B) hdc]
  termination_by A B => A.length + B.length

/-- Every value produced by the run-level sum is at least the sum of
the two leading bounds. -/
theorem zipAdd_vals_ge : ∀ (A B : Runs) (v w : Nat),
    (∀ x ∈ vals A, v ≤ x) → (∀ y ∈ vals B, w ≤ y) →
    ∀ z ∈ vals (rleZipAdd A B), v + w ≤ z
  | [], B, v, w, _, _ => by rw [rleZipAdd_nil_left]; simp [vals]
  | (a, c) :: A, [], v, w, _, _ => by rw [rleZipAdd_nil_right]; simp [vals]
  | (a, c) :: A, (b, d) :: B, v, w, hA, hB => by
      have ha : v ≤ a := hA a (by simp [vals])
      have hb : w ≤ b := hB b (by simp [vals])
      have hA' : ∀ x ∈ vals A, v ≤ x := by
        intro x hx; exact hA x (by simp [vals] at hx ⊢; exact Or.inr hx)
      have hB' : ∀ y ∈ vals B, w ≤ y := by
        intro y hy; exact hB y (by simp [vals] at hy ⊢; exact Or.inr hy)
      rw [rleZipAdd_cons_cons]
      by_cases hcd : c ≤ d
      · rw [if_pos hcd]
        intro z hz
        simp only [vals, List.map_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · omega
        · exact zipAdd_vals_ge A ((b, d - c) :: B) v w hA' hB z (by
            simpa [vals] using hz)
      · rw [if_neg hcd]
        intro z hz
        simp only [vals, List.map_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · omega
        · exact zipAdd_vals_ge ((a, c - d) :: A) B v w hA hB' z (by
            simpa [vals] using hz)
  termination_by A B => A.length + B.length

/-- The run-level sum of two sorted rows is sorted. -/
theorem zipAdd_sorted : ∀ (A B : Runs), RunsSorted A → RunsSorted B →
    RunsSorted (rleZipAdd A B)
  | [], B, _, _ => by rw [rleZipAdd_nil_left]; exact List.Pairwise.nil
  | (a, c) :: A, [], _, _ => by
      rw [rleZipAdd_nil_right]; exact List.Pairwise.nil
  | (a, c) :: A, (b, d) :: B, hA, hB => by
      have hAt : RunsSorted A := sorted_tail hA
      have hBt : RunsSorted B := sorted_tail hB
      have haA : ∀ x ∈ vals A, a ≤ x := by
        cases hA with | cons hh _ => exact fun x hx => hh x (by simpa [vals] using hx)
      have hbB : ∀ y ∈ vals B, b ≤ y := by
        cases hB with | cons hh _ => exact fun y hy => hh y (by simpa [vals] using hy)
      have hbB' : ∀ y ∈ vals ((b, d - c) :: B), b ≤ y := by
        intro y hy
        simp only [vals, List.map_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Nat.le_refl _
        · exact hbB y (by simpa [vals] using hy)
      have haA' : ∀ x ∈ vals ((a, c - d) :: A), a ≤ x := by
        intro x hx
        simp only [vals, List.map_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Nat.le_refl _
        · exact haA x (by simpa [vals] using hx)
      have hBmod : RunsSorted ((b, d - c) :: B) := by
        cases hB with
        | cons hh ht => exact List.Pairwise.cons (by simpa [vals] using hh) ht
      have hAmod : RunsSorted ((a, c - d) :: A) := by
        cases hA with
        | cons hh ht => exact List.Pairwise.cons (by simpa [vals] using hh) ht
      rw [rleZipAdd_cons_cons]
      by_cases hcd : c ≤ d
      · rw [if_pos hcd]
        refine List.Pairwise.cons ?_ (zipAdd_sorted A ((b, d - c) :: B) hAt hBmod)
        intro z hz
        exact zipAdd_vals_ge A ((b, d - c) :: B) a b haA hbB' z
          (by simpa [vals] using hz)
      · rw [if_neg hcd]
        refine List.Pairwise.cons ?_ (zipAdd_sorted ((a, c - d) :: A) B hAmod hBt)
        intro z hz
        exact zipAdd_vals_ge ((a, c - d) :: A) B a b haA' hbB z
          (by simpa [vals] using hz)
  termination_by A B => A.length + B.length

/-- Tail-recursive pointwise addition. -/
def rleZipAddTR : Runs → Runs → Runs → Runs
  | acc, [], _ => acc.reverse
  | acc, (v, c) :: A, [] => acc.reverse
  | acc, (v, c) :: A, (w, d) :: B =>
      if c ≤ d then rleZipAddTR ((v + w, c) :: acc) A ((w, d - c) :: B)
      else rleZipAddTR ((v + w, d) :: acc) ((v, c - d) :: A) B
  termination_by _ A B => A.length + B.length

theorem rleZipAddTR_eq : ∀ (acc A B : Runs),
    rleZipAddTR acc A B = acc.reverse ++ rleZipAdd A B
  | acc, [], B => by rw [rleZipAddTR, rleZipAdd_nil_left]; simp
  | acc, (v, c) :: A, [] => by
      rw [rleZipAddTR, rleZipAdd_nil_right]; simp
  | acc, (v, c) :: A, (w, d) :: B => by
      rw [rleZipAddTR, rleZipAdd_cons_cons]
      by_cases hcd : c ≤ d
      · rw [if_pos hcd, if_pos hcd,
          rleZipAddTR_eq ((v + w, c) :: acc) A ((w, d - c) :: B)]
        simp
      · rw [if_neg hcd, if_neg hcd,
          rleZipAddTR_eq ((v + w, d) :: acc) ((v, c - d) :: A) B]
        simp
  termination_by _ A B => A.length + B.length

/-- The implementation the compiler uses (see the `csimp` lemma). -/
def rleZipAddFast (A B : Runs) : Runs := rleZipAddTR [] A B

@[csimp] theorem rleZipAdd_eq_fast : @rleZipAdd = @rleZipAddFast := by
  funext A B
  rw [rleZipAddFast, rleZipAddTR_eq]
  simp

-- ------------------------------------------------------------------
-- Normalisation (so that equal expansions can be compared as data)
-- ------------------------------------------------------------------

theorem replicate_add_split (c e v : Nat) :
    List.replicate (c + e) v = List.replicate c v ++ List.replicate e v := by
  induction c with
  | zero => simp
  | succ c ih =>
      have h : c + 1 + e = (c + e) + 1 := by omega
      simp only [h, List.replicate_succ, ih, List.cons_append]

/-- Push a run onto a normalised list, fusing an equal-valued head. -/
def consRun (v c : Nat) : Runs → Runs
  | [] => [(v, c)]
  | (w, e) :: R => if v = w then (v, c + e) :: R else (v, c) :: (w, e) :: R

theorem expand_consRun : ∀ (v c : Nat) (R : Runs),
    expand (consRun v c R) = List.replicate c v ++ expand R
  | v, c, [] => by rw [consRun]; simp
  | v, c, (w, e) :: R => by
      rw [consRun]
      by_cases hvw : v = w
      · subst hvw
        rw [if_pos rfl]
        simp only [expand_cons]
        rw [replicate_add_split, List.append_assoc]
      · rw [if_neg hvw]
        simp only [expand_cons]

theorem expand_append : ∀ (X Y : Runs),
    expand (X ++ Y) = expand X ++ expand Y
  | [], Y => by simp
  | (v, c) :: X, Y => by
      simp only [List.cons_append, expand_cons, expand_append X Y,
        List.append_assoc]

/-- Fuse a run into the head of the (reversed) normalised prefix. -/
def fuse (v c : Nat) : Runs → Runs
  | [] => [(v, c)]
  | (w, e) :: acc' =>
      if v = w then (v, e + c) :: acc' else (v, c) :: (w, e) :: acc'

theorem expand_fuse_reverse : ∀ (v c : Nat) (acc : Runs),
    expand (fuse v c acc).reverse
      = expand acc.reverse ++ List.replicate c v
  | v, c, [] => by rw [fuse]; simp
  | v, c, (w, e) :: acc' => by
      rw [fuse]
      by_cases hvw : v = w
      · subst hvw
        rw [if_pos rfl]
        simp only [List.reverse_cons, expand_append, expand_cons, expand_nil,
          List.append_nil, List.append_assoc]
        rw [replicate_add_split]
      · rw [if_neg hvw]
        simp only [List.reverse_cons, expand_append, expand_cons, expand_nil,
          List.append_nil, List.append_assoc]

/-- Normalisation, tail-recursively: walk left to right, fusing each
run into the accumulator's head when the values agree.  Written with an
accumulator because rows have millions of runs and the evaluator's
stack is finite. -/
def normAcc : Runs → Runs → Runs
  | acc, [] => acc.reverse
  | acc, (v, c) :: A => if c = 0 then normAcc acc A else normAcc (fuse v c acc) A

theorem expand_normAcc : ∀ (acc A : Runs),
    expand (normAcc acc A) = expand acc.reverse ++ expand A
  | acc, [] => by rw [normAcc]; simp
  | acc, (v, c) :: A => by
      rw [normAcc]
      by_cases hc : c = 0
      · subst hc
        rw [if_pos rfl, expand_normAcc acc A]
        simp
      · rw [if_neg hc, expand_normAcc (fuse v c acc) A, expand_fuse_reverse,
          expand_cons, List.append_assoc]

/-- Drop empty runs and fuse adjacent runs of equal value. -/
def normRuns (A : Runs) : Runs := normAcc [] A

/-- Normalisation preserves the expansion. -/
theorem expand_normRuns (A : Runs) : expand (normRuns A) = expand A := by
  rw [normRuns, expand_normAcc]
  simp

-- ------------------------------------------------------------------
-- The checker
-- ------------------------------------------------------------------

/-- Decidable value-sortedness of runs. -/
def runsSortedB : Runs → Bool
  | [] => true
  | (_, _) :: [] => true
  | (v, _) :: (w, e) :: A => v ≤ w && runsSortedB ((w, e) :: A)

theorem sorted_of_runsSortedB : ∀ {A : Runs}, runsSortedB A = true → RunsSorted A
  | [], _ => List.Pairwise.nil
  | (_, _) :: [], _ => by
      refine List.Pairwise.cons ?_ List.Pairwise.nil
      intro z hz
      simp at hz
  | (v, c) :: (w, e) :: A, h => by
      rw [runsSortedB, Bool.and_eq_true, decide_eq_true_eq] at h
      have ih : RunsSorted ((w, e) :: A) := sorted_of_runsSortedB h.2
      refine List.Pairwise.cons ?_ ih
      intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h.1
      · cases ih with
        | cons hh _ => exact Nat.le_trans h.1 (hh x (by simpa using hx))

/-- **THE CHECKER.**  `checkFix prev cur` verifies, on run-length
data, that `expand cur` satisfies the row equation over
`expand prev`: it recomputes the right-hand side
`1 :: smerge prev (cur + prev)` at run level and compares normal
forms. -/
def checkFix (prev cur : Runs) : Bool :=
  runsSortedB prev && runsSortedB cur &&
    (normRuns ((1, 1) :: rleMerge prev (rleZipAdd cur prev)) == normRuns cur)

/-- **SOUNDNESS.**  A `true` answer proves the row equation. -/
theorem mergeFix_of_checkFix {prev cur : Runs} (h : checkFix prev cur = true) :
    MergeFix (expand prev) (expand cur) := by
  rw [checkFix, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hsp, hsc⟩, heq⟩ := h
  have hp : RunsSorted prev := sorted_of_runsSortedB hsp
  have hc : RunsSorted cur := sorted_of_runsSortedB hsc
  -- the B-stream is sorted because both `cur` and `prev` are
  have hzs : RunsSorted (rleZipAdd cur prev) := zipAdd_sorted cur prev hc hp
  -- the two normal forms are equal, so the two expansions are
  have hnorm : expand ((1, 1) :: rleMerge prev (rleZipAdd cur prev))
      = expand cur := by
    rw [← expand_normRuns ((1, 1) :: rleMerge prev (rleZipAdd cur prev)),
      ← expand_normRuns cur, beq_iff_eq.mp heq]
  have key : expand ((1, 1) :: rleMerge prev (rleZipAdd cur prev))
      = 1 :: smerge (expand prev)
          (List.zipWith (· + ·) (expand cur) (expand prev)) := by
    rw [expand_cons, expand_rleMerge prev (rleZipAdd cur prev) hp hzs,
      expand_rleZipAdd]
    simp
  exact hnorm.symm.trans key

end RevPebbling.RLEFix
