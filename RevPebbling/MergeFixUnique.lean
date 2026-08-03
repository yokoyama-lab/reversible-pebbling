import RevPebbling.CountRecursion

/-!
# The row equation determines the row (this work, link (3))

`gen_merge_rep` / `rowIter_succ_rep` say that the generated row
satisfies the self-referential *row equation*

  `cur = 1 :: smerge prev (zipWith (+) cur prev)`.

This file proves the converse direction that was missing: the equation
has **at most one** solution, so *any* list satisfying it — however it
was produced — is the generated row.

Why this is the piece that was blocking link (3).  The artifact's
machine-checked values (`f_10` … `f_60`) come from the run-length
generator `RLEPebble.nextRow`, a two-pointer greedy over `Array`s,
while every general theorem is about `rowIter`.  Proving those equal by
simulating the imperative generator step by step is a program-
verification task.  With `mergeFix_unique` it is no longer needed:
it suffices to *check the equation* on the produced row, which is a
run-level computation, and uniqueness identifies the result with
`rowIter`.

The proof is a prefix induction.  Entry `i` of `1 :: smerge prev B`
depends only on entries `< i` of `B`, and `B_j = cur_j + prev_j`
depends only on entry `j` of `cur`; so the first `k` entries of a
solution are determined by the first `k − 1`, and induction on `k`
pins the whole list down.  No sortedness or positivity is needed.
-/

namespace RevPebbling.MergeFixUnique

open RevPebbling.DifferenceMergeProperty RevPebbling.CountRecursion

/-- **The row equation.**  `cur` is the row generated from `prev`:
its head is `δ(2,S) = 1` and its tail is the sorted merge of the
A-stream `prev` with the B-stream `cur + prev` (read pointwise). -/
def MergeFix (prev cur : List Nat) : Prop :=
  cur = 1 :: smerge prev (List.zipWith (· + ·) cur prev)

-- Unfolding lemmas for `smerge` (its patterns overlap, so the raw
-- equation lemmas carry side conditions).

theorem smerge_nil_left (b : List Nat) : smerge [] b = b := by
  rw [smerge]

theorem smerge_nil_right : ∀ (a : List Nat), smerge a [] = a
  | [] => by rw [smerge]
  | _ :: _ => by rw [smerge] <;> simp

theorem smerge_cons_cons (x y : Nat) (xs ys : List Nat) :
    smerge (x :: xs) (y :: ys)
      = if x ≤ y then x :: smerge xs (y :: ys)
        else y :: smerge (x :: xs) ys := by
  rw [smerge]

/-- Taking a prefix of a pointwise sum. -/
theorem zipWith_add_take : ∀ (k : Nat) (a b : List Nat),
    (List.zipWith (· + ·) a b).take k
      = List.zipWith (· + ·) (a.take k) (b.take k)
  | 0, _, _ => by simp
  | _ + 1, [], _ => by simp
  | _ + 1, _ :: _, [] => by simp
  | k + 1, x :: xs, y :: ys => by
      simp only [List.zipWith_cons_cons, List.take_succ_cons,
        List.cons.injEq, true_and]
      exact zipWith_add_take k xs ys

/-- **Prefix determination of the merge.**  The first `k` entries of a
sorted merge depend only on the first `k` entries of each argument:
producing `k` outputs consumes at most `k` inputs from either side. -/
theorem smerge_take_congr : ∀ (k : Nat) (a a' b b' : List Nat),
    a.take k = a'.take k → b.take k = b'.take k →
    (smerge a b).take k = (smerge a' b').take k
  | 0, _, _, _, _, _, _ => by simp
  | k + 1, a, a', b, b', ha, hb => by
      match a, a' with
      | [], [] =>
          rw [smerge_nil_left, smerge_nil_left]
          exact hb
      | [], _ :: _ => simp at ha
      | _ :: _, [] => simp at ha
      | x :: xs, x' :: xs' =>
          simp only [List.take_succ_cons, List.cons.injEq] at ha
          obtain ⟨hx, hxs⟩ := ha
          subst hx
          match b, b' with
          | [], [] =>
              rw [smerge_nil_right, smerge_nil_right]
              simp only [List.take_succ_cons, List.cons.injEq, true_and]
              exact hxs
          | [], _ :: _ => simp at hb
          | _ :: _, [] => simp at hb
          | y :: ys, y' :: ys' =>
              simp only [List.take_succ_cons, List.cons.injEq] at hb
              obtain ⟨hy, hys⟩ := hb
              subst hy
              -- prefixes of the tails agree one step shorter
              have hxs' : xs.take k = xs'.take k := hxs
              have hys' : ys.take k = ys'.take k := hys
              have hbb : (y :: ys).take k = (y :: ys').take k := by
                match k with
                | 0 => simp
                | k + 1 =>
                    simp only [List.take_succ_cons, List.cons.injEq,
                      true_and]
                    have := congrArg (List.take k) hys'
                    simpa [List.take_take, Nat.min_eq_left,
                      Nat.le_succ] using this
              have haa : (x :: xs).take k = (x :: xs').take k := by
                match k with
                | 0 => simp
                | k + 1 =>
                    simp only [List.take_succ_cons, List.cons.injEq,
                      true_and]
                    have := congrArg (List.take k) hxs'
                    simpa [List.take_take, Nat.min_eq_left,
                      Nat.le_succ] using this
              rw [smerge_cons_cons, smerge_cons_cons]
              by_cases hle : x ≤ y
              · simp only [hle, if_true, List.take_succ_cons,
                  List.cons.injEq, true_and]
                exact smerge_take_congr k xs xs' (y :: ys) (y :: ys')
                  hxs' hbb
              · simp only [hle, if_false, List.take_succ_cons,
                  List.cons.injEq, true_and]
                exact smerge_take_congr k (x :: xs) (x :: xs') ys ys'
                  haa hys'

/-- Solutions of the row equation agree on every prefix. -/
theorem mergeFix_take {prev cur cur' : List Nat}
    (h : MergeFix prev cur) (h' : MergeFix prev cur') :
    ∀ k, cur.take k = cur'.take k
  | 0 => by simp
  | k + 1 => by
      have ih := mergeFix_take h h' k
      have hB : (List.zipWith (· + ·) cur prev).take k
          = (List.zipWith (· + ·) cur' prev).take k := by
        rw [zipWith_add_take, zipWith_add_take, ih]
      have hm := smerge_take_congr k prev prev
        (List.zipWith (· + ·) cur prev) (List.zipWith (· + ·) cur' prev)
        rfl hB
      calc cur.take (k + 1)
          = (1 :: smerge prev (List.zipWith (· + ·) cur prev)).take (k + 1) := by
            rw [← h]
        _ = 1 :: (smerge prev (List.zipWith (· + ·) cur prev)).take k := by
            simp
        _ = 1 :: (smerge prev (List.zipWith (· + ·) cur' prev)).take k := by
            rw [hm]
        _ = (1 :: smerge prev (List.zipWith (· + ·) cur' prev)).take (k + 1) := by
            simp
        _ = cur'.take (k + 1) := by rw [← h']

/-- **UNIQUENESS, fully general.**  The row equation has at most one
solution: no sortedness, positivity or length hypothesis is needed,
because the equation determines each entry from the earlier ones. -/
theorem mergeFix_unique {prev cur cur' : List Nat}
    (h : MergeFix prev cur) (h' : MergeFix prev cur') : cur = cur' := by
  have hk := mergeFix_take h h' (cur.length + cur'.length)
  rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hk
  exact hk

/-- The generated row solves the equation (this is `rowIter_succ_rep`
in the vocabulary of this file). -/
theorem rowIter_mergeFix (s : Nat) : MergeFix (rowIter s) (rowIter (s + 1)) :=
  rowIter_succ_rep s

/-- **THE IDENTIFICATION.**  Any list satisfying the row equation over
`rowIter s` *is* `rowIter (s+1)`.

This is what a fast external generator has to establish about its
output; it no longer has to be simulated step by step. -/
theorem eq_rowIter_of_mergeFix {s : Nat} {cur : List Nat}
    (h : MergeFix (rowIter s) cur) : cur = rowIter (s + 1) :=
  mergeFix_unique h (rowIter_mergeFix s)

/-- The length of a solution is forced: `|cur| = 2|prev| + 1`. -/
theorem mergeFix_length {prev cur : List Nat} (h : MergeFix prev cur) :
    cur.length = 2 * prev.length + 1 := by
  have hlen := congrArg List.length h
  rw [List.length_cons, smerge_length, List.length_zipWith] at hlen
  rcases Nat.le_total cur.length prev.length with hc | hc
  · rw [Nat.min_eq_left hc] at hlen
    omega
  · rw [Nat.min_eq_right hc] at hlen
    omega

end RevPebbling.MergeFixUnique
