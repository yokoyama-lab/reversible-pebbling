import Std

/-!
# The Merge Lemma: general core (this work, 追記18)

The Merge Lemma states that the halved difference row of Knill's
recursion at space S equals, as a multiset, {1} ∪ row(S-1) ∪ B where
B_i = δ(i,S) + δ(i,S-1).  Its mathematical heart is the exchange
principle for sorted streams, proved here in FULL GENERALITY:

  for sorted lists a, b and any split k + l = n,
    Σ take n (smerge a b) ≤ Σ take k a + Σ take l b       (le)
  and some split attains equality                          (exists),

together with multiset preservation (`smerge_count`) and sortedness
(`smerge_sorted`).  Hence the min-split DP value IS the merged prefix
sum -- the content of the Merge Lemma once Knill's recursion is
rewritten through prefix sums.

Remaining for the full self-referential closure (future work): the
prefix-sum rewriting F(n,S) - 3 = min_m [pre_B(m) + pre_A(n-m)] as a
Lean identity about a recursively defined F, and the well-founded
closure of the B-stream (whose entries reference the row being built
at strictly smaller indices).  The bounded instance is
`PebblingTheory.delta_merge_representation`.
-/

namespace GenJanus.MergeLemma

/-- Sorted (nondecreasing) merge of two lists. -/
def smerge : List Nat → List Nat → List Nat
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys =>
      if x ≤ y then x :: smerge xs (y :: ys) else y :: smerge (x :: xs) ys
  termination_by a b => a.length + b.length

/-- Nondecreasing. -/
abbrev NDec (l : List Nat) : Prop := l.Pairwise (· ≤ ·)

/-- Multiset preservation: element counts add. -/
theorem smerge_count (a b : List Nat) (v : Nat) :
    (smerge a b).count v = a.count v + b.count v := by
  fun_induction smerge a b with
  | case1 b => simp
  | case2 a => simp
  | case3 x xs y ys h ih => simp [List.count_cons, ih]; omega
  | case4 x xs y ys h ih => simp [List.count_cons, ih]; omega

theorem smerge_mem {z : Nat} (a b : List Nat) :
    z ∈ smerge a b ↔ z ∈ a ∨ z ∈ b := by
  fun_induction smerge a b with
  | case1 b => simp
  | case2 a => simp
  | case3 x xs y ys h ih => simp [ih, or_assoc]
  | case4 x xs y ys h ih =>
      simp [ih]
      constructor
      · rintro (rfl | (h1 | h2) | h3)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h2)
        · exact Or.inr (Or.inr h3)
      · rintro ((h1 | h2) | rfl | h3)
        · exact Or.inr (Or.inl (Or.inl h1))
        · exact Or.inr (Or.inl (Or.inr h2))
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h3)

/-- The merge of sorted lists is sorted. -/
theorem smerge_sorted (a b : List Nat) :
    NDec a → NDec b → NDec (smerge a b) := by
  fun_induction smerge a b with
  | case1 b => intro _ hb; exact hb
  | case2 a => intro ha _; exact ha
  | case3 x xs y ys h ih =>
      intro ha hb
      cases ha with | cons hax hxs =>
      have hb2 := hb
      cases hb2 with | cons hby hys =>
      refine List.Pairwise.cons ?_ (ih hxs hb)
      intro z hz
      rcases (smerge_mem xs (y :: ys)).mp hz with hza | hzb
      · exact hax z hza
      · rcases List.mem_cons.mp hzb with rfl | hzys
        · exact h
        · exact Nat.le_trans h (hby z hzys)
  | case4 x xs y ys h ih =>
      intro ha hb
      have ha2 := ha
      cases ha2 with | cons hax hxs =>
      cases hb with | cons hby hys =>
      have hyx : y ≤ x := Nat.le_of_lt (Nat.lt_of_not_le h)
      refine List.Pairwise.cons ?_ (ih ha hys)
      intro z hz
      rcases (smerge_mem (x :: xs) ys).mp hz with hza | hzb
      · rcases List.mem_cons.mp hza with rfl | hzxs
        · exact hyx
        · exact Nat.le_trans hyx (hax z hzxs)
      · exact hby z hzb

/-- Sum of a take grows by the indexed element. -/
theorem take_succ_sum : ∀ (l : List Nat) (n : Nat) (_ : n < l.length),
    (l.take (n + 1)).sum = (l.take n).sum + l[n]'(by omega)
  | x :: xs, 0, _ => by simp
  | x :: xs, n + 1, h => by
      simp only [List.take_succ_cons, List.sum_cons,
        List.getElem_cons_succ]
      rw [take_succ_sum xs n (by simpa using h)]
      omega

/-- In a sorted list the head bounds every indexed element. -/
theorem head_le_getElem {y : Nat} {ys : List Nat}
    (h : NDec (y :: ys)) (i : Nat) (hi : i < (y :: ys).length) :
    y ≤ (y :: ys)[i] := by
  match i with
  | 0 => simp
  | i + 1 =>
      have h2 := h
      cases h2 with | cons h' _ =>
      have hi' : i < ys.length := by simpa using hi
      have : (y :: ys)[i + 1] = ys[i] := by simp
      rw [this]
      exact h' _ (List.getElem_mem hi')

/-- Prepending an element ≤ the head costs no more than extending the
prefix by one, inside a sorted list. -/
theorem cons_prefix_step {x y : Nat} {ys : List Nat}
    (hxy : x ≤ y) (h : NDec (y :: ys)) (l : Nat)
    (hl : l < (y :: ys).length) :
    x + ((y :: ys).take l).sum ≤ ((y :: ys).take (l + 1)).sum := by
  rw [take_succ_sum _ _ hl]
  have := head_le_getElem h l hl
  omega

/-- EXCHANGE (≤ direction), fully general. -/
theorem smerge_take_le (a b : List Nat) :
    NDec a → NDec b → ∀ k l, k ≤ a.length → l ≤ b.length →
      ((smerge a b).take (k + l)).sum ≤
        (a.take k).sum + (b.take l).sum := by
  fun_induction smerge a b with
  | case1 b =>
      intro _ _ k l hk _
      simp at hk; subst hk; simp
  | case2 a =>
      intro _ _ k l _ hl
      simp at hl; subst hl; simp
  | case3 x xs y ys h ih =>
      intro ha hb k l hk hl
      have ha2 := ha
      cases ha2 with | cons hax hxs =>
      match k with
      | k' + 1 =>
          have hk' : k' ≤ xs.length := by simpa using hk
          have step := ih hxs hb k' l hk' hl
          have harith : k' + 1 + l = (k' + l) + 1 := by omega
          rw [harith]
          simp only [List.take_succ_cons, List.sum_cons]
          omega
      | 0 =>
          match l with
          | 0 => simp
          | l' + 1 =>
              have hl' : l' ≤ ys.length := by simpa using hl
              have step := ih hxs hb 0 l' (Nat.zero_le _)
                (by simp; omega)
              simp only [Nat.zero_add, List.take_zero, List.sum_nil]
                at step ⊢
              have hcons := cons_prefix_step h hb l' (by simp; omega)
              have hL : ((x :: smerge xs (y :: ys)).take (l' + 1)).sum
                  = x + ((smerge xs (y :: ys)).take l').sum := by
                simp [List.take_succ_cons]
              rw [hL]
              omega
  | case4 x xs y ys h ih =>
      intro ha hb k l hk hl
      have hb2 := hb
      cases hb2 with | cons hby hys =>
      have hyx : y ≤ x := Nat.le_of_lt (Nat.lt_of_not_le h)
      match l with
      | l' + 1 =>
          have hl' : l' ≤ ys.length := by simpa using hl
          have step := ih ha hys k l' hk hl'
          have harith : k + (l' + 1) = (k + l') + 1 := by omega
          rw [harith]
          simp only [List.take_succ_cons, List.sum_cons]
          omega
      | 0 =>
          match k with
          | 0 => simp
          | k' + 1 =>
              have hk' : k' ≤ xs.length := by simpa using hk
              have step := ih ha hys k' 0
                (by simp; omega) (Nat.zero_le _)
              simp only [Nat.add_zero, List.take_zero, List.sum_nil]
                at step ⊢
              have hcons := cons_prefix_step hyx ha k' (by simp; omega)
              have hL : ((y :: smerge (x :: xs) ys).take (k' + 1)).sum
                  = y + ((smerge (x :: xs) ys).take k').sum := by
                simp [List.take_succ_cons]
              rw [hL]
              omega

/-- EXCHANGE (attainment), fully general. -/
theorem smerge_take_exists (a b : List Nat) :
    ∀ n, n ≤ a.length + b.length →
      ∃ k l, k + l = n ∧ k ≤ a.length ∧ l ≤ b.length ∧
        ((smerge a b).take n).sum = (a.take k).sum + (b.take l).sum := by
  fun_induction smerge a b with
  | case1 b =>
      intro n hn
      exact ⟨0, n, by omega, by simp, by simpa using hn, by simp⟩
  | case2 a =>
      intro n hn
      exact ⟨n, 0, by omega, by simpa using hn, by simp, by simp⟩
  | case3 x xs y ys h ih =>
      intro n hn
      match n with
      | 0 => exact ⟨0, 0, rfl, by simp, by simp, by simp⟩
      | n' + 1 =>
          obtain ⟨k, l, hkl, hk, hl, heq⟩ := ih n' (by simp at hn ⊢; omega)
          refine ⟨k + 1, l, by omega, by simp; omega, hl, ?_⟩
          rw [List.take_succ_cons, List.take_succ_cons, List.sum_cons,
              List.sum_cons, heq]
          omega
  | case4 x xs y ys h ih =>
      intro n hn
      match n with
      | 0 => exact ⟨0, 0, rfl, by simp, by simp, by simp⟩
      | n' + 1 =>
          obtain ⟨k, l, hkl, hk, hl, heq⟩ := ih n' (by simp at hn ⊢; omega)
          refine ⟨k, l + 1, by omega, hk, by simp; omega, ?_⟩
          rw [List.take_succ_cons, List.take_succ_cons, List.sum_cons,
              List.sum_cons, heq]
          omega

/-- The merged prefix IS the min-split DP value: the general
mathematical core of the Merge Lemma. -/
theorem merged_prefix_is_min_split (a b : List Nat)
    (ha : NDec a) (hb : NDec b) (n : Nat) (hn : n ≤ a.length + b.length) :
    (∀ k l, k + l = n → k ≤ a.length → l ≤ b.length →
      ((smerge a b).take n).sum ≤ (a.take k).sum + (b.take l).sum) ∧
    (∃ k l, k + l = n ∧ k ≤ a.length ∧ l ≤ b.length ∧
      ((smerge a b).take n).sum = (a.take k).sum + (b.take l).sum) := by
  refine ⟨?_, smerge_take_exists a b n hn⟩
  intro k l hkl hk hl
  subst hkl
  exact smerge_take_le a b ha hb k l hk hl

end GenJanus.MergeLemma
