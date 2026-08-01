import Std

/-!
# The difference-merge property: general core (this work, 追記18)

The difference-merge property states that the halved difference row of Knill's
recursion at space S equals, as a multiset, {1} ∪ row(S-1) ∪ B where
B_i = δ(i,S) + δ(i,S-1).  Its mathematical heart is the exchange
principle for sorted streams, proved here in FULL GENERALITY:

  for sorted lists a, b and any split k + l = n,
    Σ take n (smerge a b) ≤ Σ take k a + Σ take l b       (le)
  and some split attains equality                          (exists),

together with multiset preservation (`smerge_count`) and sortedness
(`smerge_sorted`).  Hence the min-split DP value IS the merged prefix
sum -- the content of the difference-merge property once Knill's recursion is
rewritten through prefix sums.

The self-referential closure and the prefix-sum identity are ALSO
proved in full generality below: `gen` builds the row with the
B-stream reading the accumulator (structural, no well-foundedness
debt), `gen_invariant`/`gen_count` establish sortedness and the
multiset bookkeeping, `gen_merge_rep` is the difference-merge property in
representation form (row = 1 :: smerge prev B), and
`gen_satisfies_knill` is the Knill identity form: the prefix sums of
the generated row satisfy F(n,S) = min_m [F(m,S) + F(m,S-1) +
F(n-m,S-1)] over feasible splits, both directions, for EVERY sorted
positive input row.  (Since Knill's recursion with base F(1,S) = 1
determines F uniquely, the generated row is the difference row of F;
the bounded instance `PebblingTheory.delta_merge_representation`
cross-checks this against the DP table.)
-/

namespace RevPebbling.DifferenceMergeProperty

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
                (by (try simp); omega)
              simp only [Nat.zero_add, List.take_zero, List.sum_nil]
                at step ⊢
              have hcons := cons_prefix_step h hb l' (by (try simp); omega)
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
                (by (try simp); omega) (Nat.zero_le _)
              simp only [Nat.add_zero, List.take_zero, List.sum_nil]
                at step ⊢
              have hcons := cons_prefix_step hyx ha k' (by (try simp); omega)
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
          refine ⟨k + 1, l, by omega, by (try simp); omega, hl, ?_⟩
          rw [List.take_succ_cons, List.take_succ_cons, List.sum_cons,
              List.sum_cons, heq]
          omega
  | case4 x xs y ys h ih =>
      intro n hn
      match n with
      | 0 => exact ⟨0, 0, rfl, by simp, by simp, by simp⟩
      | n' + 1 =>
          obtain ⟨k, l, hkl, hk, hl, heq⟩ := ih n' (by simp at hn ⊢; omega)
          refine ⟨k, l + 1, by omega, hk, by (try simp); omega, ?_⟩
          rw [List.take_succ_cons, List.take_succ_cons, List.sum_cons,
              List.sum_cons, heq]
          omega

/-- The merged prefix IS the min-split DP value: the general
mathematical core of the difference-merge property. -/
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


-- ------------------------------------------------------------------
-- Self-referential closure: the row generator.  The B-stream reads
-- the row being built at strictly smaller indices; representing the
-- build state as an accumulator makes the definition structural.
-- ------------------------------------------------------------------

/-- One generation step: emit the smaller of the next A-candidate
`prev[ja]` and the next B-candidate `out[jb] + prev[jb]`. -/
def genStep (prev : List Nat) :
    List Nat × Nat × Nat → List Nat × Nat × Nat
  | (out, ja, jb) =>
    match prev[ja]?, out[jb]?, prev[jb]? with
    | some a, some o, some p =>
        if a ≤ o + p then (out ++ [a], ja + 1, jb)
        else (out ++ [o + p], ja, jb + 1)
    | some a, _, _ => (out ++ [a], ja + 1, jb)
    | none, some o, some p => (out ++ [o + p], ja, jb + 1)
    | none, _, _ => (out, ja, jb)

/-- The generated row after t steps, starting from the base entry 1
(δ(2,S) = 1).  Fully structural: the self-reference of the B-stream
is resolved by the accumulator. -/
def gen (prev : List Nat) : Nat → List Nat × Nat × Nat
  | 0 => ([1], 0, 0)
  | t + 1 => genStep prev (gen prev t)

theorem genStep_shape (prev : List Nat) (st : List Nat × Nat × Nat) :
    ∃ tail, (genStep prev st).1 = st.1 ++ tail := by
  obtain ⟨out, ja, jb⟩ := st
  unfold genStep
  rcases hA : prev[ja]? with _ | a <;> rcases hO : out[jb]? with _ | o <;>
    rcases hP : prev[jb]? with _ | p <;> simp only [hA, hO, hP]
  · exact ⟨[], by simp⟩
  · exact ⟨[], by simp⟩
  · exact ⟨[], by simp⟩
  · exact ⟨[o + p], by simp⟩
  · exact ⟨[a], by simp⟩
  · exact ⟨[a], by simp⟩
  · exact ⟨[a], by simp⟩
  · by_cases hle : a ≤ o + p
    · exact ⟨[a], by simp [hle]⟩
    · exact ⟨[o + p], by simp [hle]⟩

theorem gen_prefix_stable (prev : List Nat) (t : Nat) :
    ∃ tail, (gen prev (t + 1)).1 = (gen prev t).1 ++ tail :=
  genStep_shape prev (gen prev t)

/-- Indexed monotonicity in a sorted list (getElem? form). -/
theorem sorted_getElem?_le {l : List Nat} (h : NDec l) {i j : Nat}
    {x y : Nat} (hi : l[i]? = some x) (hj : l[j]? = some y)
    (hij : i ≤ j) : x ≤ y := by
  have hj' : j < l.length := by
    cases Nat.lt_or_ge j l.length with
    | inl hh => exact hh
    | inr hh => rw [List.getElem?_eq_none hh] at hj; simp at hj
  have hi' : i < l.length := Nat.lt_of_le_of_lt hij hj'
  have hx : l[i] = x := by
    rw [List.getElem?_eq_getElem hi'] at hi; exact Option.some.inj hi
  have hy : l[j] = y := by
    rw [List.getElem?_eq_getElem hj'] at hj; exact Option.some.inj hj
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · omega
  · have := (List.pairwise_iff_getElem.mp h) i j hi' hj' hlt
    omega

/-- Valid getElem? implies index in range. -/
theorem getElem?_some_lt {l : List Nat} {i x : Nat}
    (h : l[i]? = some x) : i < l.length := by
  cases Nat.lt_or_ge i l.length with
  | inl hh => exact hh
  | inr hh => rw [List.getElem?_eq_none hh] at h; simp at h

/-- The generation invariant: pointer bookkeeping, sortedness, and
the candidate bounds, for all t ≤ 2·|prev|. -/
theorem gen_invariant (prev : List Nat) (hprev : NDec prev)
    (hpos : ∀ q ∈ prev, 1 ≤ q) :
    ∀ t, t ≤ 2 * prev.length →
    (gen prev t).2.1 + (gen prev t).2.2 = t ∧
    (gen prev t).2.1 ≤ prev.length ∧
    (gen prev t).2.2 ≤ prev.length ∧
    (gen prev t).1.length = t + 1 ∧
    NDec (gen prev t).1 ∧
    (∀ z ∈ (gen prev t).1, ∀ a, prev[(gen prev t).2.1]? = some a → z ≤ a) ∧
    (∀ z ∈ (gen prev t).1, ∀ o q, (gen prev t).1[(gen prev t).2.2]? = some o →
      prev[(gen prev t).2.2]? = some q → z ≤ o + q) := by
  intro t
  induction t with
  | zero =>
      intro _
      refine ⟨rfl, Nat.zero_le _, Nat.zero_le _, rfl, ?_, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨by simp, List.Pairwise.nil⟩
      · intro z hz a ha
        have hz1 : z = 1 := by simpa [gen] using hz
        have : a ∈ prev := by
          have := getElem?_some_lt ha
          have h2 : prev[(0:Nat)] = a := by
            rw [List.getElem?_eq_getElem this] at ha
            exact Option.some.inj ha
          rw [← h2]; exact List.getElem_mem this
        subst hz1; exact hpos a this
      · intro z hz o q ho hq
        simp [gen] at hz ho
        omega
  | succ t iht =>
      intro ht
      obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7⟩ := iht (by omega)
      have hgen1 : gen prev (t + 1) = genStep prev (gen prev t) := rfl
      rcases hg : gen prev t with ⟨out, ja, jb⟩
      rw [hg] at ih1 ih2 ih3 ih4 ih5 ih6 ih7
      simp only at ih1 ih2 ih3 ih4 ih5 ih6 ih7
      rw [hgen1, hg]
      have hjblt : jb < out.length := by omega
      have hOsome : out[jb]? = some (out[jb]) := List.getElem?_eq_getElem hjblt
      unfold genStep
      rcases hA : prev[ja]? with _ | a <;> rcases hO : out[jb]? with _ | o <;>
        rcases hP : prev[jb]? with _ | q <;> simp only [hA, hO, hP]
      -- (none, none, none): out[jb]? = none impossible
      · rw [hOsome] at hO; simp at hO
      · rw [hOsome] at hO; simp at hO
      -- (none, some o, none): both streams exhausted → t = 2L, excluded
      · exfalso
        have hja : prev.length ≤ ja := by
          cases Nat.lt_or_ge ja prev.length with
          | inl hh => rw [List.getElem?_eq_getElem hh] at hA; simp at hA
          | inr hh => exact hh
        have hjb : prev.length ≤ jb := by
          cases Nat.lt_or_ge jb prev.length with
          | inl hh => rw [List.getElem?_eq_getElem hh] at hP; simp at hP
          | inr hh => exact hh
        omega
      -- (none, some o, some q): B-move
      · have hjbL : jb < prev.length := getElem?_some_lt hP
        refine ⟨by (try simp); omega, by (try simp); omega, by (try simp); omega,
          by simp [ih4], ?_, ?_, ?_⟩
        · refine List.pairwise_append.mpr ⟨ih5, by simp, ?_⟩
          intro z hz b hb
          simp at hb; subst hb
          exact ih7 z hz o q hO hP
        · intro z _ a2 ha2
          simp [hA] at ha2
        · intro z hz o' q' ho' hq'
          have hoo : o ≤ o' := by
            rcases Nat.lt_or_ge (jb + 1) out.length with hlt | hge
            · have : (out ++ [o + q])[jb + 1]? = out[jb + 1]? :=
                List.getElem?_append_left hlt
              rw [this] at ho'
              exact sorted_getElem?_le ih5 hO ho' (by omega)
            · have hjb1 : jb + 1 = out.length := by omega
              have hcc : (out ++ [o + q])[jb + 1]? = some (o + q) := by
                rw [hjb1]; simp
              rw [hcc] at ho'
              have := Option.some.inj ho'
              omega
          have hqq : q ≤ q' := sorted_getElem?_le hprev hP hq' (by omega)
          have hz' : z ≤ o + q := by
            rcases List.mem_append.mp hz with hz1 | hz1
            · exact ih7 z hz1 o q hO hP
            · simp at hz1; omega
          omega
      -- (some a, none, none): out[jb]? = none impossible
      · rw [hOsome] at hO; simp at hO
      · rw [hOsome] at hO; simp at hO
      -- (some a, some o, none): A-move with B exhausted
      · have hjaL : ja < prev.length := getElem?_some_lt hA
        refine ⟨by (try simp); omega, by (try simp); omega, by (try simp); omega,
          by simp [ih4], ?_, ?_, ?_⟩
        · refine List.pairwise_append.mpr ⟨ih5, by simp, ?_⟩
          intro z hz b hb
          simp at hb; rw [hb]
          exact ih6 z hz a hA
        · intro z hz a' ha'
          have haa : a ≤ a' := sorted_getElem?_le hprev hA ha' (by omega)
          rcases List.mem_append.mp hz with hz1 | hz1
          · exact Nat.le_trans (ih6 z hz1 a hA) haa
          · simp at hz1; omega
        · intro z _ o' q' _ hq2
          simp [hP] at hq2
      -- (some a, some o, some q): compare
      · by_cases hle : a ≤ o + q <;> simp only [hle, if_true, if_false]
        -- A-move
        · have hjaL : ja < prev.length := getElem?_some_lt hA
          refine ⟨by (try simp); omega, by (try simp); omega, by (try simp); omega,
            by simp [ih4], ?_, ?_, ?_⟩
          · refine List.pairwise_append.mpr ⟨ih5, by simp, ?_⟩
            intro z hz b hb
            simp at hb; rw [hb]
            exact ih6 z hz a hA
          · intro z hz a' ha'
            have haa : a ≤ a' := sorted_getElem?_le hprev hA ha' (by omega)
            rcases List.mem_append.mp hz with hz1 | hz1
            · exact Nat.le_trans (ih6 z hz1 a hA) haa
            · simp at hz1; omega
          · intro z hz o' q' ho' hq'
            have : (out ++ [a])[jb]? = out[jb]? :=
              List.getElem?_append_left hjblt
            rw [this, hO] at ho'
            rw [hP] at hq'
            have ho2 : o = o' := Option.some.inj ho'
            have hq2 : q = q' := Option.some.inj hq'
            subst ho2; subst hq2
            rcases List.mem_append.mp hz with hz1 | hz1
            · exact ih7 z hz1 o q hO hP
            · simp at hz1; omega
        -- B-move
        · have hjbL : jb < prev.length := getElem?_some_lt hP
          refine ⟨by (try simp); omega, by (try simp); omega, by (try simp); omega,
            by simp [ih4], ?_, ?_, ?_⟩
          · refine List.pairwise_append.mpr ⟨ih5, by simp, ?_⟩
            intro z hz b hb
            simp at hb; subst hb
            exact ih7 z hz o q hO hP
          · intro z hz a' ha'
            rw [hA] at ha'
            have ha2 : a = a' := Option.some.inj ha'
            subst ha2
            rcases List.mem_append.mp hz with hz1 | hz1
            · exact ih6 z hz1 a hA
            · simp at hz1; omega
          · intro z hz o' q' ho' hq'
            have hoo : o ≤ o' := by
              rcases Nat.lt_or_ge (jb + 1) out.length with hlt | hge
              · have : (out ++ [o + q])[jb + 1]? = out[jb + 1]? :=
                  List.getElem?_append_left hlt
                rw [this] at ho'
                exact sorted_getElem?_le ih5 hO ho' (by omega)
              · have hjb1 : jb + 1 = out.length := by omega
                have hcc : (out ++ [o + q])[jb + 1]? = some (o + q) := by
                  rw [hjb1]; simp
                rw [hcc] at ho'
                have := Option.some.inj ho'
                omega
            have hqq : q ≤ q' := sorted_getElem?_le hprev hP hq' (by omega)
            have hz' : z ≤ o + q := by
              rcases List.mem_append.mp hz with hz1 | hz1
              · exact ih7 z hz1 o q hO hP
              · simp at hz1; omega
            omega


/-- Count over an extended take. -/
theorem count_take_succ (l : List Nat) (k : Nat) (hk : k < l.length)
    (v : Nat) :
    (l.take (k + 1)).count v =
      (l.take k).count v + (if l[k] = v then 1 else 0) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  by_cases hv : l[k] = v
  · rw [hv]
    simp [List.count_append]
  · have hv' : v ≠ l[k] := fun h => hv h.symm
    rw [List.count_append, if_neg hv]
    have h0 : List.count v (some l[k]).toList = 0 := by
      simp only [Option.toList_some, List.count_cons, List.count_nil]
      simp [beq_iff_eq, hv]
    omega

/-- Appending to the longer zip argument does not affect a prefix. -/
theorem zipWith_take_append :
    ∀ (out : List Nat) (x : Nat) (prev : List Nat) (k : Nat),
      k ≤ out.length →
      (List.zipWith (· + ·) (out ++ [x]) prev).take k =
        (List.zipWith (· + ·) out prev).take k
  | [], x, prev, 0, _ => by simp
  | [], x, prev, k + 1, hk => by simp at hk
  | o :: os, x, prev, 0, _ => by simp
  | o :: os, x, [], k + 1, hk => by simp
  | o :: os, x, p :: ps, k + 1, hk => by
      simp only [List.cons_append, List.zipWith_cons_cons,
        List.take_succ_cons]
      rw [zipWith_take_append os x ps k (by simpa using hk)]

/-- zipWith (+) of sorted lists is sorted. -/
theorem zip_sorted :
    ∀ {a b : List Nat}, NDec a → NDec b →
      NDec (List.zipWith (· + ·) a b)
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | x :: xs, y :: ys, ha, hb => by
      cases ha with | cons hax hxs =>
      cases hb with | cons hby hys =>
      simp only [List.zipWith_cons_cons]
      refine List.Pairwise.cons ?_ (zip_sorted hxs hys)
      intro z hz
      obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
      have hlen : i < xs.length ∧ i < ys.length := by
        have h2 := hi
        simp [List.length_zipWith] at h2
        omega
      rw [List.getElem_zipWith] at hzi
      have hb1 : x ≤ xs[i] := hax _ (List.getElem_mem hlen.1)
      have hb2 : y ≤ ys[i] := hby _ (List.getElem_mem hlen.2)
      omega

/-- Prefix sums of a zip split into the two streams. -/
theorem zip_take_sum :
    ∀ (a b : List Nat) (k : Nat), k ≤ a.length → k ≤ b.length →
      ((List.zipWith (· + ·) a b).take k).sum =
        (a.take k).sum + (b.take k).sum
  | _, _, 0, _, _ => by simp
  | [], _, k + 1, hk, _ => by simp at hk
  | _ :: _, [], k + 1, _, hk => by simp at hk
  | x :: xs, y :: ys, k + 1, hk, hk' => by
      simp only [List.zipWith_cons_cons, List.take_succ_cons,
        List.sum_cons]
      rw [zip_take_sum xs ys k (by simpa using hk) (by simpa using hk')]
      omega

/-- Sorted lists with equal counts are equal. -/
theorem sorted_eq_of_count :
    ∀ {l1 l2 : List Nat}, NDec l1 → NDec l2 →
      (∀ v, l1.count v = l2.count v) → l1 = l2
  | [], l2, _, _, hc => by
      cases l2 with
      | nil => rfl
      | cons y ys =>
          have := hc y
          simp [List.count_cons] at this
  | x :: xs, l2, h1, h2, hc => by
      cases l2 with
      | nil =>
          have := hc x
          simp [List.count_cons] at this
      | cons y ys =>
          cases h1 with | cons hx hxs =>
          cases h2 with | cons hy hys =>
          have hxy : x = y := by
            have hxmem : x ∈ y :: ys := by
              have := hc x
              have hpos : 0 < (y :: ys).count x := by
                simp [List.count_cons] at this ⊢
                omega
              exact List.count_pos_iff.mp hpos
            have hymem : y ∈ x :: xs := by
              have := hc y
              have hpos : 0 < (x :: xs).count y := by
                simp [List.count_cons] at this ⊢
                omega
              exact List.count_pos_iff.mp hpos
            have h1' : y ≤ x := by
              rcases List.mem_cons.mp hxmem with rfl | hm
              · omega
              · exact hy x hm
            have h2' : x ≤ y := by
              rcases List.mem_cons.mp hymem with heq | hm
              · omega
              · exact hx y hm
            omega
          subst hxy
          have : xs = ys := by
            refine sorted_eq_of_count hxs hys ?_
            intro v
            have := hc v
            simp [List.count_cons] at this
            omega
          rw [this]



/-- Count over a concat. -/
theorem count_concat (l : List Nat) (x v : Nat) :
    (l ++ [x]).count v = l.count v + (if x = v then 1 else 0) := by
  by_cases hx : x = v
  · rw [List.count_append, if_pos hx]
    have h1 : List.count v [x] = 1 := by simp [hx]
    omega
  · rw [List.count_append, if_neg hx]
    have h0 : List.count v [x] = 0 := by
      simp only [List.count_cons, List.count_nil]
      simp [beq_iff_eq, hx]
    omega

/-- Pointwise getElem? of a zip. -/
theorem zip_getElem? :
    ∀ (a b : List Nat) (i x y : Nat), a[i]? = some x → b[i]? = some y →
      (List.zipWith (· + ·) a b)[i]? = some (x + y)
  | [], _, i, _, _, ha, _ => by simp at ha
  | _ :: _, [], i, _, _, _, hb => by simp at hb
  | x' :: xs, y' :: ys, 0, x, y, ha, hb => by
      simp at ha hb
      simp [List.zipWith_cons_cons, ha, hb]
  | x' :: xs, y' :: ys, i + 1, x, y, ha, hb => by
      simp only [List.getElem?_cons_succ] at ha hb
      simp only [List.zipWith_cons_cons, List.getElem?_cons_succ]
      exact zip_getElem? xs ys i x y ha hb

/-- The generation count identity: the produced row is, as a multiset,
{1} ∪ (consumed prefix of prev) ∪ (consumed prefix of the B-stream). -/
theorem gen_count (prev : List Nat) (hprev : NDec prev)
    (hpos : ∀ q ∈ prev, 1 ≤ q) :
    ∀ t, t ≤ 2 * prev.length → ∀ v,
      ((gen prev t).1).count v =
        (if 1 = v then 1 else 0)
        + ((prev.take (gen prev t).2.1).count v)
        + (((List.zipWith (· + ·) (gen prev t).1 prev).take
            (gen prev t).2.2).count v) := by
  intro t
  induction t with
  | zero =>
      intro _ v
      by_cases h1 : (1 : Nat) = v <;> simp [gen, List.count_cons, h1]
  | succ t iht =>
      intro ht v
      obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7⟩ :=
        gen_invariant prev hprev hpos t (by omega)
      have hcnt := iht (by omega) v
      rcases hg : gen prev t with ⟨out, ja, jb⟩
      rw [hg] at ih1 ih2 ih3 ih4 ih5 ih6 ih7 hcnt
      simp only at ih1 ih2 ih3 ih4 ih5 ih6 ih7 hcnt
      have hgen1 : gen prev (t + 1) = genStep prev (gen prev t) := rfl
      rw [hgen1, hg]
      have hjblt : jb < out.length := by omega
      have hOsome : out[jb]? = some (out[jb]) := List.getElem?_eq_getElem hjblt
      unfold genStep
      rcases hA : prev[ja]? with _ | a <;> rcases hO : out[jb]? with _ | o <;>
        rcases hP : prev[jb]? with _ | q <;> simp only [hA, hO, hP]
      · rw [hOsome] at hO; simp at hO
      · rw [hOsome] at hO; simp at hO
      · exfalso
        have hja : prev.length ≤ ja := by
          cases Nat.lt_or_ge ja prev.length with
          | inl hh => rw [List.getElem?_eq_getElem hh] at hA; simp at hA
          | inr hh => exact hh
        have hjb : prev.length ≤ jb := by
          cases Nat.lt_or_ge jb prev.length with
          | inl hh => rw [List.getElem?_eq_getElem hh] at hP; simp at hP
          | inr hh => exact hh
        omega
      · -- B-move (A exhausted)
        have hjbL : jb < prev.length := getElem?_some_lt hP
        show (out ++ [o + q]).count v =
          (if 1 = v then 1 else 0) + ((prev.take ja).count v)
          + (((List.zipWith (· + ·) (out ++ [o + q]) prev).take
              (jb + 1)).count v)
        have h1 : (out ++ [o + q])[jb]? = some o := by
          rw [List.getElem?_append_left hjblt]; exact hO
        have hz? := zip_getElem? (out ++ [o + q]) prev jb o q h1 hP
        have hzlen : jb < (List.zipWith (· + ·) (out ++ [o + q]) prev).length :=
          getElem?_some_lt hz?
        have hzv : (List.zipWith (· + ·) (out ++ [o + q]) prev)[jb] = o + q :=
          Option.some.inj ((List.getElem?_eq_getElem hzlen).symm.trans hz?)
        rw [count_concat, count_take_succ _ jb hzlen v, hzv,
            zipWith_take_append out (o + q) prev jb (by omega)]
        omega
      · rw [hOsome] at hO; simp at hO
      · rw [hOsome] at hO; simp at hO
      · -- A-move (B exhausted)
        have hjaL : ja < prev.length := getElem?_some_lt hA
        have hpa : prev[ja] = a :=
          Option.some.inj ((List.getElem?_eq_getElem hjaL).symm.trans hA)
        show (out ++ [a]).count v =
          (if 1 = v then 1 else 0) + ((prev.take (ja + 1)).count v)
          + (((List.zipWith (· + ·) (out ++ [a]) prev).take jb).count v)
        rw [count_concat, count_take_succ prev ja hjaL v, hpa,
            zipWith_take_append out a prev jb (by omega)]
        omega
      · by_cases hle : a ≤ o + q <;> simp only [hle, if_true, if_false]
        · -- A-move
          have hjaL : ja < prev.length := getElem?_some_lt hA
          have hpa : prev[ja] = a :=
            Option.some.inj ((List.getElem?_eq_getElem hjaL).symm.trans hA)
          show (out ++ [a]).count v =
            (if 1 = v then 1 else 0) + ((prev.take (ja + 1)).count v)
            + (((List.zipWith (· + ·) (out ++ [a]) prev).take jb).count v)
          rw [count_concat, count_take_succ prev ja hjaL v, hpa,
              zipWith_take_append out a prev jb (by omega)]
          omega
        · -- B-move
          have hjbL : jb < prev.length := getElem?_some_lt hP
          show (out ++ [o + q]).count v =
            (if 1 = v then 1 else 0) + ((prev.take ja).count v)
            + (((List.zipWith (· + ·) (out ++ [o + q]) prev).take
                (jb + 1)).count v)
          have h1 : (out ++ [o + q])[jb]? = some o := by
            rw [List.getElem?_append_left hjblt]; exact hO
          have hz? := zip_getElem? (out ++ [o + q]) prev jb o q h1 hP
          have hzlen : jb <
              (List.zipWith (· + ·) (out ++ [o + q]) prev).length :=
            getElem?_some_lt hz?
          have hzv : (List.zipWith (· + ·) (out ++ [o + q]) prev)[jb]
              = o + q :=
            Option.some.inj ((List.getElem?_eq_getElem hzlen).symm.trans hz?)
          rw [count_concat, count_take_succ _ jb hzlen v, hzv,
              zipWith_take_append out (o + q) prev jb (by omega)]
          omega



/-- THE GENERAL DIFFERENCE-MERGE PROPERTY (representation form): the generated row
is literally 1 followed by the sorted merge of the previous row with
its own convolution stream. -/
theorem gen_merge_rep (prev : List Nat) (hprev : NDec prev)
    (hpos : ∀ q ∈ prev, 1 ≤ q) :
    (gen prev (2 * prev.length)).1 =
      1 :: smerge prev
        (List.zipWith (· + ·) (gen prev (2 * prev.length)).1 prev) := by
  obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7⟩ :=
    gen_invariant prev hprev hpos (2 * prev.length) (Nat.le_refl _)
  have hcnt := gen_count prev hprev hpos (2 * prev.length) (Nat.le_refl _)
  rcases hg : gen prev (2 * prev.length) with ⟨out, ja, jb⟩
  rw [hg] at ih1 ih2 ih3 ih4 ih5 ih6 ih7 hcnt
  simp only at ih1 ih2 ih3 ih4 ih5 ih6 ih7 hcnt
  have hja : ja = prev.length := by omega
  have hjb : jb = prev.length := by omega
  subst hja; subst hjb
  have hziplen : (List.zipWith (· + ·) out prev).length = prev.length := by
    simp [List.length_zipWith]; omega
  have hzips : NDec (List.zipWith (· + ·) out prev) := zip_sorted ih5 hprev
  apply sorted_eq_of_count ih5
  · refine List.Pairwise.cons ?_ (smerge_sorted prev _ hprev hzips)
    intro z hz
    rcases (smerge_mem prev _).mp hz with hzp | hzz
    · exact hpos z hzp
    · obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hzz
      rw [List.getElem_zipWith] at hzi
      rw [List.length_zipWith] at hi
      have hpi : 1 ≤ prev[i]'(by omega) := by
        apply hpos
        exact List.getElem_mem (by omega)
      omega
  · intro v
    have h1 := hcnt v
    rw [List.take_length] at h1
    rw [List.take_of_length_le (Nat.le_of_eq hziplen)] at h1
    rw [h1]
    simp [List.count_cons, smerge_count]
    by_cases hv : (1 : Nat) = v <;> simp [hv, beq_iff_eq] <;> omega

/-- Reach-limit prefix-sum values: F(n) = 1 + 2·Σ of the first n-1
halved differences. -/
def Fpre (l : List Nat) (n : Nat) : Nat := 1 + 2 * ((l.take (n - 1)).sum)

/-- THE GENERAL DIFFERENCE-MERGE PROPERTY (Knill identity form): the prefix sums of
the generated row satisfy Knill's recursion
F(n,S) = min_m [F(m,S) + F(m,S-1) + F(n-m,S-1)] over feasible splits
(with n = k+l+2, m = l+1; infeasible splits are infinite in the game).
Together with `gen_merge_rep` this is the full general difference-merge property. -/
theorem gen_satisfies_knill (prev : List Nat) (hprev : NDec prev)
    (hpos : ∀ q ∈ prev, 1 ≤ q) :
    (∀ k l, k ≤ prev.length → l ≤ prev.length →
      Fpre (gen prev (2 * prev.length)).1 (k + l + 2) ≤
        Fpre (gen prev (2 * prev.length)).1 (l + 1) + Fpre prev (l + 1)
          + Fpre prev (k + 1)) ∧
    (∀ n, 2 ≤ n → n ≤ 2 * prev.length + 2 →
      ∃ k l, k + l + 2 = n ∧ k ≤ prev.length ∧ l ≤ prev.length ∧
        Fpre (gen prev (2 * prev.length)).1 n =
          Fpre (gen prev (2 * prev.length)).1 (l + 1) + Fpre prev (l + 1)
            + Fpre prev (k + 1)) := by
  obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7⟩ :=
    gen_invariant prev hprev hpos (2 * prev.length) (Nat.le_refl _)
  have hrep := gen_merge_rep prev hprev hpos
  rcases hg : gen prev (2 * prev.length) with ⟨out, ja, jb⟩
  rw [hg] at ih1 ih2 ih3 ih4 ih5 ih6 ih7 hrep
  simp only at ih1 ih2 ih3 ih4 ih5 ih6 ih7 hrep
  have hzips : NDec (List.zipWith (· + ·) out prev) := zip_sorted ih5 hprev
  have hziplen : (List.zipWith (· + ·) out prev).length = prev.length := by
    rw [List.length_zipWith]; omega
  have hsplit : ∀ l, l ≤ prev.length →
      Fpre out (l + 1) + Fpre prev (l + 1) =
        2 + 2 * (((List.zipWith (· + ·) out prev).take l).sum) := by
    intro l hl
    have hz := zip_take_sum out prev l (by omega) hl
    simp only [Fpre, Nat.add_sub_cancel]
    omega
  have hmerge : ∀ j, Fpre out (j + 2) =
      3 + 2 * (((smerge prev (List.zipWith (· + ·) out prev)).take j).sum) := by
    intro j
    have h1 : (j + 2) - 1 = j + 1 := by omega
    have htake : out.take (j + 1) =
        1 :: (smerge prev (List.zipWith (· + ·) out prev)).take j := by
      conv => lhs; rw [hrep]
      rfl
    simp only [Fpre, h1, htake, List.sum_cons]
    omega
  refine ⟨?_, ?_⟩
  · intro k l hk hl
    show Fpre out (k + l + 2) ≤
      Fpre out (l + 1) + Fpre prev (l + 1) + Fpre prev (k + 1)
    have hle := smerge_take_le prev (List.zipWith (· + ·) out prev)
      hprev hzips k l hk (by omega)
    have h2 := hsplit l hl
    have h3 := hmerge (k + l)
    simp only [Fpre, Nat.add_sub_cancel] at *
    omega
  · intro n h2n hn
    obtain ⟨k, l, hkl, hk, hl, heq⟩ :=
      smerge_take_exists prev (List.zipWith (· + ·) out prev)
        (n - 2) (by omega)
    refine ⟨k, l, by omega, hk, by omega, ?_⟩
    show Fpre out n =
      Fpre out (l + 1) + Fpre prev (l + 1) + Fpre prev (k + 1)
    have h2 := hsplit l (by omega)
    have h3 := hmerge (n - 2)
    have hn2 : n - 2 + 2 = n := by omega
    rw [hn2] at h3
    simp only [Fpre, Nat.add_sub_cancel] at *
    omega

end RevPebbling.DifferenceMergeProperty
