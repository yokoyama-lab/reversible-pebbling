import RevPebbling.CompositionAnchor

/-!
# The row maximum `M_S` and the closed-form envelope (this work, Stage C)

`CountRecursion` proves the *midpoint* bound in full generality:
`midpoint_bound_general` says `m_S = δ(2^{S−2},S) ≤ 2^{(S−2)/2}`.
What was still checked only on a bounded grid (`max_decomposition`,
`c_eq_2d_sandwich` in `PebblingTheory`, `S ≤ 8`) is the step that turns
the midpoint bound into a bound on the whole row:

* `rowMax_succ`  : **`M_S = m_S + M_{S−1}`**, the Merge-Lemma max
  decomposition — the row maximum is the last convolution term, so the
  maxima telescope into the sum of the midpoint values;
* `rowMax_envelope` : hence `M_S + 2 ≤ 2^{(s+1)/2} + 2^{(s+2)/2}` in
  the `s = S − 2` indexing, which is the *exact* value of
  `Σ_{j ≤ s} 2^{⌊j/2⌋}`;
* `fRow_le_two_pow_mul_rowMax` : the trivial upper bound
  **`f_S ≤ 2^S M_S`** (sum ≤ length × max);
* `fRow_envelope` : the two combined, a geometric envelope with ratio
  `2√2`.

`GrowthClosedForm` feeds that envelope to `growth_le_of_geometric` and
obtains the closed-form upper bound `c ≤ 2√2` of the letter.

Everything here is general in `S`; nothing is a bounded check.
-/

namespace RevPebbling.RowMax

open RevPebbling.DifferenceMergeProperty RevPebbling.CountRecursion
open RevPebbling.CompositionAnchor

-- ------------------------------------------------------------------
-- The maximum of a list
-- ------------------------------------------------------------------

/-- Maximum entry of a list (`0` on the empty list). -/
def listMax (l : List Nat) : Nat := l.foldr max 0

@[simp] theorem listMax_nil : listMax [] = 0 := rfl

@[simp] theorem listMax_cons (x : Nat) (l : List Nat) :
    listMax (x :: l) = max x (listMax l) := rfl

theorem le_listMax : ∀ {x : Nat} {l : List Nat}, x ∈ l → x ≤ listMax l
  | _, [], h => by simp at h
  | x, a :: t, h => by
      rcases List.mem_cons.mp h with rfl | ht
      · simp only [listMax_cons]; omega
      · have := le_listMax ht
        simp only [listMax_cons]
        omega

theorem listMax_mem : ∀ (l : List Nat), l ≠ [] → listMax l ∈ l
  | [], h => absurd rfl h
  | x :: t, _ => by
      cases t with
      | nil => simp
      | cons y u =>
          have ih := listMax_mem (y :: u) (by simp)
          rcases Nat.le_total (listMax (y :: u)) x with h | h
          · have hx : listMax (x :: y :: u) = x := by
              simp only [listMax_cons] at h ⊢
              omega
            rw [hx]; simp
          · have hx : listMax (x :: y :: u) = listMax (y :: u) := by
              simp only [listMax_cons] at h ⊢
              omega
            rw [hx]; exact List.mem_cons_of_mem _ ih

/-- The maximum of a sorted merge is the larger of the two maxima
(only multiset preservation is used). -/
theorem listMax_smerge (a b : List Nat) :
    listMax (smerge a b) = max (listMax a) (listMax b) := by
  refine Nat.le_antisymm ?_ ?_
  · by_cases h : smerge a b = []
    · simp [h]
    · rcases (smerge_mem a b).mp (listMax_mem _ h) with hA | hB
      · exact Nat.le_trans (le_listMax hA) (Nat.le_max_left _ _)
      · exact Nat.le_trans (le_listMax hB) (Nat.le_max_right _ _)
  · have hA : listMax a ≤ listMax (smerge a b) := by
      by_cases h : a = []
      · simp [h]
      · exact le_listMax ((smerge_mem a b).mpr (Or.inl (listMax_mem a h)))
    have hB : listMax b ≤ listMax (smerge a b) := by
      by_cases h : b = []
      · simp [h]
      · exact le_listMax ((smerge_mem a b).mpr (Or.inr (listMax_mem b h)))
    omega

/-- Reindexing a `getElem` along an index identity. -/
theorem getElem_congr_idx {l : List Nat} {i j : Nat} (h : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst h; rfl

/-- In a sorted list the maximum sits at the end. -/
theorem listMax_eq_last {l : List Nat} (hsort : NDec l)
    (hne : 0 < l.length) : listMax l = l[l.length - 1]'(by omega) := by
  refine Nat.le_antisymm ?_ (le_listMax (List.getElem_mem _))
  have hnil : l ≠ [] := by
    intro hc; rw [hc] at hne; simp at hne
  obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp (listMax_mem l hnil)
  rw [← hval]
  exact sorted_getElem_le hsort (by omega) (by omega)

/-- **The maximum of a pointwise sum of two sorted lists sits at the
end.**  This is the shape of the merge representation's convolution
term `B_i = δ(i,S) + δ(i,S−1)`. -/
theorem listMax_zipWith_add (a b : List Nat) (ha : NDec a) (hb : NDec b)
    (n : Nat) (hlen : (List.zipWith (· + ·) a b).length = n + 1)
    (hna : n < a.length) (hnb : n < b.length) :
    listMax (List.zipWith (· + ·) a b) = a[n]'hna + b[n]'hnb := by
  have hidx : n < (List.zipWith (· + ·) a b).length := by omega
  refine Nat.le_antisymm ?_ ?_
  · have hne : List.zipWith (· + ·) a b ≠ [] := by
      intro hc; rw [hc, List.length_nil] at hlen; omega
    obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp (listMax_mem _ hne)
    have hin : i ≤ n := by omega
    have h1 : a[i]'(by omega) ≤ a[n]'hna := sorted_getElem_le ha hin hna
    have h2 : b[i]'(by omega) ≤ b[n]'hnb := sorted_getElem_le hb hin hnb
    rw [← hval, List.getElem_zipWith]
    omega
  · have hval : (List.zipWith (· + ·) a b)[n]'hidx = a[n]'hna + b[n]'hnb :=
      List.getElem_zipWith
    rw [← hval]
    exact le_listMax (List.getElem_mem hidx)

/-- Sum ≤ length × maximum. -/
theorem sum_le_length_mul_listMax : ∀ (l : List Nat),
    l.sum ≤ l.length * listMax l
  | [] => by simp
  | x :: t => by
      have ih := sum_le_length_mul_listMax t
      have h2 : x ≤ listMax (x :: t) := by simp only [listMax_cons]; omega
      have hmono : t.length * listMax t ≤ t.length * listMax (x :: t) :=
        Nat.mul_le_mul_left _ (by simp only [listMax_cons]; omega)
      simp only [List.sum_cons, List.length_cons]
      calc x + t.sum
          ≤ listMax (x :: t) + t.length * listMax (x :: t) := by omega
        _ = (t.length + 1) * listMax (x :: t) := by
            rw [Nat.succ_mul]; omega

-- ------------------------------------------------------------------
-- The row maximum M_S
-- ------------------------------------------------------------------

/-- **The row maximum** `M_S = max_i δ(i,S)` of row `S = s + 2`. -/
def rowMax (s : Nat) : Nat := listMax (rowIter s)

theorem two_le_two_pow_succ (s : Nat) : 2 ≤ 2 ^ (s + 1) := by
  have := two_pow_ge_one s
  rw [Nat.pow_succ]; omega

theorem rowIter_ne_nil (s : Nat) : rowIter s ≠ [] := by
  intro hc
  have hl := rowIter_length s
  rw [hc, List.length_nil] at hl
  have := two_le_two_pow_succ s
  omega

theorem rowMax_pos (s : Nat) : 1 ≤ rowMax s := by
  obtain ⟨_, hpos⟩ := rowIter_invariant s
  exact hpos _ (listMax_mem _ (rowIter_ne_nil s))

/-- The row maximum is the last entry (the row is sorted). -/
theorem rowMax_eq_getElem (s : Nat) :
    rowMax s = (rowIter s)[2 ^ (s + 1) - 2]'(by
      rw [rowIter_length]
      have := two_le_two_pow_succ s
      omega) := by
  obtain ⟨hsort, _⟩ := rowIter_invariant s
  have hlen := rowIter_length s
  have h2 := two_le_two_pow_succ s
  have hne : 0 < (rowIter s).length := by omega
  rw [rowMax, listMax_eq_last hsort hne]
  exact getElem_congr_idx (by omega) _ _

-- ------------------------------------------------------------------
-- Tests: the general statements below, on small rows
-- ------------------------------------------------------------------

/-- Row maxima `M_S` for `S = 2..6` (cf. `deltaRow` in
`PebblingTheory`). -/
example : rowMax 0 = 1 ∧ rowMax 1 = 2 ∧ rowMax 2 = 3 ∧ rowMax 3 = 5 ∧
    rowMax 4 = 7 := by decide

/-- Midpoint values `m_S` for `S = 2..6`. -/
example : midv 0 = 1 ∧ midv 1 = 1 ∧ midv 2 = 1 ∧ midv 3 = 2 ∧
    midv 4 = 2 := by decide

/-- `M_S = m_S + M_{S−1}` on small rows (the general statement is
`rowMax_succ`). -/
example : ((List.range 4).all fun s =>
    rowMax (s + 1) == midv (s + 1) + rowMax s) = true := by decide

-- ------------------------------------------------------------------
-- The max decomposition M_S = m_S + M_{S-1}, fully general
-- ------------------------------------------------------------------

/-- **THE MAX DECOMPOSITION, fully general** (Stage C; the bounded-grid
version is `PebblingTheory.max_decomposition`, `S ≤ 8`).

`M_S = m_S + M_{S−1}`.  In the merge representation
`row_S = 1 :: smerge row_{S−1} B` with `B_i = δ(i,S) + δ(i,S−1)`, the
maximum of `B` is its last entry, and that entry is
`δ(2^{S−2},S) + δ(2^{S−2},S−1) = m_S + M_{S−1}`, because the previous
row ends exactly at the index where the midpoint of the new row sits.
So the row maxima telescope into the sum of the midpoint values. -/
theorem rowMax_succ (s : Nat) : rowMax (s + 1) = midv (s + 1) + rowMax s := by
  obtain ⟨hsort, _⟩ := rowIter_invariant s
  obtain ⟨hsort', _⟩ := rowIter_invariant (s + 1)
  have hlen := rowIter_length s
  have hlen' := rowIter_length (s + 1)
  have h2 := two_le_two_pow_succ s
  have hpow : (2:Nat) ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by
    rw [Nat.pow_succ]; omega
  have hna : 2 ^ (s + 1) - 2 < (rowIter (s + 1)).length := by omega
  have hnb : 2 ^ (s + 1) - 2 < (rowIter s).length := by omega
  have hzlen : (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)).length
      = (2 ^ (s + 1) - 2) + 1 := by
    rw [List.length_zipWith]
    omega
  -- the maximum of the convolution term is its last entry
  have hBmax := listMax_zipWith_add (rowIter (s + 1)) (rowIter s) hsort' hsort
    (2 ^ (s + 1) - 2) hzlen hna hnb
  have hmidv : (rowIter (s + 1))[2 ^ (s + 1) - 2]'hna = midv (s + 1) := rfl
  have hlast : (rowIter s)[2 ^ (s + 1) - 2]'hnb = rowMax s :=
    (rowMax_eq_getElem s).symm
  rw [hmidv, hlast] at hBmax
  -- assemble through the merge representation
  have hmax := rowMax_pos s
  calc rowMax (s + 1)
      = listMax (1 :: smerge (rowIter s)
          (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s))) :=
        congrArg listMax (rowIter_succ_rep s)
    _ = max 1 (max (rowMax s)
          (listMax (List.zipWith (· + ·) (rowIter (s + 1)) (rowIter s)))) := by
        simp only [rowMax, listMax_cons, listMax_smerge]
    _ = midv (s + 1) + rowMax s := by rw [hBmax]; omega

-- ------------------------------------------------------------------
-- The geometric envelope
-- ------------------------------------------------------------------

/-- The midpoint bound of `CountRecursion`, in `midv` notation:
`m_S ≤ 2^{(S−2)/2}`. -/
theorem midv_le (s : Nat) : midv s ≤ 2 ^ (s / 2) := midpoint_bound_general s

/-- **THE ENVELOPE.**  `M_S + 2 ≤ 2^{(s+1)/2} + 2^{(s+2)/2}` for
`S = s + 2`.

`rowMax_succ` telescopes the maxima into `M_S = Σ_{j ≤ s} m_j`, and
`midv_le` bounds each term; the stated right-hand side is the exact
value of `Σ_{j ≤ s} 2^{⌊j/2⌋}`, which is why the induction closes with
nothing to spare (`2^{(s+1)/2} + 2^{(s+1)/2} = 2^{(s+3)/2}`). -/
theorem rowMax_envelope (s : Nat) :
    rowMax s + 2 ≤ 2 ^ ((s + 1) / 2) + 2 ^ ((s + 2) / 2) := by
  induction s with
  | zero => decide
  | succ s ih =>
      have hm := midv_le (s + 1)
      have hstep := rowMax_succ s
      have hdouble : (2:Nat) ^ ((s + 3) / 2)
          = 2 ^ ((s + 1) / 2) + 2 ^ ((s + 1) / 2) := by
        have hdiv : (s + 3) / 2 = (s + 1) / 2 + 1 := by omega
        rw [hdiv, Nat.pow_succ]; omega
      have e1 : (2:Nat) ^ ((s + 1 + 1) / 2) = 2 ^ ((s + 2) / 2) := by
        have : (s + 1 + 1) / 2 = (s + 2) / 2 := by omega
        rw [this]
      have e2 : (2:Nat) ^ ((s + 1 + 2) / 2) = 2 ^ ((s + 3) / 2) := by
        have : (s + 1 + 2) / 2 = (s + 3) / 2 := by omega
        rw [this]
      have e3 : (2:Nat) ^ ((s + 1) / 2 + 1) = 2 ^ ((s + 1) / 2) * 2 :=
        Nat.pow_succ 2 ((s + 1) / 2)
      rw [e1, e2, hdouble, hstep]
      omega

-- ------------------------------------------------------------------
-- The space-optimal cost of the row, and its envelope
-- ------------------------------------------------------------------

/-- **The space-optimal cost** `f_S = F(2^{S−1},S) = 1 + 2·Σ_i δ(i,S)`
read off the generated row (the row index is `S − 2`).
`f_0 = f_1 = 1`: a single node costs one step. -/
def fRow : Nat → Nat
  | 0 => 1
  | 1 => 1
  | p + 2 => 1 + 2 * (rowIter p).sum

/-- Known small values `f_S = 3, 9, 25, 71, 193` for `S = 2..6`
(cf. `RLEPebble.rle_f_small` and `PebblingTheory.fval`). -/
example : fRow 2 = 3 ∧ fRow 3 = 9 ∧ fRow 4 = 25 ∧ fRow 5 = 71 ∧
    fRow 6 = 193 := by decide

/-- `f_S ≤ 2^S M_S` on small rows (the general statement is
`fRow_le_two_pow_mul_rowMax`). -/
example : ((List.range 5).all fun s =>
    decide (fRow (s + 2) ≤ 2 ^ (s + 2) * rowMax s)) = true := by decide

/-- The geometric envelope on small rows (the general statement is
`fRow_envelope`). -/
example : ((List.range 5).all fun s =>
    decide (fRow (s + 2) ≤ 2 ^ (s + 3) * 2 ^ ((s + 2) / 2))) = true := by decide

theorem fRow_pos : ∀ p, 1 ≤ fRow p
  | 0 => Nat.le_refl 1
  | 1 => Nat.le_refl 1
  | p + 2 => by
      show 1 ≤ 1 + 2 * (rowIter p).sum
      omega

/-- **THE TRIVIAL UPPER BOUND `f_S ≤ 2^S M_S`, fully general** (the
bounded version is the right half of `PebblingTheory.c_eq_2d_sandwich`,
`S ≤ 8`): the row has `2^{S−1} − 1` entries, each at most `M_S`, and
`f_S = 1 + 2·Σ`. -/
theorem fRow_le_two_pow_mul_rowMax (s : Nat) :
    fRow (s + 2) ≤ 2 ^ (s + 2) * rowMax s := by
  have hsum := sum_le_length_mul_listMax (rowIter s)
  have hlen := rowIter_length s
  have hmax := rowMax_pos s
  have h2 := two_le_two_pow_succ s
  have hpow : (2:Nat) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
    rw [Nat.pow_succ]; omega
  have hsum' : (rowIter s).sum ≤ (2 ^ (s + 1) - 1) * rowMax s := by
    rw [← hlen]; exact hsum
  -- `(2^{s+1} − 1)·M + M = 2^{s+1}·M`, so `1 + 2Σ ≤ 2^{s+2}M` as `1 ≤ 2M`
  have hexp : (2 ^ (s + 1) - 1) * rowMax s + rowMax s
      = 2 ^ (s + 1) * rowMax s := by
    have hsucc : 2 ^ (s + 1) - 1 + 1 = 2 ^ (s + 1) := by omega
    calc (2 ^ (s + 1) - 1) * rowMax s + rowMax s
        = (2 ^ (s + 1) - 1 + 1) * rowMax s := (Nat.succ_mul _ _).symm
      _ = 2 ^ (s + 1) * rowMax s := by rw [hsucc]
  show 1 + 2 * (rowIter s).sum ≤ 2 ^ (s + 2) * rowMax s
  rw [hpow, Nat.mul_assoc]
  omega

/-- **THE GEOMETRIC ENVELOPE** `f_S ≤ 2^{S+1}·2^{⌊S/2⌋}`: the two
bounds combined.  The right-hand side grows like `(2√2)^S`, which is
what `GrowthClosedForm` turns into `c ≤ 2√2`. -/
theorem fRow_envelope (s : Nat) :
    fRow (s + 2) ≤ 2 ^ (s + 3) * 2 ^ ((s + 2) / 2) := by
  have h1 := fRow_le_two_pow_mul_rowMax s
  have h2 := rowMax_envelope s
  have h3 : (2:Nat) ^ ((s + 1) / 2) ≤ 2 ^ ((s + 2) / 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : rowMax s ≤ 2 * 2 ^ ((s + 2) / 2) := by omega
  have h5 : 2 ^ (s + 2) * rowMax s ≤ 2 ^ (s + 2) * (2 * 2 ^ ((s + 2) / 2)) :=
    Nat.mul_le_mul_left _ h4
  have h6 : 2 ^ (s + 2) * (2 * 2 ^ ((s + 2) / 2))
      = 2 ^ (s + 3) * 2 ^ ((s + 2) / 2) := by
    have hp : (2:Nat) ^ (s + 3) = 2 ^ (s + 2) * 2 := Nat.pow_succ 2 (s + 2)
    rw [hp, Nat.mul_assoc]
  omega

end RevPebbling.RowMax
