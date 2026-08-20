import RevPebbling.Subsolution
import RevPebbling.RowMax
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# From counts to `rowMax`: the bridge the readout needs

`Subsolution.subsolution_le_count` delivers `Ψ_S(v) ≤ countLe (rowIter S) v`
— a statement about **counts**.  The growth constant, however, is read off
`rowMax` (`Unconditional.tendsto_rowMax_root_uncond` says
`rowMax s ^ (1/(s+1)) → c/2`), which is the **largest entry** of the row.
This file supplies the one step between them:

```
row.length ≤ countLe row v   ⟹   listMax row ≤ v
```

("if `v` already counts every entry, no entry exceeds `v`").  Composed with
the subsolution bound it reads: **whenever the subsolution reaches the full
row length at `v`, the row maximum is at most `v`** — and that `v` is the
readout point `ζ_½ = 1/q_h` of Lemma 1.

The reverse direction (`countLe ≤ length`) is `countLe_le_length`, so the
hypothesis is really an equality; stating it as `≤` is what the caller has.
-/

namespace RevPebbling.ReadoutBridge

open RevPebbling.CountRecursion RevPebbling.RowMax
open RevPebbling.DifferenceMergeProperty RevPebbling.CompositionAnchor

/-- If every entry of `l` is `≤ v` then `listMax l ≤ v`. -/
theorem listMax_le_of_forall {l : List Nat} {v : Nat}
    (h : ∀ x ∈ l, x ≤ v) : listMax l ≤ v := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [listMax_cons]
    exact Nat.max_le.mpr ⟨h a (by simp), ih (fun x hx => h x (by simp [hx]))⟩

/-- **The bridge.**  If the count at `v` already reaches the row length,
then no entry exceeds `v`, so `listMax ≤ v`. -/
theorem listMax_le_of_countLe {l : List Nat} {v : Nat}
    (h : l.length ≤ countLe l v) : listMax l ≤ v := by
  have hle : countLe l v ≤ l.length := countLe_le_length l v
  have heq : l.countP (fun x => decide (x ≤ v)) = l.length := by
    unfold countLe at h hle; omega
  have hall : ∀ x ∈ l, x ≤ v := by
    intro x hx
    have := (List.countP_eq_length (l := l) (p := fun x => decide (x ≤ v))).mp heq x hx
    simpa using this
  exact listMax_le_of_forall hall

/-- The form the readout uses: a subsolution that reaches the full row
length at `v` caps `rowMax`. -/
theorem rowMax_le_of_subsolution {Psi : Nat → Nat → Nat} {s v : Nat}
    (hsub : Psi s v ≤ countLe (rowIter s) v)
    (hfull : (rowIter s).length ≤ Psi s v) :
    rowMax s ≤ v :=
  listMax_le_of_countLe (Nat.le_trans hfull hsub)

/-! ## The **midpoint** readout: the quantile bridge

⚠ The manuscript's readout (Lemma 1, step (a)) does **not** run at the
cap: it reads off the row's **midpoint** `m_S = δ(2^{S−2}, S)`, where the
subsolution is only `⌊cap_S/2⌋ = 2^{S−2}−1`, far below the row length.
`rowMax_le_of_subsolution` above therefore does not apply there — its
hypothesis `length ≤ Ψ` is *false* at the midpoint.  (An independent check
on 2026-08-20 recorded this as a genuine mismatch between the two.)

What holds at the midpoint is the **quantile** statement: in a sorted row,
`k+1 ≤ countLe l v` forces the `k`-th entry to be `≤ v`.  The row maxima
then telescope through `RowMax.rowMax_succ` (`M_S = m_S + M_{S−1}`), which
is where the manuscript's harmless polynomial factor `S` comes from. -/

/-- **The quantile bridge.**  In a non-decreasing list, if at least `k+1`
entries are `≤ v` then the `k`-th entry is `≤ v`. -/
theorem getElem_le_of_countLe {l : List Nat} (hs : NDec l) {k v : Nat}
    (hk : k < l.length) (h : k + 1 ≤ countLe l v) : l[k] ≤ v := by
  by_contra hgt
  push_neg at hgt
  -- split the count at `k`: everything from `k` on is `≥ l[k] > v`
  have hsplit : countLe l v = countLe (l.take k) v + countLe (l.drop k) v := by
    unfold countLe
    rw [← List.countP_append, List.take_append_drop]
  have hzero : countLe (l.drop k) v = 0 := by
    unfold countLe
    rw [List.countP_eq_zero]
    intro x hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
    have hlt : k + i < l.length := by
      have hdl : (l.drop k).length = l.length - k := List.length_drop
      omega
    have hle : l[k] ≤ l[k + i] := sorted_getElem_le hs (by omega) hlt
    have hval : x = l[k + i] := by
      rw [← hxi, List.getElem_drop]
    simp only [decide_eq_true_eq]
    omega
  have hlen : countLe (l.take k) v ≤ k := by
    have h1 := countLe_le_length (l.take k) v
    have h2 : (l.take k).length ≤ k := by simp
    omega
  omega

/-- **The midpoint readout.**  A subsolution that reaches `2^s − 1`
(= `⌊cap_{s+2}/2⌋`, the manuscript's `2^{S−2}−1`) at `v` caps the row's
**midpoint** value `midv s`. -/
theorem midv_le_of_subsolution {Psi : Nat → Nat → Nat} {s v : Nat}
    (hs1 : 1 ≤ s)
    (hsub : Psi s v ≤ countLe (rowIter s) v)
    (hmid : 2 ^ s - 1 ≤ Psi s v) :
    midv s ≤ v := by
  -- `s ≥ 1` is needed: at `s = 0` the row is `[1]`, `2^0 − 1 = 0` says nothing,
  -- and `midv 0 = 1`, so the statement would be false.
  have hpow : (2 : Nat) ≤ 2 ^ s := by
    calc (2 : Nat) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs1
  have hlen : (rowIter s).length = 2 ^ (s + 1) - 1 := rowIter_length s
  have hidx : 2 ^ s - 2 < (rowIter s).length := by
    have : (2 : Nat) ^ s + 2 ^ s = 2 ^ (s + 1) := by rw [Nat.pow_succ]; omega
    omega
  obtain ⟨hsort, _⟩ := rowIter_invariant s
  have hcount : (2 ^ s - 2) + 1 ≤ countLe (rowIter s) v := by omega
  have := getElem_le_of_countLe hsort hidx hcount
  unfold midv
  exact this

/-! ## Telescoping the midpoints into `rowMax` -/

/-- `rowMax 0 = 1`. -/
theorem rowMax_zero : rowMax 0 = 1 := by decide

/-- **`M_S ≤ 1 + S·m`**: if every midpoint up to `s` is at most `V`, the
row maximum is at most `1 + s·V`, by `rowMax_succ` (`M_S = m_S + M_{S−1}`).
The polynomial factor `s` is harmless: the readout takes an `(s−1)`-th
root, so it contributes `s^{1/(s−1)} → 1` (`Readout.bound_tendsto`). -/
theorem rowMax_le_of_midv_le {s V : Nat}
    (h : ∀ j, 1 ≤ j → j ≤ s → midv j ≤ V) : rowMax s ≤ 1 + s * V := by
  induction s with
  | zero => simp [rowMax_zero]
  | succ n ih =>
    have hn : rowMax n ≤ 1 + n * V := ih (fun j hj1 hj2 => h j hj1 (by omega))
    have hmid : midv (n + 1) ≤ V := h (n + 1) (by omega) (by omega)
    calc rowMax (n + 1) = midv (n + 1) + rowMax n := rowMax_succ n
      _ ≤ V + (1 + n * V) := Nat.add_le_add hmid hn
      _ = 1 + (n + 1) * V := by ring

/-- **The readout, assembled.**  A subsolution that reaches `2^j − 1` at
`v j` for every level `j ≤ s`, with all `v j ≤ V`, caps `rowMax s` by
`1 + s·V`.  This is Lemma 1 step (a)+(d) of the manuscript, with the
midpoint mismatch removed. -/
theorem rowMax_le_of_midpoint_subsolution {Psi : Nat → Nat → Nat} {s V : Nat}
    {v : Nat → Nat}
    (hsub : ∀ j, Psi j (v j) ≤ countLe (rowIter j) (v j))
    (hmid : ∀ j, 2 ^ j - 1 ≤ Psi j (v j))
    (hv : ∀ j, 1 ≤ j → j ≤ s → v j ≤ V) :
    rowMax s ≤ 1 + s * V :=
  rowMax_le_of_midv_le (fun j hj1 hj2 =>
    le_trans (midv_le_of_subsolution hj1 (hsub j) (hmid j)) (hv j hj1 hj2))

end RevPebbling.ReadoutBridge
