import RevPebbling.Subsolution
import RevPebbling.RowMax

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

end RevPebbling.ReadoutBridge
