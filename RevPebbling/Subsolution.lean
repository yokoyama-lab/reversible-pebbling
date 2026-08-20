import RevPebbling.CountRecursion
import Mathlib.Data.Nat.Init
import Mathlib.Order.MinMax

/-!
# Lemma 2: base + step ⟹ `Ψ ≤ C` (the double induction)

The upper-bound programme (companion manuscript, `notes/lemma_U_clean.md`)
builds a family `Ψ S v` and concludes `Ψ S v ≤ C S v` from

* a **base** `Ψ S₀ v ≤ C S₀ v` for all `v`, and
* a **step**: for each `S ≥ S₀` and each `v ≥ 2` there is *some* split
  `u + w = v` with `u, w ≥ 1` and
  `Ψ (S+1) v ≤ 1 + Ψ S v + min (Ψ S u) (Ψ (S+1) w)`,
* a **`v = 1` clause** `Ψ (S+1) 1 ≤ 1 + Ψ S 1` (there is no split of `1`
  into two positive parts, so the step is vacuous there; omitting this
  clause makes the lemma false).

The count side supplies the matching inequality in the other direction:
`CountRecursion.count_recursion_split`.

`Ψ` may depend on `S` arbitrarily — the induction only ever uses
`Ψ S ≤ C S` at the previous level and `Ψ (S+1) w` at *smaller* `w`.  What
makes the inner recursion well-founded is `w < v`, i.e. `u ≥ 1`; the
requirement `w ≥ 1` is only there so that `Ψ (S+1) w` is a value the step
is allowed to mention.

This file states and proves the induction abstractly, over any `C`
satisfying the recursion; `subsolution_le_count` then instantiates it at
the real `C S v = countLe (rowIter S) v`.

The `v = 1` case needs `1 + C s 1 ≤ C (s+1) 1`, which the recursion gives
at `u = 1, w = 0` — the `min` term is dropped by `min ≥ 0`, so **no fact
about `C s 0` is needed** (the rows of `rowIter` do contain no `0`, but
the induction never has to know that).

⚠ **The split ordering is Lean's**: `min (Ψ S u) (Ψ (S+1) w)`, with `u`
at the *lower* level.  The manuscript writes `min (Ψ S u) (Ψ (S−1) w)`,
i.e. with `u` and `w` exchanged; `max` over splits makes the two the
same statement, but a formalisation has to pick one and keep it.
-/

namespace RevPebbling.Subsolution

open RevPebbling.CountRecursion

/-- **Lemma 2, abstractly.**  Any `C` obeying the split recursion, plus a
base and a step for `Ψ`, forces `Ψ ≤ C` from `S₀` on. -/
theorem subsolution_le_of_step {C Psi : Nat → Nat → Nat} {S₀ : Nat}
    (hrec : ∀ s u w, 1 ≤ u + w →
      1 + C s (u + w) + min (C s u) (C (s + 1) w) ≤ C (s + 1) (u + w))
    (hbase : ∀ v, Psi S₀ v ≤ C S₀ v)
    (hone : ∀ s, S₀ ≤ s → Psi (s + 1) 1 ≤ 1 + Psi s 1)
    (hzeroP : ∀ s, S₀ ≤ s → Psi (s + 1) 0 ≤ C (s + 1) 0)
    (hstep : ∀ s, S₀ ≤ s → ∀ v, 2 ≤ v → ∃ u w, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      Psi (s + 1) v ≤ 1 + Psi s v + min (Psi s u) (Psi (s + 1) w)) :
    ∀ s, S₀ ≤ s → ∀ v, Psi s v ≤ C s v := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact hbase
  | succ s hs ih =>
    -- inner: strong induction on `v`
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ihv =>
      match v with
      | 0 => exact hzeroP s hs
      | 1 =>
        -- `1 + C s 1 ≤ C (s+1) 1` comes from the recursion at `u = 1, w = 0`
        -- together with `min ≥ 0` (no need for `C s 0 = 0`).
        have h := hrec s 1 0 (by omega)
        simp only [Nat.add_zero] at h
        have hmin0 : 0 ≤ min (C s 1) (C (s + 1) 0) := Nat.zero_le _
        have h1 : Psi s 1 ≤ C s 1 := ih 1
        have h2 : Psi (s + 1) 1 ≤ 1 + Psi s 1 := hone s hs
        omega
      | (n + 2) =>
        obtain ⟨u, w, huw, hu, hw, hstep'⟩ := hstep s hs (n + 2) (by omega)
        have hwlt : w < n + 2 := by omega
        have hPw : Psi (s + 1) w ≤ C (s + 1) w := ihv w hwlt
        have hPu : Psi s u ≤ C s u := ih u
        have hPv : Psi s (n + 2) ≤ C s (n + 2) := ih (n + 2)
        have hmin : min (Psi s u) (Psi (s + 1) w) ≤ min (C s u) (C (s + 1) w) :=
          min_le_min hPu hPw
        have hcnt := hrec s u w (by omega)
        rw [huw] at hcnt
        omega

/-- The instance at the real count function `C S v = countLe (rowIter S) v`. -/
theorem subsolution_le_count {Psi : Nat → Nat → Nat} {S₀ : Nat}
    (hbase : ∀ v, Psi S₀ v ≤ countLe (rowIter S₀) v)
    (hone : ∀ s, S₀ ≤ s → Psi (s + 1) 1 ≤ 1 + Psi s 1)
    (hzeroP : ∀ s, S₀ ≤ s → Psi (s + 1) 0 = 0)
    (hstep : ∀ s, S₀ ≤ s → ∀ v, 2 ≤ v → ∃ u w, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      Psi (s + 1) v ≤ 1 + Psi s v + min (Psi s u) (Psi (s + 1) w)) :
    ∀ s, S₀ ≤ s → ∀ v, Psi s v ≤ countLe (rowIter s) v := by
  refine subsolution_le_of_step (C := fun s v => countLe (rowIter s) v)
    (fun s u w h => count_recursion_split s u w h)
    hbase hone (fun s hs => by rw [hzeroP s hs]; exact Nat.zero_le _) hstep

end RevPebbling.Subsolution
