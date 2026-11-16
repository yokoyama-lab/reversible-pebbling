import lean.CflatSubsol

/-!
# m104: the `v = 0`/`v = 1` clauses and the zero region of `hbelow`, from one vanishing condition

`CflatSubsol.subsol_of_below` (m103) leaves four hypotheses on the `Ψ` of the induction:
`hbase`, `hone` (`Ψ (s+1) 1 ≤ 1 + Ψ s 1`), `hzeroP` (`Ψ (s+1) 0 = 0`) and `hbelow` (the step
for every `v` below the band).  This module shows that `hone`, `hzeroP` and the part of
`hbelow` where the upper row vanishes all follow from a single condition

```
Vanish Ψ (s+1) V   :=   ∀ v ≤ V, Ψ (s+1) v = 0          (with V ≥ 1)
```

because on the zero region the step holds with the split `u = 1`, `w = v − 1`
(left-hand side `0`).

## What is proved

* `hone_of_vanish`, `hzero_of_vanish`, `step_of_vanish` : the three discharges.
* `subsol_of_mid` : `subsol_of_below` with `hone`, `hzeroP` and the zero part of `hbelow`
  discharged.  **Remaining hypotheses: `hbase` and `hmid`** — the step for
  `V (s+1) < v < F_{s+3}·2^{−1/100}` (above the zero region, below the band).
* `trunc_vanish_one` : `truncModel` vanishes on `[0, 1]` at every row `s ≥ 19`, so the
  hypotheses `hA`, `hV`, `hvan` of `subsol_of_mid` are jointly satisfiable with `V = 1`
  (non-vacuity).  Whether `truncModel` satisfies `hmid` is **not** claimed here.

General proofs; no `native_decide`.  ε = 0.0035 instance — **not** the published
instance ε = 0.002.

Checked by `scripts/probe_brw/m104_cflat_vanish.py --selftest` and `--mutant all`.
-/

namespace RevPebbling.CflatVanish

open RevPebbling.ShapeMonotone RevPebbling.CapZone RevPebbling.C1bCert
open RevPebbling.CflatModel RevPebbling.CflatLevel RevPebbling.CountRecursion
open RevPebbling.CflatSubsol

noncomputable section

/-- `Ψ` vanishes on `[0, V]` at row `s`. -/
def Vanish (Ψ : ℕ → ℕ → ℕ) (s V : ℕ) : Prop := ∀ v, v ≤ V → Ψ s v = 0

theorem hone_of_vanish {Ψ : ℕ → ℕ → ℕ} {s V : ℕ} (hV : 1 ≤ V) (h : Vanish Ψ (s + 1) V) :
    Ψ (s + 1) 1 ≤ 1 + Ψ s 1 := by
  rw [h 1 hV]; exact Nat.zero_le _

theorem hzero_of_vanish {Ψ : ℕ → ℕ → ℕ} {s V : ℕ} (h : Vanish Ψ (s + 1) V) :
    Ψ (s + 1) 0 = 0 :=
  h 0 (Nat.zero_le _)

/-- On the zero region of the upper row the step holds with `u = 1`, `w = v − 1`. -/
theorem step_of_vanish {Ψ : ℕ → ℕ → ℕ} {s V v : ℕ} (h : Vanish Ψ (s + 1) V)
    (hv2 : 2 ≤ v) (hvV : v ≤ V) :
    ∃ u w, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
      Ψ (s + 1) v ≤ 1 + Ψ s v + min (Ψ s u) (Ψ (s + 1) w) := by
  refine ⟨1, v - 1, by omega, le_refl _, by omega, ?_⟩
  rw [h v hvV]; exact Nat.zero_le _

/-- **`subsol_of_below` with `hone`, `hzeroP` and the zero part of `hbelow` discharged.**
What remains is the base and the step for `v` strictly above the zero region `[0, V (s+1)]`
and strictly below the band of row `s + 1`. -/
theorem subsol_of_mid {Ψ : ℕ → ℕ → ℕ} {S₀ : ℕ} (V : ℕ → ℕ) (hS₀ : 18 ≤ S₀)
    (hA : ∀ s, S₀ ≤ s → Agree Ψ s)
    (hbase : ∀ v, Ψ S₀ v ≤ countLe (rowIter S₀) v)
    (hV : ∀ s, S₀ ≤ s → 1 ≤ V (s + 1))
    (hvan : ∀ s, S₀ ≤ s → Vanish Ψ (s + 1) (V (s + 1)))
    (hmid : ∀ s, S₀ ≤ s → ∀ v : ℕ, V (s + 1) < v →
      (v : ℝ) < (2 : ℝ) ^ cornerOf (s + 3) * (2 : ℝ) ^ (-((1 : ℝ) / 100)) →
      ∃ u w : ℕ, u + w = v ∧ 1 ≤ u ∧ 1 ≤ w ∧
        Ψ (s + 1) v ≤ 1 + Ψ s v + min (Ψ s u) (Ψ (s + 1) w)) :
    ∀ s, S₀ ≤ s → ∀ v, Ψ s v ≤ countLe (rowIter s) v := by
  refine subsol_of_below hS₀ hA hbase
    (fun s hs => hone_of_vanish (hV s hs) (hvan s hs))
    (fun s hs => hzero_of_vanish (hvan s hs)) ?_
  intro s hs v hv2 hlt
  by_cases hvV : v ≤ V (s + 1)
  · exact step_of_vanish (hvan s hs) hv2 hvV
  · exact hmid s hs v (by omega) hlt

/-- **Non-vacuity**: `truncModel` vanishes on `[0, 1]` from row `19` on (at `v = 1`,
`log₂ 1 − corner = −corner ≤ −12 < −2395/1024 ≤ x_½`, so `1` is off the domain). -/
theorem trunc_vanish_one {s : ℕ} (hs : 19 ≤ s) : Vanish truncModel s 1 := by
  intro v hv
  unfold truncModel
  split_ifs with hcond
  · exfalso
    obtain ⟨hpos, hx⟩ := hcond
    have hv1 : v = 1 := by omega
    subst hv1
    have hc := corner_ge (S := s + 2) (by omega)
    have hxg := xhalf_ge
    simp only [Nat.cast_one, Real.logb_one, zero_sub] at hx
    linarith
  · rfl

/-- The hypotheses `hV`/`hvan` of `subsol_of_mid` hold for `truncModel` with `V = 1`. -/
theorem trunc_hvan {S₀ : ℕ} (hS₀ : 18 ≤ S₀) :
    ∀ s, S₀ ≤ s → Vanish truncModel (s + 1) ((fun _ => 1) (s + 1)) :=
  fun _ hs => trunc_vanish_one (by omega)

end

#print axioms hone_of_vanish
#print axioms hzero_of_vanish
#print axioms step_of_vanish
#print axioms subsol_of_mid
#print axioms trunc_vanish_one
#print axioms trunc_hvan

end RevPebbling.CflatVanish
