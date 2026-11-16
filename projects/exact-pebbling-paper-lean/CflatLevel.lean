import lean.CflatModel

/-!
# m102: Lemma C-flat at ε = 0.0035 indexed by the level (§C-3, toward the induction)

`CflatModel.cflat_step_eps0035_model` takes the corner `c` as a free real and asks
`12 ≤ c`; its conclusion speaks of a level-`(S−1)` model at corner `c − a`.  To chain
the step from one level to the next, the corner must be the **level's** corner, and the
`c − a` of the conclusion must be the corner of level `S − 1`.

This module fixes the corner rule of `m48` (`Family.corner`, `b512fix.cfg`,
`a = 1341/4000`):

```
corner(S) = 88394266807713/500000000000 + (1341/4000)·(S − 512)
```

and proves

* `corner_ge`  : `21 ≤ S → 12 ≤ corner(S)` (the floor threshold of `CflatModel` holds from
  `S = 21`; `corner(20) < 12`, so `21` is sharp — checked in Python, G3 of m102);
* `corner_pred`: `corner(S+1) − a = corner(S)` (the conclusion's level-`(S−1)` corner is the
  rule's corner, so the step really speaks of two consecutive levels);
* `cflat_step_level`: the step at level `S = n + 2` (cap exponent `n + 1`) for every
  `n ≥ 19`, with the only remaining hypothesis the band condition `hv`.

The premise `12 ≤ cornerS` of m101 is thereby discharged at every level `S ≥ 21`, in
particular at the Lean base `S = 60` and at `S = 329`.  What is still open for §C-3 is
the band condition `hv` at each level and the treatment of `v` outside the band.

ε = 0.0035 instance.  This is **not** the published instance ε = 0.002.
Checked by `scripts/probe_brw/m102_cflat_level.py --selftest` and `--mutant all`.
-/

namespace RevPebbling.CflatLevel

open RevPebbling.ShapeMonotone RevPebbling.CapZone RevPebbling.CflatModel

noncomputable section

/-- The corner rule of `m48` (`b512fix.cfg`, anchor level 512, slope `a = 1341/4000`). -/
def cornerOf (S : ℕ) : ℝ :=
  (88394266807713 : ℝ) / 500000000000 + (1341 : ℝ) / 4000 * ((S : ℝ) - 512)

/-- The floor threshold `12 ≤ corner(S)` holds from level `21` on. -/
theorem corner_ge {S : ℕ} (hS : 21 ≤ S) : (12 : ℝ) ≤ cornerOf S := by
  have h : (21 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  unfold cornerOf
  linarith

/-- One level down moves the corner by exactly `a`. -/
theorem corner_pred (S : ℕ) : cornerOf (S + 1) - (1341 : ℝ) / 4000 = cornerOf S := by
  unfold cornerOf
  push_cast
  ring

/-- **Lemma C-flat at ε = 0.0035, indexed by the level.**  At level `S = n + 2`
(cap exponent `n + 1`), for every `n ≥ 19` and every `v` in the band
`v ≥ F_S · 2^{−1/100}`, the level-`S` model is bounded by one step into the level-`(S−1)`
model at the rule's corner. -/
theorem cflat_step_level {n v : ℕ} (hn : 19 ≤ n)
    (hv : (2 : ℝ) ^ cornerOf (n + 2) * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ)) :
    Psi (n + 1) eps0035.eval (cornerOf (n + 2)) v
      ≤ 1 + Psi n eps0035.eval (cornerOf (n + 1)) v
          + min (Psi (n + 1) eps0035.eval (cornerOf (n + 2)) (uSplit (cornerOf (n + 2))))
                (Psi n eps0035.eval (cornerOf (n + 1)) (v - uSplit (cornerOf (n + 2)))) := by
  have h := cflat_step_eps0035_model (n := n) (c := cornerOf (n + 2)) (v := v)
    (corner_ge (by omega)) hv
  have e : cornerOf (n + 2) - (1341 : ℝ) / 4000 = cornerOf (n + 1) := corner_pred (n + 1)
  rw [e] at h
  exact h

/-- **In the band, the level-`(S−1)` term at `v` is its cap.**  The band exponent
`−1/100` is above `−a = −1341/4000`, so `v ≥ F_S·2^{−1/100} ≥ F_S·2^{−a} = F_{S−1}`, and
`v` lies in the cap zone of level `S − 1` (`CapZone.eps0035_capzone`). -/
theorem prev_cap {n S : ℕ} {v : ℕ}
    (hv : (2 : ℝ) ^ cornerOf (S + 1) * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ)) :
    Psi n eps0035.eval (cornerOf S) v = 2 ^ n - 1 := by
  have hexp : (2 : ℝ) ^ (-((1341 : ℝ) / 4000)) ≤ (2 : ℝ) ^ (-((1 : ℝ) / 100)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hv' : (2 : ℝ) ^ cornerOf (S + 1) * (2 : ℝ) ^ (-((1341 : ℝ) / 4000)) ≤ (v : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hexp (Real.rpow_pos_of_pos (by norm_num) _).le) hv
  rw [← corner_pred S]
  exact eps0035_capzone hv'

/-- **The level step with the level-`(S−1)` term evaluated.**  Same hypotheses as
`cflat_step_level`; the `1 + Ψ_{S−1}(v)` of the conclusion is exactly `2^n`. -/
theorem cflat_step_level_cap {n v : ℕ} (hn : 19 ≤ n)
    (hv : (2 : ℝ) ^ cornerOf (n + 2) * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ)) :
    Psi (n + 1) eps0035.eval (cornerOf (n + 2)) v
      ≤ 2 ^ n
          + min (Psi (n + 1) eps0035.eval (cornerOf (n + 2)) (uSplit (cornerOf (n + 2))))
                (Psi n eps0035.eval (cornerOf (n + 1)) (v - uSplit (cornerOf (n + 2)))) := by
  have h := cflat_step_level hn hv
  have hc : Psi n eps0035.eval (cornerOf (n + 1)) v = 2 ^ n - 1 := prev_cap hv
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [hc] at h
  omega

/-- Non-vacuity of the band: every level has a `v` meeting `hv` (its ceiling). -/
theorem band_nonempty (S : ℕ) :
    ∃ v : ℕ, (2 : ℝ) ^ cornerOf S * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ) :=
  ⟨⌈(2 : ℝ) ^ cornerOf S * (2 : ℝ) ^ (-((1 : ℝ) / 100))⌉₊, Nat.le_ceil _⟩

/-- The Lean base level `S = 60` and the base-crossing level `S = 329` are covered. -/
example : (12 : ℝ) ≤ cornerOf 60 := corner_ge (by norm_num)
example : (12 : ℝ) ≤ cornerOf 329 := corner_ge (by norm_num)

end

#print axioms corner_ge
#print axioms corner_pred
#print axioms cflat_step_level
#print axioms band_nonempty
#print axioms prev_cap
#print axioms cflat_step_level_cap

end RevPebbling.CflatLevel
