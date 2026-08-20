import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Lemma 1: reading `c ≤ 2^{1+λ}` off an exponential bound on `M_S`

The last symbolic piece of the upper-bound programme (companion
manuscript, `notes/lemma_U_clean.md`).  Once `Ψ_S ≤ C_S` is in hand
(Lemma 2) the construction gives

```
M_S ≤ K · 2^{λ S}
```

for a constant `K` that does **not** depend on `S` (it absorbs the front
offset `Δ`, the readout point `ζ_½ = 1/q_h`, and the polynomial factor
`S` from summing `m_j`; all of them are killed by the `(S−1)`-st root).
The growth constant is `d = lim M_S^{1/(S−1)}` and `c = 2d`
(`Unconditional.tendsto_rowMax_root_uncond`), so the claim is

```
log M_S / (S−1)  →  λ · ln 2      hence  d ≤ 2^λ  and  c ≤ 2^{1+λ}.
```

The content is the exact identity

```
(log K + λ S ln 2)/(S−1)  =  λ ln 2  +  (log K + λ ln 2)/(S−1)
```

— the whole `S`-dependence of the bound sits in one `1/(S−1)` term,
whatever `K` is.  **`K` never has to be estimated.**  That is why the
front offset `Δ` may be taken as large as Lemma 0 wants (`Δ ≥ (S₀−1)/q_h`)
at no cost to `c`.
-/

namespace RevPebbling.Readout

open Real Filter Topology

/-- The exact split of the bound into its limit and a `1/(S−1)` remainder. -/
theorem bound_split (K lam S : ℝ) (hS : S ≠ 1) :
    (Real.log K + lam * S * Real.log 2) / (S - 1)
      = lam * Real.log 2 + (Real.log K + lam * Real.log 2) / (S - 1) := by
  have h : S - 1 ≠ 0 := sub_ne_zero.mpr hS
  field_simp
  ring

/-- **Lemma 1, finite form.**  An exponential bound on `M` gives a bound on
`log M / (S−1)` that is `λ·ln 2` plus a `1/(S−1)` remainder. -/
theorem log_root_le {M K lam S : ℝ} (hM : 0 < M) (hK : 0 < K) (hS : 1 < S)
    (hbound : M ≤ K * (2 : ℝ) ^ (lam * S)) :
    Real.log M / (S - 1)
      ≤ lam * Real.log 2 + (Real.log K + lam * Real.log 2) / (S - 1) := by
  have hS1 : (0 : ℝ) < S - 1 := by linarith
  have hlog : Real.log M ≤ Real.log K + lam * S * Real.log 2 := by
    have h1 : Real.log M ≤ Real.log (K * (2 : ℝ) ^ (lam * S)) :=
      Real.log_le_log hM hbound
    rwa [Real.log_mul (ne_of_gt hK) (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)),
        Real.log_rpow (by norm_num)] at h1
  calc Real.log M / (S - 1)
      ≤ (Real.log K + lam * S * Real.log 2) / (S - 1) := by
        gcongr
    _ = lam * Real.log 2 + (Real.log K + lam * Real.log 2) / (S - 1) :=
        bound_split K lam S (by linarith)

/-- The remainder vanishes: `c/(S−1) → 0` as `S → ∞`, for any constant `c`. -/
theorem remainder_tendsto_zero (c : ℝ) :
    Tendsto (fun S : ℝ => c / (S - 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun S : ℝ => S - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) tendsto_id
  exact tendsto_const_nhds.div_atTop h

/-- **Lemma 1.**  `log M_S / (S−1) → λ·ln 2` from above: the bound tends to
exactly `λ·ln 2`, so `d ≤ 2^λ` and `c = 2d ≤ 2^{1+λ}`. -/
theorem bound_tendsto (K lam : ℝ) :
    Tendsto (fun S : ℝ => lam * Real.log 2 + (Real.log K + lam * Real.log 2) / (S - 1))
      atTop (𝓝 (lam * Real.log 2)) := by
  have h := remainder_tendsto_zero (Real.log K + lam * Real.log 2)
  simpa using tendsto_const_nhds.add h

end RevPebbling.Readout
