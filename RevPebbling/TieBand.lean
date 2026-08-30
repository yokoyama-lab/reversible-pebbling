import RevPebbling.CapAndSelfClosing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma C-flat (the corner tie band)

This mechanizes Lemma C-flat from `notes/tie_band_design.md` §1 of the companion
manuscript repository (the corner tie band of the upper-bound programme).

**Setting.**  A subsolution `Ψ_S(v) ≤ cap_S = 2^{S−1} − 1` obeys a count recursion
with a split `v = u + w`.  Near the corner the step margin collapses to `0`, so the
usual fixed-margin machinery (Lemma V₄ of `RevPebbling.FloorAbsorb`) does not reach.
Lemma C-flat closes the band by a *cap-reaching* argument that uses no margin and no
floor budget at all.  Its gate is the rational condition

```
(C1b)   σ₁ · 2^{δ'} + 2^{−a} ≤ 2^{t_c}
```

where `σ₁ = 2^{x_½}` is the shape constant, `a` is the per-level slope, `t_c ∈ (−a, 0)`
is the band cut, and `δ' > 0` is the split slack.

**The three branches.**

* `v` sits in the level-`(S−1)` cap zone (**T1**): once `v ≥ F_{S−1}` with
  `F_{S−1} = F_S · 2^{−a}`, `v` is already in the region where `Ψ_{S−1}` attains the
  cap `2^{S-2} − 1`.
* the `u` branch reaches `2^{S−2} − 1 = cap_{S−1}`, using that to the right of the
  shape's half-way point `x_½` the normalised shape `ŷ` is `≥ −1`, so the real
  subsolution value is `≥ 2^{S−2}`.
* `w = v − u ≥ F_{S−1}` also sits in the level-`(S−1)` cap zone, by (C1b): the slack
  `δ'` bought by the split is enough to keep `w` above the cap-zone threshold even
  after subtracting the whole `u`-budget `σ₁ · 2^{δ'} · F_S`.

The assembly is then exactly the cap identity of `RevPebbling.CapAndSelfClosing`:

```
1 + cap_{S−1} + cap_{S−1} = cap_S ≥ Ψ_S(v).
```

The external certified checker `m65_tie_band.py c1b` supplies the rational
enclosures used in the numeric section (§ eps0035) below.
-/

namespace RevPebbling.TieBand

open Real

/-! ## Floor loses at most a factor -/

/-- **Floor loses at most a factor `c`.**  If `X·(1 − c) ≥ 1` then `X·c ≤ ⌊X⌋`.
This is the elementary fact underlying the `S₄` threshold: once `X` is large enough
relative to the *relative* loss `c`, the floor of `X` still dominates `X·c`. -/
theorem floor_loses_at_most {c X : ℝ} (hc : 0 ≤ c) (hX : 1 ≤ X * (1 - c)) :
    X * c ≤ (⌊X⌋ : ℝ) := by
  have h := Int.sub_one_lt_floor X
  nlinarith

/-- The same fact with a rational upper bound `chi` on `c` and a threshold on `X`:
`X ≥ 1/(1−chi)` already suffices (this is the shape the `S₄` constant of the design
is pinned in). -/
theorem floor_loses_at_most_of_ge {c chi X : ℝ} (hc : 0 ≤ c) (hchi : c ≤ chi)
    (hchi1 : chi < 1) (hX : 1 / (1 - chi) ≤ X) : X * c ≤ (⌊X⌋ : ℝ) := by
  have hpos : (0 : ℝ) < 1 - chi := by linarith
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (by positivity) hX
  have h1 : (1 : ℝ) ≤ X * (1 - chi) := by
    rw [div_le_iff₀ hpos] at hX
    linarith
  have h2 : X * (1 - chi) ≤ X * (1 - c) := by
    have : c ≤ chi := hchi
    nlinarith
  exact floor_loses_at_most hc (by linarith)

/-! ## C1b from certified rational enclosures -/

/-- **C1b from certified rational enclosures.**  `s1` is a rational upper bound for
`σ₁`, `d2` for `2^{δ'}`, `a2` for `2^{−a}`, and `t2` a rational LOWER bound for
`2^{t_c}`.  This is the interface to the external checker `m65_tie_band.py c1b`. -/
theorem c1flat_of_enclosures {σ₁ dp a tc s1 d2 a2 t2 : ℝ}
    (hσ0 : 0 ≤ σ₁) (hσ : σ₁ ≤ s1) (hd : (2 : ℝ) ^ dp ≤ d2)
    (ha : (2 : ℝ) ^ (-a) ≤ a2) (ht : t2 ≤ (2 : ℝ) ^ tc)
    (hrat : s1 * d2 + a2 ≤ t2) :
    σ₁ * (2 : ℝ) ^ dp + (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ tc := by
  have hdp_pos : (0 : ℝ) < (2 : ℝ) ^ dp := Real.rpow_pos_of_pos (by norm_num) dp
  have hs1 : (0 : ℝ) ≤ s1 := le_trans hσ0 hσ
  have h1 : σ₁ * (2 : ℝ) ^ dp ≤ s1 * (2 : ℝ) ^ dp :=
    mul_le_mul_of_nonneg_right hσ (le_of_lt hdp_pos)
  have h2 : s1 * (2 : ℝ) ^ dp ≤ s1 * d2 := mul_le_mul_of_nonneg_left hd hs1
  nlinarith

/-! ## The three branches -/

/-- **The `w` branch — the load-bearing arithmetic of the lemma.**  Given (C1b),
if `v ≥ F·2^{tc}` and `u ≤ σ₁·2^{dp}·F` then `v − u ≥ F·2^{−a}`, i.e. `w = v − u`
sits above the level-`(S−1)` cap-zone threshold `F_{S-1} = F·2^{−a}`. -/
theorem w_branch_ge {F v u σ₁ dp a tc : ℝ} (hF : 0 < F)
    (hC1 : σ₁ * (2 : ℝ) ^ dp + (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ tc)
    (hv : F * (2 : ℝ) ^ tc ≤ v) (hu : u ≤ σ₁ * (2 : ℝ) ^ dp * F) :
    F * (2 : ℝ) ^ (-a) ≤ v - u := by
  nlinarith [hF, hC1, hv, hu]

/-- **The T1 branch.**  `v` itself is already above `F_{S−1} = F_S·2^{−a}`, as soon
as `v ≥ F·2^{tc}` and (C1b) holds — no split, no `u`-budget needed. -/
theorem t1_branch_ge {F v σ₁ dp a tc : ℝ} (hF : 0 < F) (hσ0 : 0 ≤ σ₁)
    (hC1 : σ₁ * (2 : ℝ) ^ dp + (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ tc)
    (hv : F * (2 : ℝ) ^ tc ≤ v) :
    F * (2 : ℝ) ^ (-a) ≤ v := by
  have hdp_pos : (0 : ℝ) < (2 : ℝ) ^ dp := Real.rpow_pos_of_pos (by norm_num) dp
  have hnonneg : (0 : ℝ) ≤ σ₁ * (2 : ℝ) ^ dp := mul_nonneg hσ0 (le_of_lt hdp_pos)
  have h2 : (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ tc := by linarith
  have h3 : F * (2 : ℝ) ^ (-a) ≤ F * (2 : ℝ) ^ tc :=
    mul_le_mul_of_nonneg_left h2 (le_of_lt hF)
  linarith

/-- **The split is proper.**  `u + 1 ≤ v`, which is what lets the count recursion be
applied at all: the `u`-branch and `w`-branch are then genuinely smaller instances. -/
theorem u_add_one_le {F v u σ₁ dp a tc : ℝ} (hF : 0 < F)
    (hone : 1 ≤ F * (2 : ℝ) ^ (-a))
    (hC1 : σ₁ * (2 : ℝ) ^ dp + (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ tc)
    (hv : F * (2 : ℝ) ^ tc ≤ v) (hu : u ≤ σ₁ * (2 : ℝ) ^ dp * F) :
    u + 1 ≤ v := by
  have hw := w_branch_ge hF hC1 hv hu
  linarith

/-! ## The `u` branch, shape side -/

/-- **The `u` branch, shape side.**  To the right of `x_½` the normalised shape `ŷ`
is at least `−1`, so the real subsolution value there is at least `2^{S−2}`. -/
theorem u_branch_real {y : ℝ} {n : ℝ} (hy : -1 ≤ y) :
    (2 : ℝ) ^ (n - 1) ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ y := by
  have hbase : (1 : ℝ) < 2 := by norm_num
  have heq : (2 : ℝ) ^ n * (2 : ℝ) ^ y = (2 : ℝ) ^ (n + y) :=
    (Real.rpow_add (by norm_num) n y).symm
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hbase) (by linarith)

/-- **The monotonicity step that produces the hypothesis of `u_branch_real`.**  If
`ŷ` is monotone on `Set.Ici xh`, `ŷ xh = −1`, and the evaluation point is `xh + s`
with `s ≥ 0`, then `ŷ (xh + s) ≥ −1`. -/
theorem yhat_ge_neg_one {ŷ : ℝ → ℝ} {xh s : ℝ} (hmono : MonotoneOn ŷ (Set.Ici xh))
    (hxh : ŷ xh = -1) (hs : 0 ≤ s) : -1 ≤ ŷ (xh + s) := by
  have hle : ŷ xh ≤ ŷ (xh + s) :=
    hmono (Set.left_mem_Ici) (by simp [Set.mem_Ici]; linarith) (by linarith)
  rw [hxh] at hle
  exact hle

/-! ## The assembly -/

/-- **The assembly, over `Nat`, with the cap identity.**  This is the conclusion of
Lemma C-flat: given the T1 branch, the `u` branch, and the `w` branch all reaching
their respective level-`(S−1)` caps, the `min` of the `u`/`w` branches plus `1` plus
the T1 value dominates `Ψ_S(v)`. -/
theorem cflat_assembly {ΨS ΨS1 : ℕ → ℕ} {n v u w : ℕ}
    (hcap : ΨS v ≤ 2 ^ (n + 1) - 1)
    (hT1 : 2 ^ n - 1 ≤ ΨS1 v)
    (hu : 2 ^ n - 1 ≤ ΨS u)
    (hw : 2 ^ n - 1 ≤ ΨS1 w) :
    ΨS v ≤ 1 + ΨS1 v + min (ΨS u) (ΨS1 w) := by
  have hmin : 2 ^ n - 1 ≤ min (ΨS u) (ΨS1 w) := le_min hu hw
  have hcs := RevPebbling.CapAndSelfClosing.cap_step n
  have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-! ## The packaged step -/

/-- **The packaged lemma.**  From the geometric hypotheses (the cap-zone
characterisation at level `S−1`, the `u` branch, the unconditional cap bound) plus
C1b, the step holds.  Here `F : ℝ` is `F_S`, `Fp = F·2^{−a}` is `F_{S−1}`, and
`hcapzone` is the characterisation "at level `S−1` everything at or above `F_{S−1}`
is at the cap". -/
theorem cflat_step {ΨS ΨS1 : ℕ → ℕ} {n : ℕ} {F σ₁ dp a tc : ℝ} {v u w : ℕ}
    (hF : 0 < F)
    (hC1 : σ₁ * (2 : ℝ) ^ dp + (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ tc)
    (hσ0 : 0 ≤ σ₁)
    (hcapzone : ∀ x : ℕ, F * (2 : ℝ) ^ (-a) ≤ (x : ℝ) → 2 ^ n - 1 ≤ ΨS1 x)
    (hcap : ΨS v ≤ 2 ^ (n + 1) - 1)
    (hu : 2 ^ n - 1 ≤ ΨS u)
    (hv : F * (2 : ℝ) ^ tc ≤ (v : ℝ))
    (hule : (u : ℝ) ≤ σ₁ * (2 : ℝ) ^ dp * F)
    (hw : (w : ℕ) = v - u) (hwr : ((w : ℕ) : ℝ) = (v : ℝ) - (u : ℝ)) :
    ΨS v ≤ 1 + ΨS1 v + min (ΨS u) (ΨS1 w) := by
  have hT1 : F * (2 : ℝ) ^ (-a) ≤ (v : ℝ) := t1_branch_ge hF hσ0 hC1 hv
  have hT1' : 2 ^ n - 1 ≤ ΨS1 v := hcapzone v hT1
  have hwbranch : F * (2 : ℝ) ^ (-a) ≤ (v : ℝ) - (u : ℝ) := w_branch_ge hF hC1 hv hule
  have hwbranch' : F * (2 : ℝ) ^ (-a) ≤ ((w : ℕ) : ℝ) := by rw [hwr]; exact hwbranch
  have hW' : 2 ^ n - 1 ≤ ΨS1 w := hcapzone w hwbranch'
  exact cflat_assembly hcap hT1' hu hW'

/-! ## Non-vacuity -/

/-- **The hypotheses of `cflat_step` are simultaneously satisfiable, and the bound it
proves is tight.**  A statement whose hypotheses were contradictory would be proved just
as easily, so a witness is part of the check.  Here `n = S − 1 = 3`, `F_S = 100`,
`a = 2`, `t_c = −1` (so `t_c ∈ (−a, 0)`, the genuine band case), `δ' = 0`, `σ₁ = 1/8`,
`v = 60`, `u = 12`, `w = 48`; the conclusion comes out as `15 ≤ 1 + 7 + 7`, i.e.
`cap_S ≤ 1 + cap_{S−1} + cap_{S−1}` **with equality** — the cap identity, as it should
be at the corner. -/
example : (15 : ℕ) ≤ 1 + 7 + min 15 7 := by
  have h2d : (2 : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero 2
  have h2t : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
    rw [show (-(1 : ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have h2a : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  exact cflat_step (ΨS := fun _ => 15) (ΨS1 := fun _ => 7) (n := 3) (F := 100)
    (σ₁ := 1 / 8) (dp := 0) (a := 2) (tc := -1) (v := 60) (u := 12) (w := 48)
    (by norm_num) (by rw [h2d, h2a, h2t]; norm_num) (by norm_num)
    (fun _ _ => by norm_num) (by norm_num) (by norm_num)
    (by rw [h2t]; norm_num) (by rw [h2d]; norm_num) (by norm_num) (by norm_num)

/-! ## Numeric section: the ε = 0.0035 anchor -/

/-- The rational core of C1b at the ε = 0.0035 anchor, as certified by
`m65_tie_band.py`. -/
theorem c1flat_rational_eps0035 :
    (0.197765986 : ℝ) * 1.001354720 + 0.792646770 ≤ 0.993092495 := by norm_num

/-- C1b itself at that anchor, given the four certified enclosures. -/
theorem c1flat_eps0035 {σ₁ : ℝ} (hσ0 : 0 ≤ σ₁) (hσ : σ₁ ≤ 0.197765986)
    (hd : (2 : ℝ) ^ ((1 : ℝ) / 512) ≤ 1.001354720)
    (ha : (2 : ℝ) ^ (-((1341 : ℝ) / 4000)) ≤ 0.792646770)
    (ht : (0.993092495 : ℝ) ≤ (2 : ℝ) ^ (-((1 : ℝ) / 100))) :
    σ₁ * (2 : ℝ) ^ ((1 : ℝ) / 512) + (2 : ℝ) ^ (-((1341 : ℝ) / 4000))
      ≤ (2 : ℝ) ^ (-((1 : ℝ) / 100)) :=
  c1flat_of_enclosures hσ0 hσ hd ha ht c1flat_rational_eps0035

/-- The `S₄` threshold made explicit: with `δ' = 1/512`, `X ≥ 740` already forces the
floor of `X` to lose at most the factor `2^{−δ'}`.  (`2^{−1/512} ≤ 0.998647113` is the
certified enclosure; `1/(1 − 0.998647113) < 740`.) -/
theorem floor_loses_at_most_eps0035 {X : ℝ} (hX : (740 : ℝ) ≤ X)
    (hc : (2 : ℝ) ^ (-((1 : ℝ) / 512)) ≤ 0.998647113) :
    X * (2 : ℝ) ^ (-((1 : ℝ) / 512)) ≤ (⌊X⌋ : ℝ) := by
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-((1 : ℝ) / 512)) :=
    le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have hthresh : (1 : ℝ) / (1 - 0.998647113) ≤ 740 := by norm_num
  exact floor_loses_at_most_of_ge hpos hc (by norm_num) (le_trans hthresh hX)

/-! ## Axiom audit (printed on every build) -/

#print axioms cflat_step
#print axioms c1flat_eps0035
#print axioms floor_loses_at_most_eps0035

/-! ## What is and is not proved here

The analytic inputs — the cap-zone characterisation at level `S−1` (`hcapzone` in
`cflat_step`), monotonicity of the shape `ŷ` to the right of `x_½` (the hypothesis
`hmono` of `yhat_ge_neg_one`), the geometric law `F_{S−1} = F_S · 2^{−a}` (baked into
the statements as the constant `F * 2^{-a}`), and the numerical enclosures of the
powers of two (the hypotheses `hd`, `ha`, `ht` of `c1flat_eps0035` and `hc` of
`floor_loses_at_most_eps0035`) — are HYPOTHESES here, discharged externally by the
certified checkers `m46`/`m65`.  What this module proves unconditionally is the
accounting of Lemma C-flat itself: given those inputs, the three branches (T1, `u`,
`w`) combine through the cap identity to close the step `Ψ_S(v) ≤ 1 + Ψ_{S−1}(v) +
min(Ψ_S(u), Ψ_{S−1}(w))`, and the rational core of the numeric anchor `ε = 0.0035`
checks out by `norm_num` alone.
-/

end RevPebbling.TieBand
