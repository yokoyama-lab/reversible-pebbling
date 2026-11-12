import lean.C1bCert

/-!
# m101: Lemma C-flat at ε = 0.0035 with the split point chosen (§C-3, counting side)

`C1bCert.cflat_step_eps0035_half` closed the numeric gate C1♭ of Lemma C-flat at the
ε = 0.0035 anchor, but it still took the *counting* hypotheses as inputs:

```
hcap : ΨS v ≤ 2^(n+1) − 1          hu  : 2^n − 1 ≤ ΨS u
hule : u ≤ σ₁ · 2^{dp} · 2^{cornerS}  hw, hwr : w = v − u (in ℕ and in ℝ)
```

This module supplies all of them, by fixing the two things the lemma left open:

* **`ΨS` is the closed form of `m48`** at level `S`: `Psi (n+1) eps0035.eval cornerS`
  (`capexp = S − 1 = n + 1`, corner `corner_S`), the same model whose level-`(S−1)`
  instance `Psi n eps0035.eval (cornerS − a)` already appears in the conclusion.
* **the split point is `u := ⌈2^{x_½} · 2^{cornerS}⌉₊`**, the least integer at or above
  `σ₁ · F_S`, and `w := v − u`.

Then `hcap` is the `min` in `Psi`; `hu` is the `u` branch: `u ≥ σ₁·F_S` puts
`log₂ u − corner_S` at or right of `x_½`, where the shape is `≥ −1` (`eps0035_ge_neg_one`),
so the floor is `≥ 2^n`; `hule` is `⌈X⌉ < X + 1 ≤ X · 2^{1/512}` once `X ≥ 740`; and
`u ≤ v` (hence `hw`, `hwr`) is the `w` branch `v − u ≥ F_S · 2^{−a} > 0` of `TieBand`.

**The one new hypothesis is `12 ≤ cornerS`.**  It is the floor threshold: it gives
`X = 2^{x_½ + cornerS} ≥ 2^{9893/1024} ≥ 740`, and `740 · (2^{1/512} − 1) ≥ 1` is what
makes the interval `[X, X·2^{1/512}]` contain an integer.  It is a property of the level,
not of `v`.

## Domain of agreement

`Psi _ eps0035.eval _` is a faithful model of `m48`'s `Ψ` only where its argument
`log₂ x − corner` is `≥ x_½` (`CapZone`, "Domain of agreement").  `u_dom` and `v_dom`
below show that the level-`S` model is only ever evaluated there: at `u` the argument lies
in `[x_½, x_½ + 1/512]`, at `v` it is `≥ −1/100 > x_½`.  The level-`(S−1)` evaluations at
`v` and `w` are in the cap zone (argument `≥ 0`), as in `CapZone`.

## Certificates

Three Nat inequalities, checked by the kernel (`decide +kernel`, no `native_decide`):
`wL` (`NL/2^48 ≤ 2^{1/512}`, `NL = ND − 1`, the floor root), `wF` (`740 ≤ 2^{9893/1024}`)
and `wGap` (`740 · (NL − 2^48) ≥ 2^48`).  They reach `Real.rpow` through the general
bridge `C1bCert.le_rpow_of_nat`.

ε = 0.0035 instance.  This is **not** the published instance ε = 0.002.
-/

namespace RevPebbling.CflatModel

open RevPebbling.ShapeMonotone RevPebbling.CapZone RevPebbling.C1bCert

/-! ## Nat certificates (kernel) -/

/-- `⌊2^48 · 2^{1/512}⌋` (one below `C1bCert.ND`, which is the ceiling). -/
def NL : ℕ := 281856296460736

/-- `NL^512 ≤ 2 · 2^{512·48}`, i.e. `NL / 2^48 ≤ 2^{1/512}`. -/
theorem wL : NL ^ 512 * 2 ^ 0 ≤ 2 ^ 1 * 2 ^ (512 * K) := by decide +kernel

/-- `740^1024 ≤ 2^9893`, i.e. `740 ≤ 2^{9893/1024}`. -/
theorem wF : 740 ^ 1024 * 2 ^ 0 ≤ 2 ^ 9893 * 2 ^ (1024 * 0) := by decide +kernel

/-- `740 · (NL − 2^48) ≥ 2^48`. -/
theorem wGap : 2 ^ K + 740 * 2 ^ K ≤ 740 * NL := by decide +kernel

noncomputable section

theorem encL : (NL : ℝ) / 2 ^ K ≤ (2 : ℝ) ^ ((1 : ℝ) / 512) :=
  le_rpow_of_nat (q := 512) (P := 1) (M := 0) (by norm_num) (by norm_num) wL

theorem encF : (740 : ℝ) ≤ (2 : ℝ) ^ ((9893 : ℝ) / 1024) := by
  have h := le_rpow_of_nat (r := (9893 : ℝ) / 1024) (q := 1024) (P := 9893) (M := 0)
    (N := 740) (k := 0) (by norm_num) (by norm_num) wF
  simpa using h

/-- `x_½ ≥ −2395/1024` (the other side of `C1bCert.xhalf_le`; `norm_num`). -/
theorem xhalf_ge : -((2395 : ℝ) / 1024) ≤ eps0035.xr h0035 := by
  simp only [Shape.xr, h0035, eps0035]
  norm_num

/-! ## The split point -/

/-- `X = σ₁ · F_S = 2^{x_½} · 2^{cornerS}`. -/
def X (c : ℝ) : ℝ := (2 : ℝ) ^ (eps0035.xr h0035) * (2 : ℝ) ^ c

/-- **The split point** `u = ⌈σ₁ · F_S⌉₊`. -/
def uSplit (c : ℝ) : ℕ := ⌈X c⌉₊

theorem X_eq (c : ℝ) : X c = (2 : ℝ) ^ (eps0035.xr h0035 + c) := by
  rw [X, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

theorem X_pos (c : ℝ) : 0 < X c := by
  rw [X_eq]; exact Real.rpow_pos_of_pos (by norm_num) _

/-- **The floor threshold.** `12 ≤ cornerS` gives `X ≥ 740`. -/
theorem X_ge {c : ℝ} (hS : (12 : ℝ) ≤ c) : (740 : ℝ) ≤ X c := by
  have hx := xhalf_ge
  have hexp : (9893 : ℝ) / 1024 ≤ eps0035.xr h0035 + c := by linarith
  rw [X_eq]
  exact encF.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

theorem u_ge (c : ℝ) : X c ≤ (uSplit c : ℝ) := Nat.le_ceil _

/-- `X + 1 ≤ X · 2^{1/512}` once `X ≥ 740`. -/
theorem X_add_one_le {c : ℝ} (hS : (12 : ℝ) ≤ c) :
    X c + 1 ≤ X c * (2 : ℝ) ^ ((1 : ℝ) / 512) := by
  have hX := X_ge hS
  have hK : (0 : ℝ) < 2 ^ K := by positivity
  have hgap : (2 : ℝ) ^ K + 740 * 2 ^ K ≤ 740 * (NL : ℝ) := by exact_mod_cast wGap
  set g : ℝ := (NL : ℝ) / 2 ^ K with hgdef
  have hg : (741 : ℝ) ≤ 740 * g := by
    rw [hgdef, mul_div_assoc', le_div_iff₀ hK]; linarith
  have hg1 : (0 : ℝ) ≤ g - 1 := by linarith
  have hXg : X c + 1 ≤ X c * g := by
    nlinarith [mul_nonneg (sub_nonneg.2 hX) hg1]
  exact hXg.trans (mul_le_mul_of_nonneg_left encL (le_of_lt (X_pos c)))

/-- **`hule`**: `u ≤ σ₁ · 2^{1/512} · 2^{cornerS}`. -/
theorem hule_model {c : ℝ} (hS : (12 : ℝ) ≤ c) :
    (uSplit c : ℝ) ≤ (2 : ℝ) ^ (eps0035.xr h0035) * (2 : ℝ) ^ ((1 : ℝ) / 512)
                      * (2 : ℝ) ^ c := by
  have hlt : (uSplit c : ℝ) < X c + 1 := Nat.ceil_lt_add_one (le_of_lt (X_pos c))
  have h := X_add_one_le hS
  have e : X c * (2 : ℝ) ^ ((1 : ℝ) / 512)
      = (2 : ℝ) ^ (eps0035.xr h0035) * (2 : ℝ) ^ ((1 : ℝ) / 512) * (2 : ℝ) ^ c := by
    rw [X]; ring
  rw [← e]; linarith

/-! ## Domain of agreement -/

/-- At `u` the level-`S` argument `log₂ u − cornerS` lies in `[x_½, x_½ + 1/512]`. -/
theorem u_dom {c : ℝ} (hS : (12 : ℝ) ≤ c) :
    eps0035.xr h0035 ≤ Real.logb 2 (uSplit c : ℝ) - c ∧
      Real.logb 2 (uSplit c : ℝ) - c ≤ eps0035.xr h0035 + 1 / 512 := by
  have hXp := X_pos c
  have hup : 0 < (uSplit c : ℝ) := lt_of_lt_of_le hXp (u_ge c)
  constructor
  · have h1 : Real.logb 2 (X c) ≤ Real.logb 2 (uSplit c : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) hXp (u_ge c)
    rw [X_eq, Real.logb_rpow (by norm_num) (by norm_num)] at h1
    linarith
  · have hu : (uSplit c : ℝ) ≤ (2 : ℝ) ^ (eps0035.xr h0035 + 1 / 512 + c) := by
      have h := hule_model hS
      rwa [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
    have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num) hup hu
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at h1
    linarith

/-- At `v` (in the band, `v ≥ F_S · 2^{−1/100}`) the level-`S` argument is `≥ −1/100 > x_½`. -/
theorem v_dom {c : ℝ} {v : ℕ}
    (hv : (2 : ℝ) ^ c * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ)) :
    -((1 : ℝ) / 100) ≤ Real.logb 2 (v : ℝ) - c ∧
      eps0035.xr h0035 < Real.logb 2 (v : ℝ) - c := by
  have he : (2 : ℝ) ^ c * (2 : ℝ) ^ (-((1 : ℝ) / 100)) = (2 : ℝ) ^ (c - 1 / 100) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; ring_nf
  rw [he] at hv
  have h1 := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (Real.rpow_pos_of_pos (by norm_num) _) hv
  rw [Real.logb_rpow (by norm_num) (by norm_num)] at h1
  have hx := xhalf_le
  constructor <;> linarith

/-! ## The counting hypotheses -/

/-- **`hu`, the `u` branch**: the level-`S` model reaches `2^n − 1` at the split point. -/
theorem hu_model {n : ℕ} {c : ℝ} (hS : (12 : ℝ) ≤ c) :
    2 ^ n - 1 ≤ Psi (n + 1) eps0035.eval c (uSplit c) := by
  have hdom := (u_dom hS).1
  have hy : (-1 : ℝ) ≤ eps0035.eval (Real.logb 2 (uSplit c : ℝ) - c) := by
    have h := eps0035_ge_neg_one
      (s := Real.logb 2 (uSplit c : ℝ) - c - eps0035.xr h0035) (by linarith)
    have e : eps0035.xr h0035 + (Real.logb 2 (uSplit c : ℝ) - c - eps0035.xr h0035)
        = Real.logb 2 (uSplit c : ℝ) - c := by ring
    rwa [e] at h
  have hfl : 2 ^ n ≤ ⌊(2 : ℝ) ^ (((n + 1 : ℕ) : ℝ)
      + eps0035.eval (Real.logb 2 (uSplit c : ℝ) - c))⌋₊ := by
    apply Nat.le_floor
    have e : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ ((n : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]; push_cast; ring
    rw [e]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast; linarith
  unfold Psi
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  apply le_min <;> omega

/-- **`hcap`**: the model never exceeds its cap. -/
theorem hcap_model {n : ℕ} {c : ℝ} {v : ℕ} :
    Psi (n + 1) eps0035.eval c v ≤ 2 ^ (n + 1) - 1 := by
  unfold Psi; exact min_le_left _ _

/-- **`u ≤ v`**, from the `w` branch of `TieBand` (`v − u ≥ F_S · 2^{−a} > 0`). -/
theorem u_le_v {c : ℝ} {v : ℕ} (hS : (12 : ℝ) ≤ c)
    (hv : (2 : ℝ) ^ c * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ)) :
    uSplit c ≤ v := by
  have hw := RevPebbling.TieBand.w_branch_ge (F := (2 : ℝ) ^ c) (a := (1341 : ℝ) / 4000)
    (Real.rpow_pos_of_pos (by norm_num) _) (hC1_eps0035 sigma_half_le) hv (hule_model hS)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ c * (2 : ℝ) ^ (-((1341 : ℝ) / 4000)) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
  have hr : (uSplit c : ℝ) ≤ (v : ℝ) := by linarith
  exact_mod_cast hr

/-! ## Lemma C-flat with every counting hypothesis discharged -/

/-- **Lemma C-flat at ε = 0.0035, closed.**  With `Ψ_S` the level-`S` closed form,
`u = ⌈2^{x_½}·F_S⌉₊` and `w = v − u`, the step holds for every `v` in the band
`v ≥ F_S · 2^{−1/100}`, at every level whose corner is at least `12`.  No hypothesis on
`σ₁`, `u`, `w` or `Ψ_S` remains. -/
theorem cflat_step_eps0035_model {n : ℕ} {c : ℝ} {v : ℕ} (hS : (12 : ℝ) ≤ c)
    (hv : (2 : ℝ) ^ c * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ)) :
    Psi (n + 1) eps0035.eval c v
      ≤ 1 + Psi n eps0035.eval (c - (1341 : ℝ) / 4000) v
          + min (Psi (n + 1) eps0035.eval c (uSplit c))
                (Psi n eps0035.eval (c - (1341 : ℝ) / 4000) (v - uSplit c)) :=
  cflat_step_eps0035_half (ΨS := Psi (n + 1) eps0035.eval c) (w := v - uSplit c)
    hcap_model (hu_model hS) hv (hule_model hS) rfl
    (Nat.cast_sub (u_le_v hS hv))

/-! ## Non-vacuity: the two hypotheses are met at `cornerS = 12`, `v = 2^12` -/

example : Psi 12 eps0035.eval 12 4096
      ≤ 1 + Psi 11 eps0035.eval (12 - (1341 : ℝ) / 4000) 4096
          + min (Psi 12 eps0035.eval 12 (uSplit 12))
                (Psi 11 eps0035.eval (12 - (1341 : ℝ) / 4000) (4096 - uSplit 12)) := by
  refine cflat_step_eps0035_model (n := 11) (c := 12) (v := 4096) le_rfl ?_
  have h12 : (2 : ℝ) ^ (12 : ℝ) = 4096 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hle : (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  rw [h12]; push_cast; nlinarith

end

#print axioms wL
#print axioms wF
#print axioms wGap
#print axioms hule_model
#print axioms hu_model
#print axioms u_dom
#print axioms cflat_step_eps0035_model

end RevPebbling.CflatModel
