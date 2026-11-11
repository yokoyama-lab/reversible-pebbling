import RevPebbling.CapZone

/-!
# m100: the C1♭ gate at ε = 0.0035 from a Nat certificate (§C-3)

`RevPebbling.CapZone.cflat_step_eps0035` still carries the real hypothesis

    hC1 : σ₁ · 2^{dp} + 2^{−a} ≤ 2^{tc}      (dp = 1/512, a = 1341/4000, tc = −1/100).

`scripts/probe_brw/m99_c1b_nat_cert.py` reduced it to five inequalities between natural
numbers (K = 48 dyadic enclosures D, A, T, S of 2^{1/512}, 2^{−a}, 2^{−1/100},
2^{x̄} with x̄ = −2394/1024).  Here

* the five Nat inequalities are checked by the **kernel's `decide`** (GMP-backed `Nat.pow`
  and `Nat.ble`; no `native_decide`, so no `Lean.ofReduceBool` and no auxiliary axiom);
* the bridge from a Nat power inequality to a bound on `Real.rpow` is a general lemma
  (`rpow_le_of_nat`, `le_rpow_of_nat`: `(2^r)^q = 2^{rq}` and monotonicity of `t ↦ t^q`);
* `hC1_eps0035` discharges `hC1` for every `σ₁ ≤ 2^{x̄}`, and
  `cflat_step_eps0035_cert` is `cflat_step_eps0035` with `hC1` removed.

What is *not* done here: `σ₁` is the value `2^{x_half}` of the family at its half point,
and `x_half ≤ x̄ = −2394/1024` is a Python fact (m99 asserts it over `Fraction`s, layer 2).
The theorem below takes `σ₁ ≤ 2^{x̄}` as its hypothesis instead of `hC1`.
This is the ε = 0.0035 instance, not the published ε = 0.002 one.
-/

namespace RevPebbling.C1bCert

open RevPebbling.ShapeMonotone RevPebbling.CapZone

/-! ## The certificate (m99, K = 48) -/

def K : ℕ := 48
def ND : ℕ := 281856296460737
def NA : ℕ := 223110230982063
def NT : ℕ := 279530687024666
def NS : ℕ := 55675559126184

/-- `D = ND/2^K ≥ 2^{1/512}`. -/
theorem wD : 2 ^ 1 * 2 ^ (512 * K) ≤ ND ^ 512 * 2 ^ 0 := by decide +kernel
/-- `A = NA/2^K ≥ 2^{−1341/4000}`. -/
theorem wA : 2 ^ 0 * 2 ^ (4000 * K) ≤ NA ^ 4000 * 2 ^ 1341 := by decide +kernel
/-- `T = NT/2^K ≤ 2^{−1/100}`. -/
theorem wT : NT ^ 100 * 2 ^ 1 ≤ 2 ^ 0 * 2 ^ (100 * K) := by decide +kernel
/-- `S = NS/2^K ≥ 2^{−2394/1024}`. -/
theorem wS : 2 ^ 0 * 2 ^ (1024 * K) ≤ NS ^ 1024 * 2 ^ 2394 := by decide +kernel
/-- `S·D + A ≤ T`, cleared of denominators. -/
theorem wSum : NS * ND + NA * 2 ^ K ≤ NT * 2 ^ K := by decide +kernel

/-! ## From a Nat power inequality to a bound on `2^r` (general) -/

noncomputable section

/-- `(2^r)^q = 2^P / 2^M` when `r·q = P − M`. -/
theorem rpow_pow_eq {r : ℝ} {q P M : ℕ} (hr : r * q = (P : ℝ) - M) :
    ((2 : ℝ) ^ r) ^ q = (2 : ℝ) ^ P / (2 : ℝ) ^ M := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), hr,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, Real.rpow_natCast]

/-- **Lower bound.** `2^P · 2^{qk} ≤ N^q · 2^M` and `r·q = P − M` give `2^r ≤ N/2^k`. -/
theorem rpow_le_of_nat {r : ℝ} {q P M N k : ℕ} (hq : q ≠ 0)
    (hr : r * q = (P : ℝ) - M) (h : 2 ^ P * 2 ^ (q * k) ≤ N ^ q * 2 ^ M) :
    (2 : ℝ) ^ r ≤ (N : ℝ) / 2 ^ k := by
  have hx : 0 ≤ (2 : ℝ) ^ r := Real.rpow_nonneg (by norm_num) r
  have hy : 0 ≤ (N : ℝ) / 2 ^ k := by positivity
  rw [← pow_le_pow_iff_left₀ hx hy hq, rpow_pow_eq hr, div_pow, ← pow_mul,
    div_le_div_iff₀ (by positivity) (by positivity), mul_comm k q]
  exact_mod_cast h

/-- **Upper bound.** `N^q · 2^M ≤ 2^P · 2^{qk}` and `r·q = P − M` give `N/2^k ≤ 2^r`. -/
theorem le_rpow_of_nat {r : ℝ} {q P M N k : ℕ} (hq : q ≠ 0)
    (hr : r * q = (P : ℝ) - M) (h : N ^ q * 2 ^ M ≤ 2 ^ P * 2 ^ (q * k)) :
    (N : ℝ) / 2 ^ k ≤ (2 : ℝ) ^ r := by
  have hx : 0 ≤ (2 : ℝ) ^ r := Real.rpow_nonneg (by norm_num) r
  have hy : 0 ≤ (N : ℝ) / 2 ^ k := by positivity
  rw [← pow_le_pow_iff_left₀ hy hx hq, rpow_pow_eq hr, div_pow, ← pow_mul,
    div_le_div_iff₀ (by positivity) (by positivity), mul_comm k q]
  exact_mod_cast h

/-! ## The four enclosures and their combination -/

theorem encD : (2 : ℝ) ^ ((1 : ℝ) / 512) ≤ (ND : ℝ) / 2 ^ K :=
  rpow_le_of_nat (q := 512) (P := 1) (M := 0) (by norm_num) (by norm_num) wD

theorem encA : (2 : ℝ) ^ (-((1341 : ℝ) / 4000)) ≤ (NA : ℝ) / 2 ^ K :=
  rpow_le_of_nat (q := 4000) (P := 0) (M := 1341) (by norm_num) (by norm_num) wA

theorem encS : (2 : ℝ) ^ (-((2394 : ℝ) / 1024)) ≤ (NS : ℝ) / 2 ^ K :=
  rpow_le_of_nat (q := 1024) (P := 0) (M := 2394) (by norm_num) (by norm_num) wS

theorem encT : (NT : ℝ) / 2 ^ K ≤ (2 : ℝ) ^ (-((1 : ℝ) / 100)) :=
  le_rpow_of_nat (q := 100) (P := 0) (M := 1) (by norm_num) (by norm_num) wT

theorem encSum : (NS : ℝ) / 2 ^ K * ((ND : ℝ) / 2 ^ K) + (NA : ℝ) / 2 ^ K ≤ (NT : ℝ) / 2 ^ K := by
  have ht : (0 : ℝ) < 2 ^ K := by positivity
  have h : (NS : ℝ) * ND + NA * 2 ^ K ≤ NT * 2 ^ K := by exact_mod_cast wSum
  have e : (NS : ℝ) / 2 ^ K * ((ND : ℝ) / 2 ^ K) + (NA : ℝ) / 2 ^ K
      = ((NS : ℝ) * ND + NA * 2 ^ K) / 2 ^ K / 2 ^ K := by
    field_simp
  rw [e, div_le_div_iff_of_pos_right ht, div_le_iff₀ ht]
  exact h

/-- **`hC1` at ε = 0.0035, for every `σ₁ ≤ 2^{−2394/1024}`.** -/
theorem hC1_eps0035 {σ₁ : ℝ} (hσ : σ₁ ≤ (2 : ℝ) ^ (-((2394 : ℝ) / 1024))) :
    σ₁ * (2 : ℝ) ^ ((1 : ℝ) / 512) + (2 : ℝ) ^ (-((1341 : ℝ) / 4000))
      ≤ (2 : ℝ) ^ (-((1 : ℝ) / 100)) := by
  have hD0 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 512) := Real.rpow_nonneg (by norm_num) _
  have hS0 : 0 ≤ (NS : ℝ) / 2 ^ K := by positivity
  calc σ₁ * (2 : ℝ) ^ ((1 : ℝ) / 512) + (2 : ℝ) ^ (-((1341 : ℝ) / 4000))
      ≤ (NS : ℝ) / 2 ^ K * ((ND : ℝ) / 2 ^ K) + (NA : ℝ) / 2 ^ K :=
        add_le_add (mul_le_mul (hσ.trans encS) encD hD0 hS0) encA
    _ ≤ (NT : ℝ) / 2 ^ K := encSum
    _ ≤ (2 : ℝ) ^ (-((1 : ℝ) / 100)) := encT

/-- **Lemma C-flat at ε = 0.0035 with `hC1` discharged.**  `cflat_step_eps0035` with
`dp = 1/512`, `a = 1341/4000`, `tc = −1/100` fixed and the real hypothesis `hC1` replaced
by `σ₁ ≤ 2^{−2394/1024}`. -/
theorem cflat_step_eps0035_cert {ΨS : ℕ → ℕ} {n : ℕ} {cornerS σ₁ : ℝ} {v u w : ℕ}
    (hσ : σ₁ ≤ (2 : ℝ) ^ (-((2394 : ℝ) / 1024)))
    (hσ0 : 0 ≤ σ₁)
    (hcap : ΨS v ≤ 2 ^ (n + 1) - 1)
    (hu : 2 ^ n - 1 ≤ ΨS u)
    (hv : (2 : ℝ) ^ cornerS * (2 : ℝ) ^ (-((1 : ℝ) / 100)) ≤ (v : ℝ))
    (hule : (u : ℝ) ≤ σ₁ * (2 : ℝ) ^ ((1 : ℝ) / 512) * (2 : ℝ) ^ cornerS)
    (hw : (w : ℕ) = v - u) (hwr : ((w : ℕ) : ℝ) = (v : ℝ) - (u : ℝ)) :
    ΨS v ≤ 1 + Psi n eps0035.eval (cornerS - (1341 : ℝ) / 4000) v
             + min (ΨS u) (Psi n eps0035.eval (cornerS - (1341 : ℝ) / 4000) w) :=
  cflat_step_eps0035 (hC1_eps0035 hσ) hσ0 hcap hu hv hule hw hwr

end

#print axioms wA
#print axioms hC1_eps0035
#print axioms cflat_step_eps0035_cert

end RevPebbling.C1bCert
