#!/usr/bin/env python3
"""Generate `RevPebbling/KappaEnclosure.lean`: the enclosure of `kappa*`.

The Lean file is a certificate, and this is what produces it.  Nothing
emitted here is trusted on the Decimal arithmetic: every inequality is
first verified in **exact rational arithmetic**, by the same chain the
Lean proof runs (the same log enclosures, the same endpoint division).
Decimal is used only to *design* the covering grid, and a bad grid makes
the emitted file fail to compile -- it cannot make it prove something
false.

Usage:  python3 scripts/gen_kappa_enclosure.py
        (rewrites RevPebbling/KappaEnclosure.lean in place)
"""

from decimal import Decimal as D, getcontext
from fractions import Fraction as F
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "RevPebbling" / "KappaEnclosure.lean"

getcontext().prec = 70
L2D = D(2).ln()
KHI = F(3317423792563106, 10 ** 16)
KLO = F(3317423792563105, 10 ** 16)
KDES = F(33174237925631059, 10 ** 17)     # KHI - 1e-18, for the grid design
RMAX = D('1.8')
EPS = F(1, 10 ** 22)                      # target width of each log enclosure
RND = 32                                  # decimals kept in the emitted table
THSTAR = D('0.7084396381715338555293920226324942887033943121434826303144')


def rdown(x: F, p: int) -> F:
    """largest multiple of 10^-p that is <= x"""
    s = 10 ** p
    return F((x * s).numerator // (x * s).denominator, s)


def rup(x: F, p: int) -> F:
    s = 10 ** p
    n = x * s
    return F(-((-n.numerator) // n.denominator), s)


def ftod(x: F) -> D:
    return D(x.numerator) / D(x.denominator)


def dec_str(x: F) -> str:
    """emit as NUM / DEN with DEN a power of ten (or an integer)"""
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator} / {x.denominator}"



class LogCert:
    """Rational enclosure  lo <= log y <= hi, with the Lean data."""

    def __init__(self, y: F, lo: F, hi: F, kind: str, data: dict):
        self.y, self.lo, self.hi, self.kind, self.data = y, lo, hi, kind, data
        self.name = None


def series_cert(z: F, eps: F):
    """lo <= log z <= hi via the Taylor series of log(1-x), x = 1-z."""
    x = 1 - z
    assert abs(x) < 1
    B = rup(abs(x), 12)
    assert B < 1
    E = F(1, 10 ** 24)
    while E > eps / 4:
        E /= 10
    n = 1
    while B ** (n + 1) / (1 - B) > E:
        n += 1
    S = sum((x ** (i + 1)) / F(i + 1) for i in range(n))
    p = 45
    Slo, Shi = rdown(S, p), rup(S, p)
    lo, hi = -Shi - E, -Slo + E
    return LogCert(z, lo, hi, 'series',
                   dict(B=B, n=n, Slo=Slo, Shi=Shi, E=E))



def exp_cert(x: F, eps: F = F(1, 10 ** 24)):
    """Slo/Shi/E for `Real.exp x`, verified exactly."""
    import math
    B = rup(abs(x), 12)
    assert B <= 1
    n = 1
    while B ** n * F(n + 1, math.factorial(n) * n) > eps:
        n += 1
    S = sum(x ** m / F(math.factorial(m)) for m in range(n))
    Slo, Shi = rdown(S, 40), rup(S, 40)
    return dict(B=B, n=n, Slo=Slo, Shi=Shi, E=eps, lo=Slo - eps, hi=Shi + eps)


def H(t):
    return -t * t.ln() - (1 - t) * (1 - t).ln()


def LamD(t, l1, l2):
    return (t * l1 + (1 - t) * l2) / H(t) - l1 / L2D


def logsD(r):
    return (r.ln(), (1 + r).ln())


def qc(l1, l2):
    q = D('1.5')
    for _ in range(200):
        a, b = (-q * l1).exp(), (-q * l2).exp()
        step = (a + b - 1) / (-l1 * a - l2 * b)
        q -= step
        if abs(step) < D(10) ** -60:
            break
    return q


def thstar(r):
    l1, l2 = logsD(r)
    return (-qc(l1, l2) * l1).exp()


def pairval(t, P1, P2):
    return max(LamD(t, *P1), LamD(t, *P2))



def greedy(K, rmax, shrink=D('0.97')):
    pts, ths = [D(1)], []
    r = D(1)
    while True:
        P = logsD(r)

        def ok(r2):
            t = thstar((r * r2).sqrt())
            return pairval(t, P, logsD(r2)) <= K, t

        good, t = ok(rmax)
        if good:
            pts.append(rmax)
            ths.append(t)
            break
        lo, hi = r, rmax
        for _ in range(200):
            m = (lo + hi) / 2
            g, _ = ok(m)
            if g:
                lo = m
            else:
                hi = m
            if hi - lo < (hi + lo) * D(10) ** -50:
                break
        r2 = r + shrink * (lo - r)
        _, t = ok(r2)
        pts.append(r2)
        ths.append(t)
        r = r2
        if len(ths) > 500:
            sys.exit('too many intervals')
    return pts, ths



def rho_of_t(t: D) -> D:
    """root of t*ln r = ln (1+r), r > 1, by Newton"""
    r = D('1.2554')
    for _ in range(300):
        f = t * r.ln() - (1 + r).ln()
        df = t / r - 1 / (1 + r)
        step = f / df
        r -= step
        if abs(step) < D(10) ** -60:
            break
    return r



PREAMBLE = r"""import RevPebbling.KappaAttainment

/-!
# `κ*` enclosed inside Lean

`Final.c_eq_two_rpow_kappaStar` pins the growth rate to `c = 2^{1+κ*}`
with `κ* = sup_q V(q)`, but says nothing about the *value* of `κ*`; the
sixteen-digit enclosure was carried from `rocq/KappaStar.v`
(CoqInterval) as the two hypotheses `Final.KappaUpperBound Final.KHI`
and `Final.KappaAttained Final.KLO`.  This file discharges both, so the
enclosure is a Lean theorem and the Rocq layer is no longer load-bearing
for the value of `c`.

## The route

Lean has no interval-arithmetic tactic, and the integer-power trick of
`CriticalRootRat` is unusable here: the witness slope has a sixteen-digit
denominator, so the certificates would be `10^16`-th powers.  Everything
below is instead built on **one** numerical primitive — a rational
enclosure of `Real.log` of a rational, from Mathlib's Taylor bound
`Real.abs_log_sub_add_sum_range_le` — plus two pieces of convexity.

**Upper bound.**  `κ* ≤ K` is a statement about a *supremum*, which
ordinarily needs the whole root curve.  Gibbs' inequality removes the
implicit function: at any root, `ρ^{-q} + (1+ρ)^{-q} = 1` is a Kraft
equality, so for **every** weight `θ ∈ (0,1)`

  `1/q ≤ (θ·log ρ + (1-θ)·log (1+ρ)) / H(θ)`,   `H(θ) = -θ log θ - (1-θ) log (1-θ)`,

by weighted AM–GM (`Real.geom_mean_le_arith_mean2_weighted`).  Hence
`V(q) ≤ Λ(θ, ρ)` where `Λ` is an **explicit** function of `ρ` alone —
no root-finding, no derivatives.  `Λ(θ, ·)` is convex in `log ρ`
(`log_one_add_convex`, again two AM–GMs), so on an interval it is at most
its larger endpoint value.  Covering `ρ ∈ [1, 9/5]` by 34 intervals, each
with its own `θ`, and handling `ρ ≥ 9/5` by `θ = 1/2` — where
`Λ(1/2, ρ) = ½·log₂(1 + 1/ρ)` is decreasing — closes the bound at
`K = KHI'`.

The 34 intervals are the whole cost of the tangency: `Λ(θ*, ·)` touches
the true `V` curve at `ρ*`, so the grid must be geometric there.  Their
widths run from `4·10^{-11}` (at `ρ*`) to `0.36`.

**Lower bound.**  Read the same inequality backwards.  Fix a rational
`a ∈ (1/2, 1)` — the intended Gibbs weight — and let
`t = log (1-a) / log a > 1`.  The equation `ρ^t = 1 + ρ` has a root
`ρ > 1` (intermediate value theorem), and setting `q = -log a / log ρ`
makes `ρ^{-q} = a` and `(1+ρ)^{-q} = 1-a` *exactly*, so `(q, ρ)` is a
genuine root of `G` and

  `V(q) = log ρ · (-1/log a - 1/log 2)`.

A rational lower bound `B ≤ ρ` follows from `t·log B ≤ log (1+B)` alone,
because `x ↦ t log x - log (1+x)` is strictly increasing for `t > 1` —
which is elementary, not a derivative computation.  So the lower bound
needs five logarithms and no covering at all.

## What is machine-checked here

Nothing below is `native_decide`, `sorry`, or carried: the axioms are the
three standard ones.  The numerals were produced by
`scripts/gen_kappa_enclosure.py`, which verifies the same inequality chain
in exact rational arithmetic before emitting it.
-/

namespace RevPebbling.KappaEnclosure

open Finset RevPebbling.CriticalRoot RevPebbling.Final

/-! ## 1. Rational enclosures for `Real.log` -/

/-- **The one numerical primitive.**  Mathlib's Taylor estimate
`|∑_{i<n} x^{i+1}/(i+1) + log (1-x)| ≤ |x|^{n+1}/(1-|x|)` (valid under
its standing hypothesis `|x| < 1`), read as a two-sided rational bound on
`log y` for `y = 1 - x`.  The partial sum is bracketed rather than
evaluated, so each instance costs two `norm_num` evaluations of a
`Finset.range` sum and nothing else. -/
theorem log_enclose {y B E Slo Shi lo hi : ℝ} {n : ℕ}
    (hxB : |1 - y| ≤ B) (hB : B < 1)
    (hslo : Slo ≤ ∑ i ∈ Finset.range n, (1 - y) ^ (i + 1) / (i + 1))
    (hshi : (∑ i ∈ Finset.range n, (1 - y) ^ (i + 1) / (i + 1)) ≤ Shi)
    (hE : B ^ (n + 1) / (1 - B) ≤ E)
    (hlo : lo ≤ -Shi - E) (hhi : -Slo + E ≤ hi) :
    lo ≤ Real.log y ∧ Real.log y ≤ hi := by
  have hx1 : |1 - y| < 1 := lt_of_le_of_lt hxB hB
  have h := Real.abs_log_sub_add_sum_range_le hx1 n
  rw [show (1 : ℝ) - (1 - y) = y by ring] at h
  have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) hxB
  have hmono : |1 - y| ^ (n + 1) / (1 - |1 - y|) ≤ B ^ (n + 1) / (1 - B) :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hxB _)
      (by linarith) (by linarith)
  have hEE : |(∑ i ∈ Finset.range n, (1 - y) ^ (i + 1) / (i + 1)) + Real.log y| ≤ E :=
    le_trans h (le_trans hmono hE)
  rw [abs_le] at hEE
  exact ⟨by linarith [hEE.1], by linarith [hEE.2]⟩

/-- Range reduction upwards: `log (2^k · z)`. -/
theorem log_shift_mul {y z lo hi ZLO ZHI L2lo L2hi : ℝ} {k : ℕ}
    (hy : y = 2 ^ k * z) (hz : 0 < z)
    (hzlo : ZLO ≤ Real.log z) (hzhi : Real.log z ≤ ZHI)
    (h2lo : L2lo ≤ Real.log 2) (h2hi : Real.log 2 ≤ L2hi)
    (hlo : lo ≤ (k : ℝ) * L2lo + ZLO) (hhi : (k : ℝ) * L2hi + ZHI ≤ hi) :
    lo ≤ Real.log y ∧ Real.log y ≤ hi := by
  have hk : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  rw [hy, Real.log_mul hk (ne_of_gt hz), Real.log_pow]
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  constructor
  · nlinarith
  · nlinarith

/-- Range reduction downwards: `log (z / 2^k)`. -/
theorem log_shift_div {y z lo hi ZLO ZHI L2lo L2hi : ℝ} {k : ℕ}
    (hy : y = z / 2 ^ k) (hz : 0 < z)
    (hzlo : ZLO ≤ Real.log z) (hzhi : Real.log z ≤ ZHI)
    (h2lo : L2lo ≤ Real.log 2) (h2hi : Real.log 2 ≤ L2hi)
    (hlo : lo ≤ ZLO - (k : ℝ) * L2hi) (hhi : ZHI - (k : ℝ) * L2lo ≤ hi) :
    lo ≤ Real.log y ∧ Real.log y ≤ hi := by
  have hk : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  rw [hy, Real.log_div (ne_of_gt hz) hk, Real.log_pow]
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  constructor
  · nlinarith
  · nlinarith

/-- Rational enclosure of `Real.exp` of a rational, from Mathlib's
`Real.exp_bound` (standing hypothesis `|x| ≤ 1`).  Used only at the very
end, to turn the enclosure of `κ*` into a decimal for `c`. -/
theorem exp_enclose {x B Slo Shi E lo hi : ℝ} {n : ℕ}
    (hxB : |x| ≤ B) (hB : B ≤ 1) (hn : 0 < n)
    (hslo : Slo ≤ ∑ m ∈ Finset.range n, x ^ m / (Nat.factorial m))
    (hshi : (∑ m ∈ Finset.range n, x ^ m / (Nat.factorial m)) ≤ Shi)
    (hE : B ^ n * ((Nat.succ n : ℝ) / ((Nat.factorial n : ℝ) * n)) ≤ E)
    (hlo : lo ≤ Slo - E) (hhi : Shi + E ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have h := Real.exp_bound (le_trans hxB hB) hn
  have hmono : |x| ^ n * ((Nat.succ n : ℝ) / ((Nat.factorial n : ℝ) * n))
      ≤ B ^ n * ((Nat.succ n : ℝ) / ((Nat.factorial n : ℝ) * n)) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hxB _) (by positivity)
  have h2 : |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / (Nat.factorial m)| ≤ E :=
    le_trans h (le_trans hmono hE)
  rw [abs_le] at h2
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-! ## 2. The Gibbs bound and its convexity -/

/-- The binary entropy, in nats. -/
noncomputable def Hf (θ : ℝ) : ℝ := -(θ * Real.log θ) - (1 - θ) * Real.log (1 - θ)

/-- **The Gibbs upper bound for `V`, at a fixed weight `θ`.**  An
explicit function of `ρ` — the slope `q` has been eliminated. -/
noncomputable def Lam (θ ρ : ℝ) : ℝ :=
  (θ * Real.log ρ + (1 - θ) * Real.log (1 + ρ)) / Hf θ - Real.log ρ / Real.log 2

theorem Hf_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) : 0 < Hf θ := by
  have hlt : Real.log θ < 0 := Real.log_neg h0 h1
  have hlt' : Real.log (1 - θ) < 0 := Real.log_neg (by linarith) (by linarith)
  have k1 : 0 < -(θ * Real.log θ) := by nlinarith
  have k2 : 0 < -((1 - θ) * Real.log (1 - θ)) := by nlinarith
  unfold Hf; linarith

/-- Weighted AM–GM, in the exponential form used twice below.
`Real.geom_mean_le_arith_mean2_weighted` carries the standing hypotheses
`0 ≤ w₁`, `0 ≤ w₂`, `0 ≤ p₁`, `0 ≤ p₂`, `w₁ + w₂ = 1`. -/
theorem gm2 {u v lam : ℝ} (hu : 0 < u) (hv : 0 < v) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Real.exp (lam * Real.log u + (1 - lam) * Real.log v) ≤ lam * u + (1 - lam) * v := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := lam) (w₂ := 1 - lam)
    (p₁ := u) (p₂ := v) h0 (by linarith) hu.le hv.le (by ring)
  rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hv, ← Real.exp_add] at h
  rw [show lam * Real.log u + (1 - lam) * Real.log v
      = Real.log u * lam + Real.log v * (1 - lam) by ring]
  exact h

/-- **`V(q) ≤ Λ(θ, ρ)` at every supersolution, for every weight.**
`ρ^{-q} + (1+ρ)^{-q} ≤ 1` is Kraft's inequality for the two "codeword
lengths" `log ρ` and `log (1+ρ)`; AM–GM against the weights `(θ, 1-θ)`
turns it into `H(θ) ≤ q·(θ log ρ + (1-θ) log (1+ρ))`. -/
theorem V_le_Lam {q ρ θ : ℝ} (hq : 0 < q) (hρ : 1 ≤ ρ) (h0 : 0 < θ) (h1 : θ < 1)
    (hG : G q ρ ≤ 1) :
    1 / q - Real.log ρ / Real.log 2 ≤ Lam θ ρ := by
  have hG' : ρ ^ (-q) + (1 + ρ) ^ (-q) ≤ 1 := hG
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hρ1 : (0 : ℝ) < 1 + ρ := by linarith
  set l₁ := Real.log ρ with hl₁
  set l₂ := Real.log (1 + ρ) with hl₂
  have hl₁0 : 0 ≤ l₁ := Real.log_nonneg hρ
  have hl₂0 : 0 < l₂ := Real.log_pos (by linarith)
  set N := θ * l₁ + (1 - θ) * l₂ with hN
  have hN0 : 0 < N := by
    have a1 : 0 < (1 - θ) * l₂ := by positivity
    have a2 : 0 ≤ θ * l₁ := by positivity
    simp only [hN]; linarith
  have hHf := Hf_pos h0 h1
  have e₁ : ρ ^ (-q) = Real.exp (-q * l₁) := by
    rw [Real.rpow_def_of_pos hρ0, ← hl₁]; ring_nf
  have e₂ : (1 + ρ) ^ (-q) = Real.exp (-q * l₂) := by
    rw [Real.rpow_def_of_pos hρ1, ← hl₂]; ring_nf
  rw [e₁, e₂] at hG'
  have hu : (0 : ℝ) < Real.exp (-q * l₁) / θ := by positivity
  have hv : (0 : ℝ) < Real.exp (-q * l₂) / (1 - θ) := by positivity
  have hAM := gm2 hu hv h0.le (by linarith)
  have hlu : Real.log (Real.exp (-q * l₁) / θ) = -q * l₁ - Real.log θ := by
    rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt h0), Real.log_exp]
  have hlv : Real.log (Real.exp (-q * l₂) / (1 - θ)) = -q * l₂ - Real.log (1 - θ) := by
    rw [Real.log_div (Real.exp_ne_zero _) (by linarith), Real.log_exp]
  rw [hlu, hlv] at hAM
  have hthne : (1 : ℝ) - θ ≠ 0 := ne_of_gt (by linarith)
  have hrhs : θ * (Real.exp (-q * l₁) / θ) + (1 - θ) * (Real.exp (-q * l₂) / (1 - θ))
      = Real.exp (-q * l₁) + Real.exp (-q * l₂) := by field_simp
  rw [hrhs] at hAM
  have harg : θ * (-q * l₁ - Real.log θ) + (1 - θ) * (-q * l₂ - Real.log (1 - θ))
      = -q * N + Hf θ := by simp only [hN, Hf]; ring
  rw [harg] at hAM
  have hone : Real.exp (-q * N + Hf θ) ≤ 1 := le_trans hAM hG'
  rw [Real.exp_le_one_iff] at hone
  have hfin : 1 / q ≤ N / Hf θ := by
    rw [div_le_div_iff₀ hq hHf]; linarith
  unfold Lam
  simp only [← hl₁, ← hl₂, ← hN]
  linarith

/-- `1 + ρ₁^λ ρ₂^{1-λ} ≤ (1+ρ₁)^λ (1+ρ₂)^{1-λ}` — superadditivity of the
geometric mean, in logarithmic form.  This is the convexity of
`t ↦ log (1 + e^t)`, proved from two AM–GMs instead of a second
derivative. -/
theorem log_one_add_convex {ρ₁ ρ₂ lam : ℝ} (h1 : 0 < ρ₁) (h2 : 0 < ρ₂)
    (h0 : 0 ≤ lam) (h1' : lam ≤ 1) :
    Real.log (1 + Real.exp (lam * Real.log ρ₁ + (1 - lam) * Real.log ρ₂))
      ≤ lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂) := by
  set L := lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂) with hL
  have hp1 : (0 : ℝ) < 1 + ρ₁ := by linarith
  have hp2 : (0 : ℝ) < 1 + ρ₂ := by linarith
  have ha := gm2 (u := 1 / (1 + ρ₁)) (v := 1 / (1 + ρ₂)) (by positivity) (by positivity) h0 h1'
  have hla : Real.log (1 / (1 + ρ₁)) = -Real.log (1 + ρ₁) := by rw [one_div, Real.log_inv]
  have hlb : Real.log (1 / (1 + ρ₂)) = -Real.log (1 + ρ₂) := by rw [one_div, Real.log_inv]
  rw [hla, hlb, show lam * -Real.log (1 + ρ₁) + (1 - lam) * -Real.log (1 + ρ₂) = -L by
    rw [hL]; ring] at ha
  set M := lam * Real.log ρ₁ + (1 - lam) * Real.log ρ₂ with hM
  have hb := gm2 (u := ρ₁ / (1 + ρ₁)) (v := ρ₂ / (1 + ρ₂)) (by positivity) (by positivity) h0 h1'
  have hlc : Real.log (ρ₁ / (1 + ρ₁)) = Real.log ρ₁ - Real.log (1 + ρ₁) :=
    Real.log_div (ne_of_gt h1) (ne_of_gt hp1)
  have hld : Real.log (ρ₂ / (1 + ρ₂)) = Real.log ρ₂ - Real.log (1 + ρ₂) :=
    Real.log_div (ne_of_gt h2) (ne_of_gt hp2)
  rw [hlc, hld, show lam * (Real.log ρ₁ - Real.log (1 + ρ₁))
      + (1 - lam) * (Real.log ρ₂ - Real.log (1 + ρ₂)) = M - L by rw [hM, hL]; ring] at hb
  have hsum : lam * (1 / (1 + ρ₁)) + (1 - lam) * (1 / (1 + ρ₂))
      + (lam * (ρ₁ / (1 + ρ₁)) + (1 - lam) * (ρ₂ / (1 + ρ₂))) = 1 := by
    field_simp; ring
  have hkey : Real.exp (-L) + Real.exp (M - L) ≤ 1 := by linarith
  have hexp : Real.exp (-L) + Real.exp (M - L) = (1 + Real.exp M) / Real.exp L := by
    rw [Real.exp_sub, Real.exp_neg]; field_simp
  rw [hexp, div_le_one (Real.exp_pos _)] at hkey
  calc Real.log (1 + Real.exp M) ≤ Real.log (Real.exp L) := Real.log_le_log (by positivity) hkey
    _ = L := Real.log_exp L

/-- **The endpoint reduction.**  `Λ(θ, ·)` is convex in `log ρ`, so on
`[ρ₁, ρ₂]` it never exceeds its larger endpoint value.  This is what makes
a finite grid a proof. -/
theorem Lam_le_max {θ ρ ρ₁ ρ₂ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (hr1 : 0 < ρ₁) (ha : ρ₁ ≤ ρ) (hb : ρ ≤ ρ₂) :
    Lam θ ρ ≤ max (Lam θ ρ₁) (Lam θ ρ₂) := by
  have hr : (0 : ℝ) < ρ := lt_of_lt_of_le hr1 ha
  have hr2 : (0 : ℝ) < ρ₂ := lt_of_lt_of_le hr hb
  have hHf := Hf_pos h0 h1
  rcases eq_or_lt_of_le (le_trans ha hb) with heq | hlt
  · have : ρ = ρ₁ := le_antisymm (by linarith [heq ▸ hb]) ha
    subst this
    exact le_max_left _ _
  · have hlog : Real.log ρ₁ < Real.log ρ₂ := Real.log_lt_log hr1 hlt
    set lam := (Real.log ρ₂ - Real.log ρ) / (Real.log ρ₂ - Real.log ρ₁) with hlam
    have hd : 0 < Real.log ρ₂ - Real.log ρ₁ := by linarith
    have hla : Real.log ρ₁ ≤ Real.log ρ := Real.log_le_log hr1 ha
    have hlb : Real.log ρ ≤ Real.log ρ₂ := Real.log_le_log hr hb
    have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
    have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hd]; linarith
    have hmix : lam * Real.log ρ₁ + (1 - lam) * Real.log ρ₂ = Real.log ρ := by
      rw [hlam]; field_simp; ring
    have hrho : Real.exp (lam * Real.log ρ₁ + (1 - lam) * Real.log ρ₂) = ρ := by
      rw [hmix, Real.exp_log hr]
    have hconv := log_one_add_convex hr1 hr2 hlam0 hlam1
    rw [hrho] at hconv
    have hHfne : Hf θ ≠ 0 := ne_of_gt hHf
    have hL2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    have hdiff : lam * Lam θ ρ₁ + (1 - lam) * Lam θ ρ₂ - Lam θ ρ
        = (1 - θ) * ((lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂))
            - Real.log (1 + ρ)) / Hf θ := by
      unfold Lam
      rw [← hmix]
      field_simp
      ring
    have hcomb : Lam θ ρ ≤ lam * Lam θ ρ₁ + (1 - lam) * Lam θ ρ₂ := by
      have hnn : 0 ≤ (1 - θ) * ((lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂))
          - Real.log (1 + ρ)) / Hf θ := by
        apply div_nonneg _ hHf.le
        have hd2 : 0 ≤ (lam * Real.log (1 + ρ₁) + (1 - lam) * Real.log (1 + ρ₂))
            - Real.log (1 + ρ) := by linarith
        nlinarith
      linarith [hdiff, hnn]
    calc Lam θ ρ ≤ lam * Lam θ ρ₁ + (1 - lam) * Lam θ ρ₂ := hcomb
      _ ≤ lam * max (Lam θ ρ₁) (Lam θ ρ₂) + (1 - lam) * max (Lam θ ρ₁) (Lam θ ρ₂) := by
          have m1 := le_max_left (Lam θ ρ₁) (Lam θ ρ₂)
          have m2 := le_max_right (Lam θ ρ₁) (Lam θ ρ₂)
          nlinarith
      _ = max (Lam θ ρ₁) (Lam θ ρ₂) := by ring

/-- **One endpoint check**, reduced to rational arithmetic.  Every
hypothesis but the last three comes from the log table; the last three are
`norm_num` on rationals. -/
theorem Lam_le_of_bounds {θ ρ K l1lo l1hi l2hi tu su L2hi : ℝ}
    (h0 : 0 < θ) (h1 : θ < 1) (hρ : 1 ≤ ρ)
    (hl1lo : l1lo ≤ Real.log ρ) (hl1hi : Real.log ρ ≤ l1hi)
    (hl2hi : Real.log (1 + ρ) ≤ l2hi)
    (htu : Real.log θ ≤ tu) (hsu : Real.log (1 - θ) ≤ su)
    (hL2hi : Real.log 2 ≤ L2hi)
    (hHlo : 0 < -(θ * tu) - (1 - θ) * su)
    (hNnn : 0 ≤ θ * l1hi + (1 - θ) * l2hi)
    (hfin : (θ * l1hi + (1 - θ) * l2hi) / (-(θ * tu) - (1 - θ) * su) - l1lo / L2hi ≤ K) :
    Lam θ ρ ≤ K := by
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogρ : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have p1 : θ * Real.log θ ≤ θ * tu := mul_le_mul_of_nonneg_left htu h0.le
  have p2 : (1 - θ) * Real.log (1 - θ) ≤ (1 - θ) * su :=
    mul_le_mul_of_nonneg_left hsu (by linarith)
  have hHge : -(θ * tu) - (1 - θ) * su ≤ Hf θ := by unfold Hf; linarith
  have p3 : θ * Real.log ρ ≤ θ * l1hi := mul_le_mul_of_nonneg_left hl1hi h0.le
  have p4 : (1 - θ) * Real.log (1 + ρ) ≤ (1 - θ) * l2hi :=
    mul_le_mul_of_nonneg_left hl2hi (by linarith)
  have hstep1 : (θ * Real.log ρ + (1 - θ) * Real.log (1 + ρ)) / Hf θ
      ≤ (θ * l1hi + (1 - θ) * l2hi) / (-(θ * tu) - (1 - θ) * su) :=
    div_le_div₀ hNnn (by linarith) hHlo hHge
  have hstep2 : l1lo / L2hi ≤ Real.log ρ / Real.log 2 :=
    div_le_div₀ hlogρ hl1lo hL2pos hL2hi
  unfold Lam
  linarith

/-! ## 3. The `θ = 1/2` tail -/

theorem Hf_half : Hf (1 / 2) = Real.log 2 := by
  unfold Hf
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  ring

/-- `Λ(1/2, ρ) = ½·log₂(1 + 1/ρ)`, which decreases in `ρ`. -/
theorem Lam_half_le {ρ R u L2lo K : ℝ} (hR : 0 < R) (hρ : R ≤ ρ)
    (hu : Real.log (1 + 1 / R) ≤ u) (h2lo : L2lo ≤ Real.log 2) (h2pos : 0 < L2lo)
    (hu0 : 0 ≤ u) (hfin : u / (2 * L2lo) ≤ K) :
    Lam (1 / 2) ρ ≤ K := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le hR hρ
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hval : Lam (1 / 2) ρ = (Real.log (1 + ρ) - Real.log ρ) / (2 * Real.log 2) := by
    unfold Lam
    rw [Hf_half]
    field_simp
    ring
  have hid : Real.log (1 + ρ) - Real.log ρ = Real.log (1 + 1 / ρ) := by
    rw [show (1 : ℝ) + 1 / ρ = (1 + ρ) / ρ by field_simp; ring,
      Real.log_div (by linarith) (ne_of_gt hρ0)]
  have hmono : Real.log (1 + 1 / ρ) ≤ Real.log (1 + 1 / R) := by
    apply Real.log_le_log (by positivity)
    have : 1 / ρ ≤ 1 / R := by
      apply one_div_le_one_div_of_le hR hρ
    linarith
  have hnum : Real.log (1 + ρ) - Real.log ρ ≤ u := by rw [hid]; linarith
  have hstep : (Real.log (1 + ρ) - Real.log ρ) / (2 * Real.log 2) ≤ u / (2 * L2lo) :=
    div_le_div₀ hu0 hnum (by linarith) (by linarith)
  rw [hval]
  linarith

/-! ## 4. The two ends of the enclosure -/

/-- The upper end proved here — numerically `Final.KHI`. -/
noncomputable def KHI' : ℝ := 3317423792563106 / 10000000000000000

/-- The lower end proved here — numerically `Final.KLO`. -/
noncomputable def KLO' : ℝ := 3317423792563105 / 10000000000000000

theorem KHI'_eq : KHI' = Final.KHI := by unfold KHI' Final.KHI; norm_num

theorem KLO'_eq : KLO' = Final.KLO := by unfold KLO' Final.KLO; norm_num

/-- Every root exceeds `1`: `G q 1 = 1 + 2^{-q} > 1` and `G q ·` is
strictly decreasing. -/
theorem root_gt_one' {q ρ : ℝ} (hq : 0 < q) (hρ : 0 < ρ) (hg : G q ρ = 1) : 1 < ρ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-q) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : G q 1 = 1 + (2 : ℝ) ^ (-q) := by
    unfold G
    rw [Real.one_rpow, show (1 : ℝ) + 1 = 2 by norm_num]
  rcases lt_trichotomy ρ 1 with hlt | heq | hgt
  · have := G_strictAntiOn hq (Set.mem_Ioi.mpr hρ) (Set.mem_Ioi.mpr one_pos) hlt
    rw [hg, h1] at this; linarith
  · rw [heq, h1] at hg; linarith
  · exact hgt
"""


TABLE = []        # list of dicts, in emission order
BYEXPR = {}       # lean expression -> entry


def num(x: F) -> str:
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator} / {x.denominator}"


def add_entry(expr: str, y: F, need_lo: bool, need_hi: bool):
    """register `Real.log expr` (expr must evaluate to y) in the table"""
    if expr in BYEXPR:
        e = BYEXPR[expr]
        e['need_lo'] |= need_lo
        e['need_hi'] |= need_hi
        return e
    if y == 1:
        e = dict(kind='one', expr=expr, y=y, lo=F(0), hi=F(0),
                 need_lo=need_lo, need_hi=need_hi)
    else:
        k = 0
        z = y
        while abs(1 - z / 2) < abs(1 - z):
            z /= 2
            k += 1
        while abs(1 - z * 2) < abs(1 - z):
            z *= 2
            k -= 1
        c = series_cert(z, EPS)
        if k == 0:
            e = dict(kind='series', expr=expr, y=y, cert=c,
                     lo=rdown(c.lo, RND), hi=rup(c.hi, RND),
                     need_lo=need_lo, need_hi=need_hi)
        else:
            zexpr = num(z)
            ze = add_entry(zexpr, z, True, True)
            l2 = ent2()
            if k > 0:
                lo = k * l2['lo'] + ze['lo']
                hi = k * l2['hi'] + ze['hi']
            else:
                lo = ze['lo'] - (-k) * l2['hi']
                hi = ze['hi'] - (-k) * l2['lo']
            e = dict(kind='shift', expr=expr, y=y, k=k, zexpr=zexpr,
                     lo=rdown(lo, RND), hi=rup(hi, RND),
                     need_lo=need_lo, need_hi=need_hi)
    e['name'] = f"lgv{len(TABLE)}"
    TABLE.append(e)
    BYEXPR[expr] = e
    return e


ENT2 = None


def ent2():
    """the entry for log 2 (always present, emitted first)"""
    global ENT2
    if ENT2 is None:
        c = series_cert(F(1, 2), F(1, 10 ** 25))
        ENT2 = dict(kind='log2', expr='2', y=F(2), cert=c,
                    lo=rdown(-c.hi, RND), hi=rup(-c.lo, RND),
                    need_lo=True, need_hi=True, name='lgtwo')
        TABLE.append(ENT2)
        BYEXPR['2'] = ENT2
    return ENT2


def emit_entry(e) -> str:
    nm, lo, hi = e['name'], num(e['lo']), num(e['hi'])
    stmt = (f"theorem {nm} : ({lo} : ℝ) ≤ Real.log ({e['expr']})"
            f" ∧ Real.log ({e['expr']}) ≤ ({hi} : ℝ)")
    if e['kind'] == 'one':
        return f"{stmt} := by\n  simp\n"
    if e['kind'] == 'log2':
        c = e['cert']
        d = c.data
        return (f"{stmt} := by\n"
                f"  have h := log_enclose (y := (1 / 2 : ℝ)) (B := {num(d['B'])})"
                f" (n := {d['n']})\n"
                f"    (Slo := {num(d['Slo'])})\n"
                f"    (Shi := {num(d['Shi'])})\n"
                f"    (E := {num(d['E'])}) (lo := {num(rdown(c.lo, RND))})"
                f" (hi := {num(rup(c.hi, RND))})\n"
                f"    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)\n"
                f"    (by norm_num [Finset.sum_range_succ])"
                f" (by norm_num [Finset.sum_range_succ])\n"
                f"    (by norm_num) (by norm_num) (by norm_num)\n"
                f"  rw [show ((1 : ℝ) / 2) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h\n"
                f"  exact ⟨by linarith [h.2], by linarith [h.1]⟩\n")
    if e['kind'] == 'series':
        c = e['cert']
        d = c.data
        return (f"{stmt} :=\n"
                f"  log_enclose (y := ({e['expr']} : ℝ)) (B := {num(d['B'])})"
                f" (n := {d['n']})\n"
                f"    (Slo := {num(d['Slo'])})\n"
                f"    (Shi := {num(d['Shi'])})\n"
                f"    (E := {num(d['E'])})\n"
                f"    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)\n"
                f"    (by norm_num [Finset.sum_range_succ])"
                f" (by norm_num [Finset.sum_range_succ])\n"
                f"    (by norm_num) (by norm_num) (by norm_num)\n")
    # shift
    ze = BYEXPR[e['zexpr']]
    k = e['k']
    lem = 'log_shift_mul' if k > 0 else 'log_shift_div'
    kk = k if k > 0 else -k
    return (f"{stmt} :=\n"
            f"  {lem} (k := {kk}) (z := ({e['zexpr']} : ℝ))\n"
            f"    (by norm_num) (by norm_num) {ze['name']}.1 {ze['name']}.2"
            f" lgtwo.1 lgtwo.2\n"
            f"    (by norm_num) (by norm_num)\n")


# ------------------------------------------------------------ the pieces

def check_value(th: F, rho: F, rexpr: str, texpr: str):
    """register the table entries and return the exact bound value"""
    e1 = add_entry(rexpr, rho, True, True)
    e2 = add_entry(f"1 + {rexpr}", 1 + rho, False, True)
    e3 = add_entry(texpr, th, False, True)
    e4 = add_entry(f"1 - {texpr}", 1 - th, False, True)
    l2 = ent2()
    hlo = -(th * e3['hi']) - (1 - th) * e4['hi']
    Nhi = th * e1['hi'] + (1 - th) * e2['hi']
    val = Nhi / hlo - e1['lo'] / l2['hi']
    return val, e1, e2, e3, e4



def build_grid():
    KDES = F(33174237925631059, 10 ** 17)
    pts, ths = greedy(ftod(KDES), D('1.8'))
    rp = [F(1)]
    for j in range(1, len(pts)):
        if j == len(pts) - 1:
            rp.append(F(18, 10))
            continue
        w = pts[j] - pts[j - 1]
        d = max(4, int(-w.log10()) + 5)
        rp.append(rup(F(str(pts[j])), d))
    assert all(rp[i] < rp[i + 1] for i in range(len(rp) - 1))
    rth = []
    for j in range(len(rp) - 1):
        a, b = ftod(rp[j]), ftod(rp[j + 1])
        t = thstar((a * b).sqrt())
        for d in range(6, 26):
            tr = rup(F(str(t)), d)
            if 0 < tr < 1 and pairval(ftod(tr), logsD(a), logsD(b)) <= ftod(KHI) - D('1e-19'):
                break
        rth.append(tr)
    n = len(rth)

    ent2()                                   # log 2 first
    checks = []
    for j in range(n):
        texpr = num(rth[j])
        for side in (0, 1):
            rho = rp[j + side]
            rexpr = num(rho)
            val, e1, e2, e3, e4 = check_value(rth[j], rho, rexpr, texpr)
            assert val <= KHI, f'endpoint check failed at j={j} side={side}'
            checks.append(dict(j=j, side=side, th=rth[j], rho=rho,
                               texpr=texpr, rexpr=rexpr, val=val,
                               e1=e1, e2=e2, e3=e3, e4=e4))
    # tail: log (1 + 1/(9/5)) = log (14/9)
    etail = add_entry("1 + 1 / (9 / 5)", F(14, 9), False, True)
    l2 = ent2()
    tailval = etail['hi'] / (2 * l2['lo'])
    assert tailval <= KHI, f'tail fails: {float(tailval)}'
    return rp, rth, checks, etail, tailval



def main():
    rp, rth, checks, etail, tailval = build_grid()
    n = len(rth)

    # ---------------------------------------------------------- lower bound
    a = rup(F(str(THSTAR)), 12)
    ea = add_entry(num(a), a, True, True)
    eb = add_entry(f"1 - {num(a)}", 1 - a, True, True)
    l2 = ent2()
    TBAR = rup(eb['lo'] / ea['hi'], 32)
    assert TBAR * ea['hi'] <= eb['lo'], 'tbar check'
    assert eb['hi'] <= 3 * ea['lo'], 'tW >= 3 check'
    rho = rho_of_t((1 - ftod(a)).ln() / ftod(a).ln())
    B = rdown(F(str(rho)), 20)
    eB = add_entry(num(B), B, True, True)
    eB1 = add_entry(f"1 + {num(B)}", 1 + B, True, True)
    assert TBAR * eB['hi'] <= eB1['lo'], 'sign check'
    CLO = rdown(F(-1, 1) / ea['lo'] - F(1, 1) / l2['lo'], 32)
    assert CLO <= -F(1) / ea['lo'] - F(1) / l2['lo']
    Vlo = eB['lo'] * CLO
    assert Vlo >= KLO, f'lower bound fails: {float(Vlo)}'

    P = []
    add = P.append
    add(PREAMBLE.rstrip('\n'))

    # ------------------------------------------------------------ log table
    add("\n/-! ## 5. The table of logarithms\n\n"
        f"{len(TABLE)} rational enclosures, each `Real.log` of a rational to about\n"
        "`10^-22`.  Every one is a single application of `log_enclose` (plus a\n"
        "range reduction by a power of two where the argument is far from `1`);\n"
        "the series lengths run from "
        f"{min(e['cert'].data['n'] for e in TABLE if 'cert' in e)} to "
        f"{max(e['cert'].data['n'] for e in TABLE if 'cert' in e)} terms. -/\n")
    for e in TABLE:
        add(emit_entry(e))

    # -------------------------------------------------------- endpoint checks
    add("\n/-! ## 6. The endpoint checks -/\n")
    for c in checks:
        nm = f"chk{c['j']}{'a' if c['side'] == 0 else 'b'}"
        add(f"theorem {nm} : Lam ({c['texpr']}) ({c['rexpr']}) ≤ KHI' :=\n"
            f"  Lam_le_of_bounds (by norm_num) (by norm_num) (by norm_num)\n"
            f"    {c['e1']['name']}.1 {c['e1']['name']}.2 {c['e2']['name']}.2"
            f" {c['e3']['name']}.2 {c['e4']['name']}.2 lgtwo.2\n"
            f"    (by norm_num) (by norm_num) (by norm_num [KHI'])\n")

    # ------------------------------------------------------------- covering
    add("\n/-! ## 7. The covering -/\n")
    for j in range(n):
        add(f"theorem cover{j} {{ρ : ℝ}} (h1 : ({num(rp[j])} : ℝ) ≤ ρ)"
            f" (h2 : ρ ≤ ({num(rp[j + 1])} : ℝ)) :\n"
            f"    Lam ({num(rth[j])}) ρ ≤ KHI' :=\n"
            f"  le_trans (Lam_le_max (by norm_num) (by norm_num) (by norm_num) h1 h2)\n"
            f"    (max_le chk{j}a chk{j}b)\n")
    add(f"theorem coverTail {{ρ : ℝ}} (h : ((9 : ℝ) / 5) ≤ ρ) : Lam (1 / 2) ρ ≤ KHI' :=\n"
        f"  Lam_half_le (by norm_num) h {etail['name']}.2 lgtwo.1 (by norm_num)\n"
        f"    (by norm_num) (by norm_num [KHI'])\n")

    # ---------------------------------------------------------- upper bound
    add("\n/-! ## 8. The upper bound -/\n")
    body = ["theorem V_le_KHI' {q ρ : ℝ} (hq : 0 < q) (hρ : 1 ≤ ρ) (hG : G q ρ ≤ 1) :",
            "    1 / q - Real.log ρ / Real.log 2 ≤ KHI' := by"]
    for j in range(n):
        lo = "hρ" if j == 0 else f"h{j}"
        body.append(f"  rcases lt_or_ge ρ ({num(rp[j + 1])} : ℝ) with h{j + 1} | h{j + 1}")
        body.append(f"  · exact le_trans (V_le_Lam hq hρ (θ := {num(rth[j])})"
                    f" (by norm_num) (by norm_num) hG) (cover{j} {lo} h{j + 1}.le)")
    body.append(f"  exact le_trans (V_le_Lam hq hρ (θ := 1 / 2)"
                f" (by norm_num) (by norm_num) hG) (coverTail h{n})")
    add("\n".join(body) + "\n")
    add("""
/-- **`κ* ≤ 0.3317423792563106`, in Lean.** -/
theorem kappaStar_le_hi : kappaStar ≤ KHI' := by
  refine csSup_le Vset_nonempty ?_
  rintro x ⟨q, ρ, hq, hρ, hg, rfl⟩
  exact V_le_KHI' hq hρ (le_of_eq hg)

/-- **The hypothesis `Final.c_le_of_rocq` carried from `rocq/KappaStar.v`,
now a theorem.** -/
theorem kappaUpperBound_KHI : Final.KappaUpperBound Final.KHI := by
  intro q ρ hq hρ hg
  have h1 : 1 < ρ := root_gt_one' hq hρ hg
  have h := V_le_KHI' hq h1.le (le_of_eq hg)
  rw [KHI'_eq] at h
  exact h
""")

    # ---------------------------------------------------------- lower bound
    add(f"""
/-! ## 9. The lower bound

Fix the Gibbs weight `a` and let `t = log (1-a) / log a`.  The root of
`ρ^t = 1 + ρ` gives an *exact* point of the root curve at
`q = -log a / log ρ`, where `V = log ρ · (-1/log a - 1/log 2)`. -/

/-- The witness Gibbs weight `a ≈ ρ_c(q*)^{{-q*}}`. -/
noncomputable def aW : ℝ := {num(a)}

/-- `t = log (1-a) / log a`; the exponent of `ρ^t = 1 + ρ`. -/
noncomputable def tW : ℝ := Real.log (1 - aW) / Real.log aW

/-- The rational lower bound for the root. -/
noncomputable def BW : ℝ := {num(B)}

theorem aW_pos : 0 < aW := by unfold aW; norm_num

theorem aW_lt_one : aW < 1 := by unfold aW; norm_num

theorem log_aW : ({num(ea['lo'])} : ℝ) ≤ Real.log aW ∧ Real.log aW ≤ ({num(ea['hi'])} : ℝ) := by
  unfold aW; exact {ea['name']}

theorem log_one_sub_aW :
    ({num(eb['lo'])} : ℝ) ≤ Real.log (1 - aW) ∧
      Real.log (1 - aW) ≤ ({num(eb['hi'])} : ℝ) := by
  unfold aW; exact {eb['name']}

theorem log_BW : ({num(eB['lo'])} : ℝ) ≤ Real.log BW ∧ Real.log BW ≤ ({num(eB['hi'])} : ℝ) := by
  unfold BW; exact {eB['name']}

theorem log_one_add_BW :
    ({num(eB1['lo'])} : ℝ) ≤ Real.log (1 + BW) ∧
      Real.log (1 + BW) ≤ ({num(eB1['hi'])} : ℝ) := by
  unfold BW; exact {eB1['name']}

theorem log_aW_neg : Real.log aW < 0 := lt_of_le_of_lt log_aW.2 (by norm_num)

theorem tW_ge_three : 3 ≤ tW := by
  rw [tW, le_div_iff_of_neg log_aW_neg]
  linarith [log_aW.1, log_one_sub_aW.2]

theorem tW_gt_one : 1 < tW := lt_of_lt_of_le (by norm_num) tW_ge_three

theorem tW_le : tW ≤ ({num(TBAR)} : ℝ) := by
  rw [tW, div_le_iff_of_neg log_aW_neg]
  nlinarith [log_aW.2, log_one_sub_aW.1]

theorem tW_mul : tW * Real.log aW = Real.log (1 - aW) := by
  have hne : Real.log aW ≠ 0 := ne_of_lt log_aW_neg
  rw [tW]
  field_simp

/-- `ρ^t = 1 + ρ` has a root above `1`: the function
`x ↦ t log x - log (1+x)` is `-log 2` at `1` and positive at `4`. -/
theorem exists_root_t : ∃ ρ : ℝ, 1 < ρ ∧ tW * Real.log ρ = Real.log (1 + ρ) := by
  have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcont : ContinuousOn (fun x : ℝ => tW * Real.log x - Real.log (1 + x))
      (Set.Icc 1 4) := by
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := hx.1
    refine ContinuousAt.continuousWithinAt ?_
    have e1 : ContinuousAt (fun y : ℝ => Real.log y) x :=
      Real.continuousAt_log (by intro h; rw [h] at hx1; linarith)
    have ea : ContinuousAt (fun y : ℝ => 1 + y) x := continuousAt_const.add continuousAt_id
    have e2 : ContinuousAt (fun y : ℝ => Real.log (1 + y)) x :=
      ea.log (by show (1 : ℝ) + x ≠ 0; intro h; linarith)
    exact (continuousAt_const.mul e1).sub e2
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 5 ≤ 3 * Real.log 2 := by
    have : Real.log 5 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    rwa [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow, show ((3 : ℕ) : ℝ) = 3 by
      norm_num] at this
  have hf1 : tW * Real.log 1 - Real.log (1 + 1) = -Real.log 2 := by
    rw [Real.log_one, show (1 : ℝ) + 1 = 2 by norm_num]; ring
  have hf4 : 0 ≤ tW * Real.log 4 - Real.log (1 + 4) := by
    rw [show (1 : ℝ) + 4 = 5 by norm_num, h4]
    nlinarith [tW_ge_three, h5, hL2]
  have hmem : (0 : ℝ) ∈ Set.Icc (tW * Real.log 1 - Real.log (1 + 1))
      (tW * Real.log 4 - Real.log (1 + 4)) := by
    constructor
    · rw [hf1]; linarith
    · exact hf4
  obtain ⟨ρ, hρmem, hρ⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 4) hcont hmem
  have hne : ρ ≠ 1 := by
    intro h
    rw [h] at hρ
    simp only at hρ
    rw [hf1] at hρ
    linarith
  have hρ' : tW * Real.log ρ - Real.log (1 + ρ) = 0 := hρ
  exact ⟨ρ, lt_of_le_of_ne hρmem.1 (Ne.symm hne), by linarith⟩

/-- `x ↦ t log x - log (1+x)` is strictly increasing for `t > 1`, with no
derivative in sight: `log (1+y) - log (1+x) ≤ log y - log x` for `x ≤ y`. -/
theorem le_root {{B ρ : ℝ}} (hB : 1 < B) (hρ : 1 < ρ)
    (hroot : tW * Real.log ρ = Real.log (1 + ρ))
    (hsign : tW * Real.log B ≤ Real.log (1 + B)) : B ≤ ρ := by
  rcases lt_or_ge ρ B with hc | hok
  swap
  · exact hok
  exfalso
  have hB0 : (0 : ℝ) < B := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hd : Real.log ρ < Real.log B := Real.log_lt_log hρ0 hc
  have hstep : Real.log (1 + B) - Real.log (1 + ρ) ≤ Real.log B - Real.log ρ := by
    rw [← Real.log_div (by linarith) (by linarith), ← Real.log_div (by linarith) (by linarith)]
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by linarith) hρ0]
    nlinarith
  have hkey : (tW - 1) * (Real.log B - Real.log ρ) ≤ 0 := by linarith
  nlinarith [tW_gt_one, hd]

/-- **`0.3317423792563105 ≤ κ*`, in Lean.** -/
theorem kappaStar_ge_lo : KLO' ≤ kappaStar := by
  obtain ⟨ρ, hρ1, hroot⟩ := exists_root_t
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ1
  have hloga := log_aW_neg
  have hane : Real.log aW ≠ 0 := ne_of_lt hloga
  have hL2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set q : ℝ := -Real.log aW / Real.log ρ with hqdef
  have hq : 0 < q := by rw [hqdef]; exact div_pos (by linarith) hlogρ
  have hqlog : Real.log ρ * (-q) = Real.log aW := by rw [hqdef]; field_simp
  have hqlog2 : Real.log (1 + ρ) * (-q) = Real.log (1 - aW) := by
    rw [← hroot, ← tW_mul, hqdef]; field_simp
  have hG : G q ρ = 1 := by
    unfold G
    rw [Real.rpow_def_of_pos hρ0, Real.rpow_def_of_pos (by linarith), hqlog, hqlog2,
      Real.exp_log aW_pos, Real.exp_log (by unfold aW; norm_num)]
    ring
  have hV := V_le_kappaStar hq (le_of_lt hρ1) hG
  have hVal : 1 / q - Real.log ρ / Real.log 2
      = Real.log ρ * (-1 / Real.log aW - 1 / Real.log 2) := by
    rw [hqdef]; field_simp
  -- the root is at least `BW`
  have hBW1 : (1 : ℝ) < BW := by unfold BW; norm_num
  have hsign : tW * Real.log BW ≤ Real.log (1 + BW) := by
    have h1 : (0 : ℝ) ≤ Real.log BW := by linarith [log_BW.1]
    nlinarith [tW_le, log_BW.2, log_one_add_BW.1]
  have hBle : BW ≤ ρ := le_root hBW1 hρ1 hroot hsign
  have hlogB : ({num(eB['lo'])} : ℝ) ≤ Real.log ρ :=
    le_trans log_BW.1 (Real.log_le_log (by unfold BW; norm_num) hBle)
  -- the coefficient
  have hc1 : (1 : ℝ) / (-({num(ea['lo'])} : ℝ)) ≤ 1 / (-Real.log aW) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [log_aW.1])
  have hc2 : (1 : ℝ) / Real.log 2 ≤ 1 / ({num(l2['lo'])} : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [lgtwo.1])
  have he1 : -1 / Real.log aW = 1 / (-Real.log aW) := by field_simp
  have hcoef : ({num(CLO)} : ℝ) ≤ -1 / Real.log aW - 1 / Real.log 2 := by
    rw [he1]
    have : (1 : ℝ) / (-({num(ea['lo'])} : ℝ)) - 1 / ({num(l2['lo'])} : ℝ) ≥ ({num(CLO)} : ℝ) := by
      norm_num
    linarith
  have hprod : ({num(eB['lo'])} : ℝ) * ({num(CLO)} : ℝ)
      ≤ Real.log ρ * (-1 / Real.log aW - 1 / Real.log 2) :=
    mul_le_mul hlogB hcoef (by norm_num) (by linarith)
  have hfin : KLO' ≤ ({num(eB['lo'])} : ℝ) * ({num(CLO)} : ℝ) := by norm_num [KLO']
  rw [hVal] at hV
  linarith

/-- **The attainment hypothesis carried from `rocq/KappaStar.v`, now a
theorem.** -/
theorem kappaAttained_KLO : Final.KappaAttained Final.KLO := by
  have h := kappaStar_ge_lo
  rw [KLO'_eq] at h
  obtain ⟨q, ρ, hq, hρ, hg, hx⟩ := KappaAttainment.kappaStar_mem_Vset
  exact ⟨q, ρ, hq, hρ, hg, by rw [← hx]; exact h⟩

/-! ## 10. The enclosure, and the value of `c` -/

/-- **`κ*` to sixteen places, with no carried hypothesis.** -/
theorem kappaStar_enclosure : KLO' ≤ kappaStar ∧ kappaStar ≤ KHI' :=
  ⟨kappaStar_ge_lo, kappaStar_le_hi⟩

/-- **`2^{{1+KLO}} ≤ c ≤ 2^{{1+KHI}}` — `Final.c_bracket_of_rocq` with both
hypotheses discharged.** -/
theorem c_bracket_unconditional :
    (2 : ℝ) ^ (1 + Final.KLO) ≤ RevPebbling.BlockSim.c ∧
      RevPebbling.BlockSim.c ≤ (2 : ℝ) ^ (1 + Final.KHI) :=
  Final.c_bracket_of_rocq kappaUpperBound_KHI kappaAttained_KLO
""")

    # ---- the decimal value of c: two exponentials -----------------------
    XLO = rdown((1 + KLO) * l2['lo'], 34)
    XHI = rup((1 + KHI) * l2['hi'], 34)
    ea_, eb_ = exp_cert(XLO), exp_cert(XHI)
    CLO = F(2517064836893816, 10 ** 15)
    CHI = F(2517064836893817, 10 ** 15)
    # render these two unreduced: they are the headline decimals, and
    # `Fraction` would print 2517064836893816/10^15 as 314633104611727/1.25e14
    CLOs = "2517064836893816 / 1000000000000000"
    CHIs = "2517064836893817 / 1000000000000000"
    assert ea_['lo'] >= CLO, 'decimal lower end'
    assert eb_['hi'] <= CHI, 'decimal upper end'
    assert XLO <= (1 + KLO) * l2['lo'] and (1 + KHI) * l2['hi'] <= XHI

    def emit_exp(name, x, c):
        return (f"theorem {name} : ({num(c['lo'])} : ℝ) ≤ Real.exp ({num(x)}) ∧\n"
                f"    Real.exp ({num(x)}) ≤ ({num(c['hi'])} : ℝ) :=\n"
                f"  exp_enclose (x := ({num(x)} : ℝ)) (B := {num(c['B'])})"
                f" (n := {c['n']})\n"
                f"    (Slo := {num(c['Slo'])})\n"
                f"    (Shi := {num(c['Shi'])})\n"
                f"    (E := {num(c['E'])})\n"
                f"    (by rw [abs_le]; constructor <;> norm_num) (by norm_num)"
                f" (by norm_num)\n"
                f"    (by norm_num [Finset.sum_range_succ, Nat.factorial])\n"
                f"    (by norm_num [Finset.sum_range_succ, Nat.factorial])\n"
                f"    (by norm_num [Nat.factorial]) (by norm_num) (by norm_num)\n")

    add("\n/-! ## 11. The decimal value of `c`\n\n"
        "`c = 2^(1+κ*) = exp (log 2 · (1+κ*))`, and the enclosure of `κ*`\n"
        "bounds the exponent between two rationals; two applications of\n"
        "`exp_enclose` then name `c` to sixteen digits.  This is the step\n"
        "`rocq/KappaStar.v`'s `c_bracket_of_kappa` did with `interval`. -/\n")
    add(emit_exp('expXlo', XLO, ea_))
    add(emit_exp('expXhi', XHI, eb_))
    add(f"""/-- **`c = 2.517064836893816…`, in Lean.** -/
theorem c_decimal_bracket :
    ({CLOs} : ℝ) ≤ RevPebbling.BlockSim.c ∧
      RevPebbling.BlockSim.c ≤ ({CHIs} : ℝ) := by
  obtain ⟨hlo, hhi⟩ := kappaStar_enclosure
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hks : (0 : ℝ) ≤ kappaStar := by
    have h := hlo
    rw [KLO'] at h
    linarith
  have hxlo : ({num(XLO)} : ℝ) ≤ Real.log 2 * (1 + kappaStar) := by
    have h1 : ({num(l2['lo'])} : ℝ) * (1 + KLO') ≤ Real.log 2 * (1 + kappaStar) :=
      mul_le_mul lgtwo.1 (by linarith) (by rw [KLO']; norm_num) hL2pos.le
    rw [KLO'] at h1
    norm_num at h1 ⊢
    linarith
  have hxhi : Real.log 2 * (1 + kappaStar) ≤ ({num(XHI)} : ℝ) := by
    have h1 : Real.log 2 * (1 + kappaStar) ≤ ({num(l2['hi'])} : ℝ) * (1 + KHI') :=
      mul_le_mul lgtwo.2 (by linarith) (by linarith) (by norm_num)
    rw [KHI'] at h1
    norm_num at h1 ⊢
    linarith
  have hc : RevPebbling.BlockSim.c = Real.exp (Real.log 2 * (1 + kappaStar)) := by
    rw [Final.c_eq_two_rpow_kappaStar, Real.rpow_def_of_pos (by norm_num)]
  refine ⟨?_, ?_⟩
  · calc ({CLOs} : ℝ) ≤ ({num(ea_['lo'])} : ℝ) := by norm_num
      _ ≤ Real.exp ({num(XLO)}) := expXlo.1
      _ ≤ Real.exp (Real.log 2 * (1 + kappaStar)) := Real.exp_le_exp.mpr hxlo
      _ = RevPebbling.BlockSim.c := hc.symm
  · calc RevPebbling.BlockSim.c = Real.exp (Real.log 2 * (1 + kappaStar)) := hc
      _ ≤ Real.exp ({num(XHI)}) := Real.exp_le_exp.mpr hxhi
      _ ≤ ({num(eb_['hi'])} : ℝ) := expXhi.2
      _ ≤ ({CHIs} : ℝ) := by norm_num

end RevPebbling.KappaEnclosure
""")

    txt = "\n".join(P)
    OUT.write_text(txt, encoding='utf-8')
    print('wrote', OUT, len(txt.splitlines()), 'lines')
    print('intervals', n, 'table', len(TABLE))
    print('lower bound margin :', float(Vlo - KLO))
    print('upper worst        :', float(max(c['val'] for c in checks)), 'vs', float(KHI))



if __name__ == '__main__':
    main()
