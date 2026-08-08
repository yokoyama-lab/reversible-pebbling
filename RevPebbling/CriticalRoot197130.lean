import RevPebbling.CriticalRoot

/-!
# The critical root at `q = 197/130`, as a decimal (this work)

`CriticalRoot.c_ge_critical` says `2·2^{1/q}/ρ_c(q) ≤ c` for every real
`q > 0`, but its conclusion mentions `ρ_c(q)`, so it does not by itself
produce a number.  Getting a decimal out of it needs a rigorous
enclosure of `ρ_c(q)`, and that is what Lean cannot do in general: there
is no interval arithmetic here.

**Unless `q` is rational.**  Then every `rpow` in sight collapses into an
integer comparison, and the kernel does the rest:

* `A ≤ 2^{130/197}`   ⟸  `A^197 ≤ 2^130`
* `ρ_c ≤ B`           ⟸  `G q B ≤ 1`  (since `G q ·` is strictly
  decreasing and `G q ρ_c = 1`), and each summand of `G q B` is bounded
  by a rational through `x^{197/130} ≤ s ⟸ x^197 ≤ s^130`.

So the whole passage from the general real theorem to a quoted decimal
is four integer inequalities, settled by `decide`.

## What this changes

`Dispersion197130Growth.c_ge_2_5170648368936010208` reaches the same
constant, but by a different and much more expensive route: it builds a
bespoke rational instance of the dispersion induction and checks a
master inequality of about **5·10⁵ digits**.  Here the same constant
(very slightly sharper — the rational family loses `10⁻¹⁸` rounding
`λ₀`) comes out of `c_ge_critical` with certificates of at most **8826
digits**, and the mathematical content sits in the real theorem rather
than in the instance.

The reason `q` may be pinned is that `197/130` is a convergent of `q*`;
the deficit `2^{1+κ*} − 2^{1+V(q)}` falls like `(q − q*)²`, so this is
the sharpest exponent whose constants fit (see `DispersionBound197130`).
Taking `sup_q` — which is what `κ*` is — is a different problem: the
expression is tangent to its bound at `q*`, so it genuinely needs
interval arithmetic with Taylor models, and that stays in the Rocq layer
(`rocq/KappaStar.v`).
-/

namespace RevPebbling.CriticalRoot197130

open RevPebbling.CriticalRoot RevPebbling.GrowthRate Real

/-! ## Two conversions between `rpow` and integer powers -/

/-- `x^m ≤ s^n` gives `x^{m/n} ≤ s`. -/
theorem rpow_div_le {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) {m n : ℕ} (hn : n ≠ 0)
    (h : x ^ m ≤ s ^ n) : x ^ ((m : ℝ) / (n : ℝ)) ≤ s := by
  have h1 : ((x ^ m : ℝ)) ^ ((n : ℝ)⁻¹) ≤ s :=
    rpow_inv_le_of_le_pow (by positivity) hs hn h
  have h2 : (x : ℝ) ^ ((m : ℝ) / (n : ℝ)) = ((x ^ m : ℝ)) ^ ((n : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast x m, ← Real.rpow_mul hx, div_eq_mul_inv]
  rw [h2]; exact h1

/-- `x^n ≤ s^m` gives `x ≤ s^{m/n}`. -/
theorem le_rpow_div {x s : ℝ} (hs : 0 ≤ s) {m n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ≤ s ^ m) : x ≤ s ^ ((m : ℝ) / (n : ℝ)) := by
  refine le_of_pow_le_pow_left₀ hn (by positivity) ?_
  have hid : (s ^ ((m : ℝ) / (n : ℝ))) ^ n = s ^ m := by
    rw [← Real.rpow_natCast (s ^ ((m : ℝ) / (n : ℝ))) n, ← Real.rpow_mul hs,
        div_mul_cancel₀ _ (by exact_mod_cast hn), Real.rpow_natCast]
  rw [hid]; exact h

/-- A root of `G q` is at most any point where `G q` has already dropped
to `1`, because `G q ·` is strictly decreasing. -/
theorem root_le_of_G_le {q ρ B : ℝ} (hq : 0 < q) (hρ : 0 < ρ) (hB : 0 < B)
    (hg : G q ρ = 1) (hGB : G q B ≤ 1) : ρ ≤ B := by
  by_contra hc
  have hlt : B < ρ := not_le.mp hc
  have := G_strictAntiOn hq (Set.mem_Ioi.mpr hB) (Set.mem_Ioi.mpr hρ) hlt
  linarith

/-! ## The witnesses -/

/-- `A = a/S` is a lower bound for `2^{130/197}`. -/
def a : ℕ := 15799714367946952477666817

/-- `B = u/S` is an upper bound for `ρ_c(197/130)`. -/
def u : ℕ := 12554078175789814208120195

def S : ℕ := 10000000000000000000000000

/-- `s₁/T` bounds `B^{-197/130}`, `s₂/T` bounds `(1+B)^{-197/130}`. -/
def s1 : ℕ := 708439862859994610710586195534

def s2 : ℕ := 291560137140005389289413795603

def T : ℕ := 1000000000000000000000000000000

/-! ## The four integer certificates

All four are `decide`, so kernel only; the largest compares two 8826-digit
integers. -/

theorem cert_A : a ^ 197 ≤ 2 ^ 130 * S ^ 197 := by decide

theorem cert_s1 : S ^ 197 * T ^ 130 ≤ s1 ^ 130 * u ^ 197 := by decide

theorem cert_s2 : S ^ 197 * T ^ 130 ≤ s2 ^ 130 * (S + u) ^ 197 := by decide

theorem cert_sum : s1 + s2 ≤ T := by decide

/-! ## From the certificates to the enclosure -/

/-- `2^{130/197} ≥ a/S`. -/
theorem two_rpow_ge : ((a : ℝ) / S) ≤ (2 : ℝ) ^ ((130 : ℝ) / (197 : ℝ)) := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  refine le_rpow_div (by norm_num) (by norm_num) ?_
  rw [div_pow, div_le_iff₀ (pow_pos hS 197)]
  have h : ((a : ℝ)) ^ 197 ≤ 2 ^ 130 * ((S : ℝ)) ^ 197 := by exact_mod_cast cert_A
  linarith

/-- `G (197/130) (u/S) ≤ 1`: the two summands are bounded by `s₁/T` and
`s₂/T`, whose sum is at most `1`. -/
theorem G_bound : G ((197 : ℝ) / 130) ((u : ℝ) / S) ≤ 1 := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hu : (0 : ℝ) < u := by norm_num [u]
  have hT : (0 : ℝ) < T := by norm_num [T]
  have hB : (0 : ℝ) < (u : ℝ) / S := by positivity
  -- the first summand
  have e1 : ((u : ℝ) / S) ^ (-((197 : ℝ) / 130)) = ((S : ℝ) / u) ^ ((197 : ℝ) / 130) := by
    rw [Real.rpow_neg (le_of_lt hB), ← Real.inv_rpow (le_of_lt hB), inv_div]
  have h1 : ((S : ℝ) / u) ^ ((197 : ℝ) / 130) ≤ (s1 : ℝ) / T := by
    refine rpow_div_le (by positivity) (by positivity) (by norm_num) ?_
    rw [div_pow, div_pow, div_le_div_iff₀ (pow_pos hu 197) (pow_pos hT 130)]
    exact_mod_cast cert_s1
  -- the second summand
  have hSu : (0 : ℝ) < 1 + (u : ℝ) / S := by positivity
  have e2 : (1 + (u : ℝ) / S) ^ (-((197 : ℝ) / 130))
      = ((S : ℝ) / (S + u)) ^ ((197 : ℝ) / 130) := by
    rw [Real.rpow_neg (le_of_lt hSu), ← Real.inv_rpow (le_of_lt hSu)]
    congr 1
    field_simp
  have h2 : ((S : ℝ) / (S + u)) ^ ((197 : ℝ) / 130) ≤ (s2 : ℝ) / T := by
    refine rpow_div_le (by positivity) (by positivity) (by norm_num) ?_
    rw [div_pow, div_pow, div_le_div_iff₀ (pow_pos (by positivity : (0:ℝ) < (S:ℝ) + u) 197)
      (pow_pos hT 130)]
    have h : ((S : ℝ)) ^ 197 * ((T : ℝ)) ^ 130
        ≤ ((s2 : ℝ)) ^ 130 * (((S : ℝ)) + u) ^ 197 := by exact_mod_cast cert_s2
    linarith
  -- and their sum
  have hsum : (s1 : ℝ) / T + (s2 : ℝ) / T ≤ 1 := by
    have hid : (s1 : ℝ) / T + (s2 : ℝ) / T = ((s1 : ℝ) + s2) / T := by ring
    rw [hid, div_le_one hT]
    exact_mod_cast cert_sum
  unfold G
  rw [e1, e2]
  linarith

/-- **`ρ_c(197/130) ≤ u/S`.** -/
theorem root_le {ρ : ℝ} (hρ : 1 ≤ ρ) (hg : G ((197 : ℝ) / 130) ρ = 1) :
    ρ ≤ (u : ℝ) / S := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hu : (0 : ℝ) < u := by norm_num [u]
  exact root_le_of_G_le (by norm_num) (by linarith) (div_pos hu hS) hg G_bound

/-! ## The bound -/

/-- **`2.5170648368936010217 ≤ c`.**

`c_ge_critical` at `q = 197/130`, with the root pinned between the two
integer certificates.  Kernel only; the largest `decide` compares two
8826-digit integers, against about `5·10⁵` digits for the same constant
in `Dispersion197130Growth`. -/
theorem c_ge_2_5170648368936010217 :
    (25170648368936010217 / 10000000000000000000 : ℝ) ≤ RevPebbling.BlockSim.c := by
  obtain ⟨ρ, hρ1, hg, hc⟩ := c_ge_critical (q := (197 : ℝ) / 130) (by norm_num)
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hu : (0 : ℝ) < u := by norm_num [u]
  -- `q⁻¹ = 130/197`
  have hinv : (((197 : ℝ) / 130)⁻¹) = (130 : ℝ) / (197 : ℝ) := by norm_num
  rw [hinv] at hc
  -- pin the root and the power
  have hB := root_le hρ1 hg
  have hA := two_rpow_ge
  have hBpos : (0 : ℝ) < (u : ℝ) / S := by positivity
  -- `2·(a/S)/(u/S) ≤ 2·2^{130/197}/ρ`
  have hstep : 2 * ((a : ℝ) / S) / ((u : ℝ) / S)
      ≤ 2 * (2 : ℝ) ^ ((130 : ℝ) / (197 : ℝ)) / ρ :=
    div_le_div₀ (by positivity) (by linarith) hρ0 hB
  refine le_trans ?_ (le_trans hstep hc)
  -- and the rational comparison `2a/u ≥ 2.5170648368936010217`
  have hid : 2 * ((a : ℝ) / S) / ((u : ℝ) / S) = 2 * (a : ℝ) / u := by
    field_simp
  rw [hid, le_div_iff₀ hu, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 10000000000000000000)]
  norm_num [a, u]

end RevPebbling.CriticalRoot197130
