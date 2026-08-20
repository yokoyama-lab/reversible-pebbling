import RevPebbling.ArcGeometry
import RevPebbling.MarginStep5
import RevPebbling.BracketPositive
import RevPebbling.Shape

/-!
# The arc: a lower bound on the idealised margin

This is the last analytic step of the upper bound.  `Shape.idealMargin`
is what the composition needs bounded below; every other file bounds
pieces of it.  Here they are put together for the arc `λ ≤ ζ < ζ_sc`,
where both levels sit on the climbing part of the profile.

The split is at the balance point `δ* = log₂(1+ρ)`, `ρ = 2^{1/q−λ}`
(`ArcGeometry`), which makes **both branches of the `min` carry the same
ideal exponent** `−q δ*`, so the idealised margin is exactly

```
F(q,λ) − 1 = 2^{qλ−1} + (1+ρ)^{−q} − 1.
```

The real profile deviates from its tangent by at most `m·s²/2` at offset
`s` (`RampProfile.Iof_tangent`), and the transfer `2^{X−E} ≥ 2^X(1 −
E ln 2)` (`MarginTransfer`) turns those deviations into a subtracted term
`ln 2 · (m/2) · v_A` with `v_A = 2^{qλ−1}λ² + (1+ρ)^{−q}δ*²`.  Step 5
(`MarginStep5`, derivative-free) bounds `F(q,λ) − 1` below by
`ρ_c^{−q}·q·ln 2·(λ − V q)`, and the design condition `m ≤ (q/10)(λ − V)`
— which the linear ramp satisfies because `m = (q_h/10)ε`, `q ≥ q_h` and
`λ − V ≥ ε` — makes both terms proportional to `λ − V`:

```
idealMargin ≥ ln 2 · q · (λ − V) · [ ρ_c^{−q} − v_A/20 ].
```

The bracket is positive with room to spare: `ρ_c^{−q} > 1/2` at a root
(`BracketPositive.half_lt_rpow`) while `v_A/20 ≤ 0.294`.
-/

namespace RevPebbling.ArcMargin

open Real RevPebbling.CriticalRoot RevPebbling.ArcGeometry

/-! ## The transfer, for three positions at once -/

/-- **The transfer.**  Perturbing the three exponents by `E_b, E_c, E_d`
costs at most `ln 2` times the weighted sum of the deviations.  (Both
signs are covered: `two_rpow_shift_ge` uses `|E|`.) -/
theorem margin_transfer_three (A B Eb Ec Ed : ℝ) :
    (2 : ℝ) ^ A + (2 : ℝ) ^ B - 1
      - Real.log 2 * ((2 : ℝ) ^ A * |Eb| + (2 : ℝ) ^ B * max |Ec| |Ed|)
    ≤ (2 : ℝ) ^ (A - Eb) + min ((2 : ℝ) ^ (B - Ec)) ((2 : ℝ) ^ (B - Ed)) - 1 := by
  have hsplit : ∀ X E : ℝ, (2 : ℝ) ^ (X - E) = (2 : ℝ) ^ X * (2 : ℝ) ^ (-E) := by
    intro X E
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), sub_eq_add_neg]
  have hb : (2 : ℝ) ^ A - (2 : ℝ) ^ A * Real.log 2 * |Eb| ≤ (2 : ℝ) ^ (A - Eb) := by
    rw [hsplit A Eb]
    exact RevPebbling.MarginTransfer.two_rpow_shift_ge
  have hc : (2 : ℝ) ^ B - (2 : ℝ) ^ B * Real.log 2 * |Ec| ≤ (2 : ℝ) ^ (B - Ec) := by
    rw [hsplit B Ec]
    exact RevPebbling.MarginTransfer.two_rpow_shift_ge
  have hd : (2 : ℝ) ^ B - (2 : ℝ) ^ B * Real.log 2 * |Ed| ≤ (2 : ℝ) ^ (B - Ed) := by
    rw [hsplit B Ed]
    exact RevPebbling.MarginTransfer.two_rpow_shift_ge
  have hBpos : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  have hmin : (2 : ℝ) ^ B - (2 : ℝ) ^ B * Real.log 2 * max |Ec| |Ed|
      ≤ min ((2 : ℝ) ^ (B - Ec)) ((2 : ℝ) ^ (B - Ed)) := by
    refine le_min ?_ ?_
    · have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ B * Real.log 2 := mul_nonneg (le_of_lt hBpos) hlog2
      have := mul_le_mul_of_nonneg_left (le_max_left |Ec| |Ed|) hnn
      linarith
    · have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ B * Real.log 2 := mul_nonneg (le_of_lt hBpos) hlog2
      have := mul_le_mul_of_nonneg_left (le_max_right |Ec| |Ed|) hnn
      linarith
  nlinarith [hb, hmin]

/-! ## The pure-power reference at the root -/

/-- At a root, `2^{1/q − V} = ρ_c` and `2^{qV−1} = ρ_c^{−q}`, so
`F(q, V) = G q ρ_c = 1`: the hypothesis of Step 5. -/
theorem F_at_V {q V ρc : ℝ} (hq : 0 < q) (hρc : 0 < ρc)
    (hV : V = 1 / q - Real.log ρc / Real.log 2) (hg : G q ρc = 1) :
    (2 : ℝ) ^ (q * V - 1) + (1 + (2 : ℝ) ^ (1 / q - V)) ^ (-q) = 1 := by
  have hlogρ : (2 : ℝ) ^ (Real.log ρc / Real.log 2) = ρc :=
    RevPebbling.MarginAnchors.two_rpow_log_div_log hρc
  have h1 : (1 : ℝ) / q - V = Real.log ρc / Real.log 2 := by rw [hV]; ring
  have h2 : q * V - 1 = -(q * (Real.log ρc / Real.log 2)) := by
    rw [hV]; field_simp; ring
  have h3 : (2 : ℝ) ^ (q * V - 1) = ρc ^ (-q) := by
    rw [h2, show -(q * (Real.log ρc / Real.log 2))
      = (Real.log ρc / Real.log 2) * (-q) by ring,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), hlogρ]
  rw [h1, h3, hlogρ]
  exact hg

/-! ## The arc bound -/

/-- The weight `v_A` of the deviation term. -/
noncomputable def vA (q lam : ℝ) : ℝ :=
  (2 : ℝ) ^ (q * lam - 1) * lam ^ 2
    + (1 + rhoLam q lam) ^ (-q) * deltaStar q lam ^ 2

/-- **The arc's margin bound.**  With the split at the balance point and
the design condition `m ≤ (q/10)(λ − V)`, the idealised margin is at
least `ln 2 · q · (λ − V) · [ρ_c^{−q} − v_A/20]`. -/
theorem arc_margin_ge {q lam m V ρc a b c d : ℝ}
    (hq : 0 < q) (hm : 0 ≤ m) (hV : V ≤ lam)
    (hρc : 1 ≤ ρc) (hg : G q ρc = 1)
    (hVdef : V = 1 / q - Real.log ρc / Real.log 2)
    (hab : |(a - b) - q * lam| ≤ m * lam ^ 2 / 2)
    (hac : |(a - c) - q * (lam - tStar q lam)| ≤ m * deltaStar q lam ^ 2 / 2)
    (had : |(a - d) + q * deltaStar q lam| ≤ m * deltaStar q lam ^ 2 / 2)
    (hdesign : m ≤ q / 10 * (lam - V)) :
    Real.log 2 * q * (lam - V) * (ρc ^ (-q) - vA q lam / 20)
      ≤ RevPebbling.Shape.idealMargin a b c d := by
  have hρc0 : (0 : ℝ) < ρc := lt_of_lt_of_le zero_lt_one hρc
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set δ := deltaStar q lam with hδ
  set A := q * lam - 1 with hA
  set B := -(q * δ) with hB
  -- the three perturbations
  set Eb := q * lam - (a - b) with hEb
  set Ec := q * (lam - tStar q lam) - (a - c) with hEc
  set Ed := -(q * δ) - (a - d) with hEd
  have habs_b : |Eb| ≤ m * lam ^ 2 / 2 := by
    rw [hEb, show q * lam - (a - b) = -((a - b) - q * lam) by ring, abs_neg]
    exact hab
  have habs_c : |Ec| ≤ m * δ ^ 2 / 2 := by
    rw [hEc, show q * (lam - tStar q lam) - (a - c)
      = -((a - c) - q * (lam - tStar q lam)) by ring, abs_neg]
    exact hac
  have habs_d : |Ed| ≤ m * δ ^ 2 / 2 := by
    rw [hEd, show -(q * δ) - (a - d) = -((a - d) + q * δ) by ring, abs_neg]
    exact had
  -- the ideal exponents: the `c` branch also sits at `−qδ`
  have hqlt : q * (lam - tStar q lam) = 1 - q * δ := by
    rw [lam_sub_t, hδ]
    field_simp
  have hexp_b : a - (b + 1) = A - Eb := by rw [hA, hEb]; ring
  have hexp_c : a - (c + 1) = B - Ec := by
    rw [hB, hEc, hqlt]; ring
  have hexp_d : a - d = B - Ed := by rw [hB, hEd]; ring
  -- transfer
  have htrans := margin_transfer_three A B Eb Ec Ed
  have hmargin : RevPebbling.Shape.idealMargin a b c d
      = (2 : ℝ) ^ (A - Eb) + min ((2 : ℝ) ^ (B - Ec)) ((2 : ℝ) ^ (B - Ed)) - 1 := by
    unfold RevPebbling.Shape.idealMargin
    rw [hexp_b, hexp_c, hexp_d]
  -- the ideal margin is `F − 1`
  have hBval : (2 : ℝ) ^ B = (1 + rhoLam q lam) ^ (-q) := by
    rw [hB, hδ]
    exact two_rpow_neg_q_delta q lam
  -- Step 5: `F(q,λ) − 1 ≥ ρ_c^{−q}·q·ln2·(λ−V)`
  have hone := F_at_V hq hρc0 hVdef hg
  have hstep5 := RevPebbling.MarginStep5.step5_of_F_eq_one hq hV hone
  have hVpow : (2 : ℝ) ^ (q * V - 1) = ρc ^ (-q) := by
    have hlogρ : (2 : ℝ) ^ (Real.log ρc / Real.log 2) = ρc :=
      RevPebbling.MarginAnchors.two_rpow_log_div_log hρc0
    have h2 : q * V - 1 = (Real.log ρc / Real.log 2) * (-q) := by
      rw [hVdef]; field_simp; ring
    rw [h2, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), hlogρ]
  have hrho' : (1 + (2 : ℝ) ^ (1 / q - lam)) ^ (-q) = (1 + rhoLam q lam) ^ (-q) := rfl
  have hF : ρc ^ (-q) * (q * (lam - V) * Real.log 2)
      ≤ (2 : ℝ) ^ A + (2 : ℝ) ^ B - 1 := by
    rw [hA, hBval, ← hrho', ← hVpow]
    linarith [hstep5]
  -- the deviation term, absorbed by the design condition
  have hApos : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have hBpos : (0 : ℝ) < (2 : ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) _
  have hmaxcd : max |Ec| |Ed| ≤ m * δ ^ 2 / 2 := max_le habs_c habs_d
  have hdev : (2 : ℝ) ^ A * |Eb| + (2 : ℝ) ^ B * max |Ec| |Ed|
      ≤ (m / 2) * vA q lam := by
    have h1 : (2 : ℝ) ^ A * |Eb| ≤ (2 : ℝ) ^ A * (m * lam ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left habs_b (le_of_lt hApos)
    have h2 : (2 : ℝ) ^ B * max |Ec| |Ed| ≤ (2 : ℝ) ^ B * (m * δ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hmaxcd (le_of_lt hBpos)
    unfold vA
    rw [← hBval, ← hδ, ← hA]
    linarith
  have hvA0 : 0 ≤ vA q lam := by
    unfold vA
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (q * lam - 1) * lam ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (1 + rhoLam q lam) ^ (-q) * deltaStar q lam ^ 2 := by
      have := one_add_rhoLam_pos (q := q) (lam := lam)
      positivity
    linarith
  have hmdev : (m / 2) * vA q lam ≤ (q / 20 * (lam - V)) * vA q lam := by
    have hcoef : m / 2 ≤ q / 20 * (lam - V) := by linarith
    exact mul_le_mul_of_nonneg_right hcoef hvA0
  -- combine
  rw [hmargin]
  have hchain : Real.log 2 * q * (lam - V) * (ρc ^ (-q) - vA q lam / 20)
      ≤ (2 : ℝ) ^ A + (2 : ℝ) ^ B - 1
        - Real.log 2 * ((2 : ℝ) ^ A * |Eb| + (2 : ℝ) ^ B * max |Ec| |Ed|) := by
    have hdev' : Real.log 2 * ((2 : ℝ) ^ A * |Eb| + (2 : ℝ) ^ B * max |Ec| |Ed|)
        ≤ Real.log 2 * ((q / 20 * (lam - V)) * vA q lam) :=
      mul_le_mul_of_nonneg_left (le_trans hdev hmdev) (le_of_lt hlog2)
    have hid : Real.log 2 * ((q / 20 * (lam - V)) * vA q lam)
        = Real.log 2 * q * (lam - V) * (vA q lam / 20) := by ring
    have hF' : Real.log 2 * q * (lam - V) * ρc ^ (-q)
        ≤ (2 : ℝ) ^ A + (2 : ℝ) ^ B - 1 := by
      have : ρc ^ (-q) * (q * (lam - V) * Real.log 2)
          = Real.log 2 * q * (lam - V) * ρc ^ (-q) := by ring
      linarith [hF, this]
    rw [hid] at hdev'
    have hexpand : Real.log 2 * q * (lam - V) * (ρc ^ (-q) - vA q lam / 20)
        = Real.log 2 * q * (lam - V) * ρc ^ (-q)
          - Real.log 2 * q * (lam - V) * (vA q lam / 20) := by ring
    linarith
  linarith [htrans, hchain]

/-! ## The bracket is positive -/

/-- **`v_A/20 < ρ_c^{−q}`** — the bracket of `arc_margin_ge` is positive.

`ρ_c^{−q} > 1/2` at a root (`BracketPositive.half_lt_rpow`), while
`v_A ≤ (8/5)(51/100)² + 1·(49/9) = 5.86`, so `v_A/20 ≤ 0.294`.  Unlike
`BracketPositive.bracket_pos` this needs no bound on the second summand
beyond `(1+ρ)^{−q} ≤ 1`, because the linear ramp makes the schedule
factor exactly `q/10` (no `γ̄`-to-`γ(q₀)` ratio to pay). -/
theorem bracket_pos_arc {q lam ρc : ℝ} (hq : 0 < q) (hqhi : q ≤ 16 / 5)
    (hlam0 : 33 / 100 ≤ lam) (hlam : lam ≤ 51 / 100)
    (hqlo : 43 / 100 ≤ q)
    (hρc : 1 ≤ ρc) (hg : G q ρc = 1) :
    0 < ρc ^ (-q) - vA q lam / 20 := by
  have hhalf : 1 / 2 < ρc ^ (-q) := RevPebbling.BracketPositive.half_lt_rpow hq hρc hg
  -- the exponential factor `2^{qλ−1} ≤ 8/5`
  have hql : q * lam ≤ 5 / 3 := by nlinarith
  have hfac : (2 : ℝ) ^ (q * lam - 1) ≤ 8 / 5 :=
    RevPebbling.BracketPositive.two_rpow_factor_le hql
  -- the second summand: `(1+ρ)^{−q} ≤ 1`
  have hρ1 : (1 : ℝ) ≤ 1 + rhoLam q lam := by
    have := rhoLam_pos (q := q) (lam := lam); linarith
  have hsec : (1 + rhoLam q lam) ^ (-q) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hρ1 (by linarith)
  have hsec0 : (0 : ℝ) < (1 + rhoLam q lam) ^ (-q) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hδ2 : deltaStar q lam ^ 2 ≤ 612 / 100 := delta_sq_le hqlo hlam0
  have hδ0 : 0 ≤ deltaStar q lam ^ 2 := sq_nonneg _
  have hfac0 : (0 : ℝ) < (2 : ℝ) ^ (q * lam - 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hbound : vA q lam ≤ 8 / 5 * (51 / 100) ^ 2 + 612 / 100 := by
    unfold vA
    have h1 : (2 : ℝ) ^ (q * lam - 1) * lam ^ 2 ≤ 8 / 5 * (51 / 100) ^ 2 := by
      nlinarith
    have h2 : (1 + rhoLam q lam) ^ (-q) * deltaStar q lam ^ 2 ≤ 612 / 100 := by
      nlinarith
    linarith
  have hnum : (8 / 5 * (51 / 100) ^ 2 + 612 / 100 : ℝ) / 20 < 1 / 2 := by norm_num
  linarith

end RevPebbling.ArcMargin
