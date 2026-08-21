import RevPebbling.Final

/-!
# `κ*` is attained: the supremum is a maximum

`Final.kappaStar` is `sup_q V(q)`, and `Final.c_eq_two_rpow_kappaStar`
needs nothing more.  The manuscript, however, writes `κ* = max_q V(q)`
with a maximiser `q* ≈ 1.515`; this file closes that gap.

The argument is the usual one:

* `ρ_c` is a **function** of `q` (the root is unique, `root_unique`), and
  it is continuous — not by an implicit-function theorem but by the
  order structure: `G q ·` is strictly decreasing, so a root at `ρ₀` is
  pinned between `ρ₀ ± ε` by two strict inequalities that persist under
  small changes of `q`;
* `V` therefore is continuous on `(0, ∞)`;
* `V` is small in both tails — `V(q) ≤ 3/10` for `q ≤ 1/2` and
  `V(q) ≤ 1/q ≤ 1/4` for `q ≥ 4` — while `V(3/2) ≥ 33/100`, so the
  supremum is the maximum over the compact `[1/2, 4]`.

The small-`q` tail is the only delicate piece.  The bound
`V(q) < (1/q)(1 − log₂(1 + 2^{−q}))` of `KappaLtHalf` tends to `1/2`, which
is **not** below `κ*`; one more Bernoulli step — `(1+ρ)^{−q} ≥ ρ^{−q}/(1+q/ρ)`
instead of `≥ (2ρ)^{−q}` — gives `ρ^q ≥ 2 − q/ρ` and hence
`V(q) ≤ 1/(ln 2·(2ρ − q))`, which is small because `ρ ≥ 2.89` there.
-/

namespace RevPebbling.KappaAttainment

open RevPebbling.CriticalRoot RevPebbling.Final Filter Topology

/-! ## The root as a function -/

/-- The critical root `ρ_c(q)`, as a function (`1` off the domain). -/
noncomputable def rhoc (q : ℝ) : ℝ :=
  if h : 0 < q then Classical.choose (exists_root h) else 1

theorem rhoc_spec {q : ℝ} (hq : 0 < q) : 1 ≤ rhoc q ∧ G q (rhoc q) = 1 := by
  unfold rhoc
  rw [dif_pos hq]
  exact Classical.choose_spec (exists_root hq)

theorem rhoc_pos {q : ℝ} (hq : 0 < q) : 0 < rhoc q :=
  lt_of_lt_of_le zero_lt_one (rhoc_spec hq).1

/-- Any root is *the* root. -/
theorem rhoc_eq {q ρ : ℝ} (hq : 0 < q) (hρ : 0 < ρ) (hg : G q ρ = 1) : rhoc q = ρ :=
  root_unique hq (rhoc_pos hq) hρ (rhoc_spec hq).2 hg

/-- `V(q) = 1/q − log₂ ρ_c(q)`. -/
noncomputable def Vf (q : ℝ) : ℝ := 1 / q - Real.log (rhoc q) / Real.log 2

theorem Vf_mem {q : ℝ} (hq : 0 < q) : Vf q ∈ Vset :=
  ⟨q, rhoc q, hq, (rhoc_spec hq).1, (rhoc_spec hq).2, rfl⟩

theorem mem_Vset_iff {x : ℝ} : x ∈ Vset ↔ ∃ q, 0 < q ∧ x = Vf q := by
  constructor
  · rintro ⟨q, ρ, hq, hρ, hg, rfl⟩
    refine ⟨q, hq, ?_⟩
    unfold Vf
    rw [rhoc_eq hq (lt_of_lt_of_le zero_lt_one hρ) hg]
  · rintro ⟨q, hq, rfl⟩
    exact Vf_mem hq

/-! ## The two tails -/

/-- `V(q) ≤ 1/q`: the root is at least `1`. -/
theorem Vf_le_inv {q : ℝ} (hq : 0 < q) : Vf q ≤ 1 / q := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (rhoc q) := Real.log_nonneg (rhoc_spec hq).1
  have : 0 ≤ Real.log (rhoc q) / Real.log 2 := div_nonneg hlog hL.le
  unfold Vf
  linarith

/-- **The small-`q` tail**: `V(q) ≤ 3/10` for `0 < q ≤ 1/2`. -/
theorem Vf_le_of_small {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 1 / 2) : Vf q ≤ 3 / 10 := by
  unfold Vf
  obtain ⟨hρ1, hg⟩ := rhoc_spec hq
  set ρ := rhoc q with hρdef
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL69 : (69 / 100 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h
    linarith
  -- (a) `ρ^q > 1 + 2^{−q} ≥ 17/10`, hence `ρ ≥ (17/10)^{1/q} ≥ (17/10)² = 2.89`
  have ha : 1 + (2 : ℝ) ^ (-q) < ρ ^ q := RevPebbling.KappaLtHalf.one_add_two_rpow_lt hq hρ1 hg
  have h7 : (7 / 10 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num)]
    have hs : (2 : ℝ) ^ ((1 : ℝ) / 2) ≤ 10 / 7 := by
      have h := RevPebbling.CriticalRootRat.rpow_div_le (x := (2 : ℝ)) (s := (10 : ℝ) / 7)
        (by norm_num) (by norm_num) (n := 2) (m := 1) (by norm_num) (by norm_num)
      simpa using h
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    rw [le_inv_comm₀ (by norm_num) hpos]
    linarith
  have h2q : (17 / 10 : ℝ) ≤ 1 + (2 : ℝ) ^ (-q) := by
    have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-q) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    linarith
  have hρq : (17 / 10 : ℝ) ≤ ρ ^ q := by linarith
  have hρbig : (289 / 100 : ℝ) ≤ ρ := by
    have h1 : ((17 / 10 : ℝ)) ^ q⁻¹ ≤ (ρ ^ q) ^ q⁻¹ :=
      Real.rpow_le_rpow (by norm_num) hρq (by positivity)
    have h2 : (ρ ^ q) ^ q⁻¹ = ρ := by
      rw [← Real.rpow_mul hρ0.le, mul_inv_cancel₀ hq.ne', Real.rpow_one]
    have h3 : ((17 / 10 : ℝ)) ^ (2 : ℝ) ≤ (17 / 10 : ℝ) ^ q⁻¹ := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      rw [le_inv_comm₀ (by norm_num) hq]
      have : ((2 : ℝ))⁻¹ = 1 / 2 := by norm_num
      rw [this]; exact hq2
    have h4 : ((17 / 10 : ℝ)) ^ (2 : ℝ) = 289 / 100 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h2] at h1
    linarith
  -- (b) Bernoulli: `(1+ρ)^{−q} = ρ^{−q}(1+1/ρ)^{−q} ≥ ρ^{−q}/(1 + q/ρ)`
  have hsplit : (1 + ρ) ^ (-q) = ρ ^ (-q) * (1 + 1 / ρ) ^ (-q) := by
    rw [← Real.mul_rpow hρ0.le (by positivity)]
    congr 1
    field_simp
    ring
  have hinvρ : (0 : ℝ) ≤ 1 / ρ := by positivity
  have hbern : (1 + 1 / ρ) ^ q ≤ 1 + q * (1 / ρ) :=
    rpow_one_add_le_one_add_mul_self (by linarith) hq.le (by linarith)
  have hbpos : (0 : ℝ) < (1 + 1 / ρ) ^ q := Real.rpow_pos_of_pos (by positivity) _
  have hx0 : (0 : ℝ) ≤ q / ρ := by positivity
  have hx1 : (0 : ℝ) < 1 + q / ρ := by linarith
  have hlow : 1 / (1 + q / ρ) ≤ (1 + 1 / ρ) ^ (-q) := by
    rw [Real.rpow_neg (by positivity), one_div, inv_le_inv₀ hx1 hbpos]
    have : q * (1 / ρ) = q / ρ := by ring
    linarith
  -- (c) the root equation then gives `ρ^q ≥ 2 − q/ρ`
  have hρnq : (0 : ℝ) < ρ ^ (-q) := Real.rpow_pos_of_pos hρ0 _
  have hG : ρ ^ (-q) + (1 + ρ) ^ (-q) = 1 := hg
  rw [hsplit] at hG
  have hkey : ρ ^ (-q) * (1 + 1 / (1 + q / ρ)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hlow hρnq.le
    have hexp : ρ ^ (-q) * (1 + 1 / (1 + q / ρ))
        = ρ ^ (-q) + ρ ^ (-q) * (1 / (1 + q / ρ)) := by ring
    linarith
  have hρqpos : (0 : ℝ) < ρ ^ q := Real.rpow_pos_of_pos hρ0 _
  have hρq2 : 2 - q / ρ ≤ ρ ^ q := by
    have h1 : 1 + 1 / (1 + q / ρ) ≤ ρ ^ q := by
      rw [Real.rpow_neg hρ0.le, inv_mul_le_iff₀ hρqpos] at hkey
      linarith
    have h2 : 1 - q / ρ ≤ 1 / (1 + q / ρ) := by
      rw [le_div_iff₀ hx1]
      nlinarith [sq_nonneg (q / ρ)]
    linarith
  -- (d) logarithms: `q·ln ρ ≥ ln 2 + ln(1 − q/(2ρ)) ≥ ln 2 − (10/9)·q/(2ρ)`
  have hxs : q / ρ ≤ 1 / 5 := by
    rw [div_le_iff₀ hρ0]; linarith
  have hpos2 : (0 : ℝ) < 2 - q / ρ := by linarith
  have hlog1 : Real.log (2 - q / ρ) ≤ q * Real.log ρ := by
    have := Real.log_le_log hpos2 hρq2
    rwa [Real.log_rpow hρ0] at this
  set y := q / (2 * ρ) with hy
  have hy0 : (0 : ℝ) ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 1 / 10 := by
    rw [hy, div_le_iff₀ (by positivity)]; nlinarith
  have hypos : (0 : ℝ) < 1 - y := by linarith
  have hlog2' : Real.log (2 - q / ρ) = Real.log 2 + Real.log (1 - y) := by
    rw [← Real.log_mul (by norm_num) hypos.ne']
    congr 1
    rw [hy]
    field_simp
  have hlog3 : 1 - (1 - y)⁻¹ ≤ Real.log (1 - y) := Real.one_sub_inv_le_log_of_pos hypos
  have hinv : (1 - y)⁻¹ ≤ 1 + (10 / 9) * y := by
    rw [inv_eq_one_div, div_le_iff₀ hypos]
    nlinarith [mul_nonneg hy0 (show (0 : ℝ) ≤ 1 / 10 - y by linarith)]
  have hlog4 : -(10 / 9) * y ≤ Real.log (1 - y) := by linarith
  -- (e) `(5/9)(q/ρ) ≤ (3/10)·q·ln 2` because `50 ≤ 27·ln 2·ρ`
  have hρL : (50 : ℝ) ≤ 27 * Real.log 2 * ρ := by nlinarith [hL69, hρbig]
  have h5 : 5 / (9 * ρ) ≤ 3 * Real.log 2 / 10 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hρL]
  have hq5 : q * (5 / (9 * ρ)) ≤ q * (3 * Real.log 2 / 10) :=
    mul_le_mul_of_nonneg_left h5 hq.le
  have hyq : (10 / 9) * y = q * (5 / (9 * ρ)) := by rw [hy]; field_simp; ring
  have hkeyL : Real.log 2 - q * Real.log ρ ≤ 3 / 10 * (q * Real.log 2) := by
    linarith [hlog1, hlog2', hlog4, hq5, hyq]
  -- (f) assemble
  rw [div_sub_div _ _ hq.ne' hL.ne', div_le_iff₀ (by positivity)]
  linarith

/-- `V(3/2) ≥ 33/100`, the anchor inside the compact window (the same
computation as `Final.kappaStar_ge`, at the root function). -/
theorem Vf_three_halves_ge : (33 / 100 : ℝ) ≤ Vf (3 / 2) := by
  have hq : (0 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨hρ1, hg⟩ := rhoc_spec hq
  set ρ := rhoc (3 / 2) with hρdef
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hle : ρ ≤ 6307 / 5000 := RevPebbling.KappaLowerRat.root_le_witness hρ0 hg
  have hpow : ρ ^ (300 : ℕ) ≤ (2 : ℝ) ^ (101 : ℕ) :=
    le_trans (pow_le_pow_left₀ hρ0.le hle 300) witness_pow_le
  have hrpow : ρ ≤ (2 : ℝ) ^ ((101 : ℝ) / 300) := by
    have h := RevPebbling.CriticalRootRat.le_rpow_div (x := ρ) (s := (2 : ℝ))
      (by norm_num) (n := 300) (m := 101) (by norm_num) hpow
    simpa using h
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log ρ / Real.log 2 ≤ 101 / 300 := by
    have h1 : Real.log ρ ≤ Real.log ((2 : ℝ) ^ ((101 : ℝ) / 300)) :=
      Real.log_le_log hρ0 hrpow
    rw [Real.log_rpow (by norm_num)] at h1
    rw [div_le_iff₀ hL]
    linarith
  unfold Vf
  rw [← hρdef]
  have : (1 : ℝ) / (3 / 2) = 2 / 3 := by norm_num
  rw [this]
  linarith

/-! ## Continuity of the root -/

/-- `G` is continuous in `q` at a fixed positive `ρ`. -/
theorem G_continuous_q {ρ : ℝ} (hρ : 0 < ρ) : Continuous (fun q : ℝ => G q ρ) := by
  unfold G
  exact (continuous_const.rpow continuous_neg (fun _ => Or.inl hρ.ne')).add
    (continuous_const.rpow continuous_neg (fun _ => Or.inl (by linarith)))

/-- **`ρ_c` is continuous on `(0, ∞)`.**  At `q₀` with root `ρ₀`, the two
strict inequalities `G q₀ (ρ₀−ε) > 1 > G q₀ (ρ₀+ε)` persist for `q` near
`q₀`; the intermediate value theorem then puts a root of `G q` inside
`(ρ₀−ε, ρ₀+ε)`, and by uniqueness that root is `ρ_c(q)`. -/
theorem rhoc_continuousAt {q₀ : ℝ} (hq₀ : 0 < q₀) : ContinuousAt rhoc q₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨hρ₀1, hg₀⟩ := rhoc_spec hq₀
  set ρ₀ := rhoc q₀ with hρ₀def
  have hρ₀ : (0 : ℝ) < ρ₀ := by linarith
  set e := min (ε / 2) (ρ₀ / 2) with he
  have he0 : 0 < e := lt_min (by positivity) (by positivity)
  have heε : e ≤ ε / 2 := min_le_left _ _
  have heρ : e ≤ ρ₀ / 2 := min_le_right _ _
  have hlo_pos : 0 < ρ₀ - e := by linarith
  -- the two strict inequalities at `q₀`
  have h1 : 1 < G q₀ (ρ₀ - e) := by
    have := (G_strictAntiOn hq₀) (show ρ₀ - e ∈ Set.Ioi (0 : ℝ) from hlo_pos)
      (show ρ₀ ∈ Set.Ioi (0 : ℝ) from hρ₀) (by linarith : ρ₀ - e < ρ₀)
    rw [hg₀] at this
    exact this
  have h2 : G q₀ (ρ₀ + e) < 1 := by
    have := (G_strictAntiOn hq₀) (show ρ₀ ∈ Set.Ioi (0 : ℝ) from hρ₀)
      (show ρ₀ + e ∈ Set.Ioi (0 : ℝ) from by simp only [Set.mem_Ioi]; linarith)
      (by linarith : ρ₀ < ρ₀ + e)
    rw [hg₀] at this
    exact this
  -- they persist near `q₀`, and so does `0 < q`
  have hc1 : ContinuousAt (fun q => G q (ρ₀ - e)) q₀ := (G_continuous_q hlo_pos).continuousAt
  have hc2 : ContinuousAt (fun q => G q (ρ₀ + e)) q₀ :=
    (G_continuous_q (by linarith : (0 : ℝ) < ρ₀ + e)).continuousAt
  have ev1 : ∀ᶠ q in 𝓝 q₀, 1 < G q (ρ₀ - e) := hc1.eventually (eventually_gt_nhds h1)
  have ev2 : ∀ᶠ q in 𝓝 q₀, G q (ρ₀ + e) < 1 := hc2.eventually (eventually_lt_nhds h2)
  have ev3 : ∀ᶠ q in 𝓝 q₀, (0 : ℝ) < q := eventually_gt_nhds hq₀
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ((ev1.and ev2).and ev3)
  refine ⟨δ, hδ, ?_⟩
  intro q hqδ
  obtain ⟨⟨hq1, hq2⟩, hq0⟩ := hball hqδ
  -- IVT for `G q` on `[ρ₀−e, ρ₀+e]`
  have hcont : ContinuousOn (G q) (Set.Icc (ρ₀ - e) (ρ₀ + e)) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by linarith [hr.1]
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_id.rpow_const (Or.inl (ne_of_gt hr0))).add
      ((continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (ne_of_gt (by linarith : (0 : ℝ) < 1 + r))))
  have hmem : (1 : ℝ) ∈ Set.Icc (G q (ρ₀ + e)) (G q (ρ₀ - e)) := ⟨hq2.le, hq1.le⟩
  obtain ⟨r, hr, hgr⟩ := intermediate_value_Icc' (by linarith) hcont hmem
  have hr0 : (0 : ℝ) < r := by linarith [hr.1]
  have hroot : rhoc q = r := rhoc_eq hq0 hr0 hgr
  rw [Real.dist_eq, hroot, abs_sub_lt_iff]
  constructor <;> linarith [hr.1, hr.2]

/-- `V` is continuous on `(0, ∞)`. -/
theorem Vf_continuousOn : ContinuousOn Vf (Set.Ioi 0) := by
  intro q hq
  have hq0 : (0 : ℝ) < q := hq
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun q : ℝ => 1 / q) q :=
    continuousAt_const.div continuousAt_id hq0.ne'
  have h2 : ContinuousAt (fun q : ℝ => Real.log (rhoc q)) q :=
    (rhoc_continuousAt hq0).log (rhoc_pos hq0).ne'
  exact h1.sub (h2.div_const _)

/-! ## Attainment -/

/-- **`κ*` is attained**: there is `q₁ > 0` with `V(q₁) = κ*`.  The tails
are below `V(3/2)`, so the supremum is the maximum over `[1/2, 4]`. -/
theorem exists_max : ∃ q₁ : ℝ, 0 < q₁ ∧ Vf q₁ = kappaStar := by
  have hK : IsCompact (Set.Icc (1 / 2 : ℝ) 4) := isCompact_Icc
  have hne : (Set.Icc (1 / 2 : ℝ) 4).Nonempty := ⟨1, by norm_num, by norm_num⟩
  have hsub : Set.Icc (1 / 2 : ℝ) 4 ⊆ Set.Ioi 0 := by
    intro x hx
    simp only [Set.mem_Ioi]
    linarith [hx.1]
  obtain ⟨q₁, hq₁, hmax⟩ := hK.exists_isMaxOn hne (Vf_continuousOn.mono hsub)
  have hmax' : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 4, Vf x ≤ Vf q₁ := isMaxOn_iff.mp hmax
  have hq₁0 : (0 : ℝ) < q₁ := by linarith [hq₁.1]
  refine ⟨q₁, hq₁0, le_antisymm (le_csSup Vset_bddAbove (Vf_mem hq₁0)) ?_⟩
  refine csSup_le Vset_nonempty ?_
  intro x hx
  obtain ⟨q, hq, rfl⟩ := mem_Vset_iff.mp hx
  have h32 : Vf (3 / 2) ≤ Vf q₁ := hmax' _ ⟨by norm_num, by norm_num⟩
  have hanchor : (33 / 100 : ℝ) ≤ Vf q₁ := le_trans Vf_three_halves_ge h32
  rcases lt_or_ge (1 / 2 : ℝ) q with hbig | hsmall
  · rcases lt_or_ge (4 : ℝ) q with h4 | h4
    · have : Vf q ≤ 1 / 4 := by
        refine le_trans (Vf_le_inv hq) ?_
        rw [div_le_div_iff₀ hq (by norm_num)]
        linarith
      linarith
    · exact hmax' q ⟨hbig.le, h4⟩
  · have := Vf_le_of_small hq hsmall
    linarith

/-- `κ*` is a member of the value set: the supremum is a **maximum**. -/
theorem kappaStar_mem_Vset : kappaStar ∈ Vset := by
  obtain ⟨q₁, hq₁, h⟩ := exists_max
  rw [← h]
  exact Vf_mem hq₁

theorem isGreatest_kappaStar : IsGreatest Vset kappaStar :=
  ⟨kappaStar_mem_Vset, fun _ hx => le_csSup Vset_bddAbove hx⟩

/-- **The attainment hypothesis, discharged** — the form `Final` carries
from Rocq, now a theorem at `κ = κ*`. -/
theorem kappaAttained_kappaStar : KappaAttained kappaStar := by
  obtain ⟨q₁, hq₁, h⟩ := exists_max
  obtain ⟨hρ1, hg⟩ := rhoc_spec hq₁
  exact ⟨q₁, rhoc q₁, hq₁, hρ1, hg, by rw [← h]; exact le_of_eq rfl⟩

/-- `c = 2^{1+V(q₁)}` at a maximiser `q₁`: the identity with an explicit
witness slope, as the manuscript states it. -/
theorem c_eq_at_maximiser :
    ∃ q₁ : ℝ, 0 < q₁ ∧ RevPebbling.BlockSim.c = (2 : ℝ) ^ (1 + Vf q₁) := by
  obtain ⟨q₁, hq₁, h⟩ := exists_max
  exact ⟨q₁, hq₁, by rw [h]; exact c_eq_two_rpow_kappaStar⟩

end RevPebbling.KappaAttainment
