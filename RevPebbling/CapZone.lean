import RevPebbling.ShapeMonotone
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The cap zone at level `S−1` (the `hcapzone` input of Lemma C-flat)

`RevPebbling.TieBand.cflat_step` closes the corner tie band, but it takes the
*cap-zone characterisation* as a hypothesis:

```
hcapzone : ∀ x : ℕ, F * 2^(-a) ≤ (x : ℝ) → 2 ^ n - 1 ≤ ΨS1 x
```

"at level `S−1`, everything at or above `F_{S−1} = F_S · 2^{−a}` already sits at the
cap `2^{S−2} − 1`".  That was residue **(i)** of §6.11 of the companion manuscript
(`notes/eps_theorem_draft.md`) — the last analytic input of Lemma C-flat left
undischarged.  This module discharges it.

## Why it is a theorem and not an analytic assumption

`m48_exact_replay.py` does not *assume* the cap zone, it *computes* with a subsolution
of the closed form

```
Ψ_S(v) = min (2^{S−1} − 1) ⌊2^{(S−1) + ŷ(log₂ v − corner_S)}⌋
```

(`m48_exact_replay.py:163-212, 239-281`; `capexp = S − 1`, `cap = 2^{S−1} − 1`, and the
knots of level `S` sit at `x = corner_S + dx` with `dx ≤ 0`).  The corner obeys
`corner_S = corner_anchor + a·(S − s_anchor)`, so `corner_{S−1} = corner_S − a` and
`F_{S−1} = 2^{corner_{S−1}} = F_S · 2^{−a}` exactly.  The shape is **flat at its top
knot**: `ŷ(0) = 0`, and `ŷ` is extended by that constant to the right.  Hence for
`log₂ v ≥ corner_{S−1}` the exponent is exactly `S − 2`, the floor is exactly `2^{S−2}`,
and the `min` returns the cap.  Nothing analytic is involved: it is the definition of
`Ψ` plus one finite fact about the knot list.

So the pattern is again that of `RevPebbling.XLift` and `RevPebbling.ShapeMonotone`:
**a checker whose soundness is an unconditional theorem, applied to data whose
provenance is external.**

* `Psi` is the model.  `Psi_eq_cap` is the soundness theorem: for *any* `ŷ` that
  vanishes on `[0, ∞)`, `Psi` returns the cap throughout the cap zone.
* `Psi_eq_cap_of_natLog` certifies the *integer* early return that `m48` actually
  executes (`if Fraction(bl - 1) >= lev.x_top: return lev.cap, lev.cap`, where
  `bl - 1 = ⌊log₂ v⌋ = Nat.log 2 v`): the test is sufficient, hence sound.
* `eval_flat_right` is the finite fact: a shape that passes `ShapeMonotone`'s `ok`
  check takes its **last** knot's ordinate everywhere to its right.  It is the mirror
  of `Shape.eval_head`, which supplied residue (ii) in §6.13.
* `cflat_step_capzone` is `TieBand.cflat_step` **with `hcapzone` removed**.

## What is and is not proved here

**Proved, unconditionally.**  `eval_flat_right` (soundness of the `ok` checker at the
right end), `Psi_eq_cap` and `Psi_eq_cap_of_natLog` (the cap zone for any flat-topped
`ŷ`), and `cflat_step_capzone` (Lemma C-flat with one hypothesis fewer).

**Not proved here: that a given `Shape` is `ŷ`, nor that `Psi` is `m48`'s `Ψ`.**  The
knot data is transcribed from the repaired anchors by
`scripts/probe_brw/m68_shape_monotone.py`; that the transcription is exact, that
`rel[0] = (0,0)` (the flat top), that the corner law holds in `m48`'s own `Family`, and
that `m48`'s real `PsiEval.psi` really does return the cap on the cap zone **and less
than the cap just below it**, are checked by `scripts/probe_brw/m69_cap_zone.py`.  Those
are replay-grade facts about particular files, deliberately kept outside Lean.

**Domain of agreement.**  The concrete `Shape`s of `ShapeMonotone` equal `ŷ` on
`[x_½, ∞)` only; below `x_½` their `eval` is the constant `−1` while `ŷ` keeps
descending.  Every use below evaluates the shape at `log₂ v − corner_{S−1} ≥ 0 > x_½`,
i.e. strictly inside the domain of agreement — which is the same place Lemma C-flat
evaluates it.  `Psi _ eps0035.eval _` is therefore a faithful model of `Ψ_{S−1}` on the
cap zone, and nowhere else; it is only ever used on the cap zone.
-/

namespace RevPebbling.CapZone

open RevPebbling.ShapeMonotone

/-! ## The last knot of a knot list

`lastK` is written with the same three-case recursion as `pieces`, so that the two
unfold in step and no `List.getLast?` bookkeeping is needed. -/

/-- The final knot of a knot list (`(0,0)` on the empty list, a value never used). -/
def lastK : List (ℤ × ℤ) → ℤ × ℤ
  | [] => (0, 0)
  | [p] => p
  | _ :: q :: rest => lastK (q :: rest)

theorem lastK_cons_cons (p q : ℤ × ℤ) (rest : List (ℤ × ℤ)) :
    lastK (p :: q :: rest) = lastK (q :: rest) := rfl

/-- Mirror of `ShapeMonotone.okList_head_le`: every knot of an `okList` list sits at or
to the left of the last one. -/
theorem okList_le_lastK : ∀ {ks : List (ℤ × ℤ)}, okList ks = true →
    ∀ r ∈ ks, r.1 ≤ (lastK ks).1
  | [], _, r, hr => by simp at hr
  | [p], _, r, hr => by
    simp only [List.mem_singleton] at hr
    simp [lastK, hr]
  | p :: q :: rest, h, r, hr => by
    obtain ⟨hlt, _, htail⟩ := okList_cons h
    rw [lastK_cons_cons]
    rcases List.mem_cons.1 hr with hr | hr
    · have hq : q.1 ≤ (lastK (q :: rest)).1 :=
        okList_le_lastK htail q (List.mem_cons_self ..)
      rw [hr]; omega
    · exact okList_le_lastK htail r hr

/-! ## The shape is flat to the right of its last knot -/

noncomputable section

/-- A ramp is fully risen at and beyond its head. -/
theorem piece_of_ge {m l u x : ℝ} (hlu : l ≤ u) (hx : u ≤ x) :
    piece m l u x = m * (u - l) := by
  have hmin : min u x = u := min_eq_left hx
  simp [piece, clamp', hmin, max_eq_right hlu]

/-- **The ramp sum telescopes** once `x` is at or beyond every knot. -/
theorem pieces_right (S : Shape) (hDx : (0 : ℝ) < (S.Dx : ℝ)) :
    ∀ {ks : List (ℤ × ℤ)} {p : ℤ × ℤ} {x : ℝ}, okList (p :: ks) = true →
      (∀ r ∈ p :: ks, S.xr r ≤ x) →
      pieces S (p :: ks) x = S.yr (lastK (p :: ks)) - S.yr p
  | [], _, _, _, _ => by simp [pieces, lastK]
  | q :: rest, p, x, h, hx => by
    obtain ⟨hlt, _, htail⟩ := okList_cons h
    have hxlt : S.xr p < S.xr q := xr_lt_xr hDx hlt
    have hne : S.xr q - S.xr p ≠ 0 := sub_ne_zero_of_ne (ne_of_gt hxlt)
    have hq : S.xr q ≤ x := hx q (by simp)
    have h1 : piece ((S.yr q - S.yr p) / (S.xr q - S.xr p)) (S.xr p) (S.xr q) x
        = S.yr q - S.yr p := by
      rw [piece_of_ge (le_of_lt hxlt) hq]
      field_simp
    have h2 : pieces S (q :: rest) x = S.yr (lastK (q :: rest)) - S.yr q :=
      pieces_right S hDx htail (fun r hr => hx r (List.mem_cons_of_mem _ hr))
    have hunfold : pieces S (p :: q :: rest) x
        = piece ((S.yr q - S.yr p) / (S.xr q - S.xr p)) (S.xr p) (S.xr q) x
            + pieces S (q :: rest) x := rfl
    rw [hunfold, h1, h2, lastK_cons_cons]
    ring

/-- **Soundness at the right end.**  A shape that passes `ok` takes its last knot's
ordinate everywhere at or to the right of its last knot's abscissa.  Mirror of
`ShapeMonotone.Shape.eval_head`. -/
theorem eval_flat_right {S : Shape} {p : ℤ × ℤ} {rest : List (ℤ × ℤ)}
    (h : S.ok = true) (hks : S.ks = p :: rest) {x : ℝ}
    (hx : S.xr (lastK S.ks) ≤ x) : S.eval x = S.yr (lastK S.ks) := by
  simp only [RevPebbling.ShapeMonotone.Shape.ok, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hxD, _⟩, hok⟩ := h
  have hDx : (0 : ℝ) < (S.Dx : ℝ) := by exact_mod_cast hxD
  have hok' : okList (p :: rest) = true := by rwa [hks] at hok
  have hall : ∀ r ∈ p :: rest, S.xr r ≤ x := by
    intro r hr
    refine le_trans (xr_le_xr hDx ?_) hx
    have hle := okList_le_lastK hok' r hr
    rw [hks]; exact hle
  have hpieces : pieces S S.ks x = S.yr (lastK S.ks) - S.yr p := by
    rw [hks]; exact pieces_right S hDx hok' hall
  simp only [RevPebbling.ShapeMonotone.Shape.eval, hpieces,
    RevPebbling.ShapeMonotone.Shape.y0_cons hks]
  ring

/-- The packaged form: a shape whose last knot is the origin vanishes on `[0, ∞)`. -/
theorem eval_zero_of_nonneg {S : Shape} {p : ℤ × ℤ} {rest : List (ℤ × ℤ)}
    (h : S.ok = true) (hks : S.ks = p :: rest) (hlast : lastK S.ks = (0, 0))
    {x : ℝ} (hx : 0 ≤ x) : S.eval x = 0 := by
  have hxr : S.xr (lastK S.ks) = 0 := by
    simp [RevPebbling.ShapeMonotone.Shape.xr, hlast]
  have hev := eval_flat_right h hks (x := x) (by rw [hxr]; exact hx)
  rw [hev, hlast]
  simp [RevPebbling.ShapeMonotone.Shape.yr]

/-! ## The model of `Ψ` at one level -/

/-- **`m48`'s subsolution value at one level.**  `capexp` is `S − 1`, the cap is
`2^{capexp} − 1`, `corner` is the level's corner abscissa, and `yhat` is the normalised
family shape in the level's own coordinate `t = log₂ v − corner`
(`m48_exact_replay.py:163-281`). -/
def Psi (capexp : ℕ) (yhat : ℝ → ℝ) (corner : ℝ) (v : ℕ) : ℕ :=
  min (2 ^ capexp - 1)
    ⌊(2 : ℝ) ^ ((capexp : ℝ) + yhat (Real.logb 2 (v : ℝ) - corner))⌋₊

/-- **The cap zone.**  If the shape vanishes on `[0, ∞)` — which is what the knot
list's last knot being the origin gives — then `Ψ` returns the cap at every `v` at or
above `2^{corner}`.  No hypothesis is placed on `yhat` anywhere else. -/
theorem Psi_eq_cap {capexp : ℕ} {yhat : ℝ → ℝ} {corner : ℝ} {v : ℕ}
    (hflat : ∀ t : ℝ, 0 ≤ t → yhat t = 0)
    (hv : (2 : ℝ) ^ corner ≤ (v : ℝ)) :
    Psi capexp yhat corner v = 2 ^ capexp - 1 := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ corner := Real.rpow_pos_of_pos (by norm_num) corner
  have hvpos : (0 : ℝ) < (v : ℝ) := lt_of_lt_of_le hpow hv
  have hrp : (2 : ℝ) ^ Real.logb 2 (v : ℝ) = (v : ℝ) :=
    Real.rpow_logb (by norm_num) (by norm_num) hvpos
  have hlogb : corner ≤ Real.logb 2 (v : ℝ) := by
    have hle : (2 : ℝ) ^ corner ≤ (2 : ℝ) ^ Real.logb 2 (v : ℝ) := by rw [hrp]; exact hv
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).mp hle
  have ht : yhat (Real.logb 2 (v : ℝ) - corner) = 0 := hflat _ (by linarith)
  have hfloor : ⌊(2 : ℝ) ^ ((capexp : ℝ) + yhat (Real.logb 2 (v : ℝ) - corner))⌋₊
      = 2 ^ capexp := by
    rw [ht, add_zero, Real.rpow_natCast,
      show ((2 : ℝ) ^ capexp) = ((2 ^ capexp : ℕ) : ℝ) by push_cast; ring,
      Nat.floor_natCast]
  simp only [Psi, hfloor]
  have h1 : (1 : ℕ) ≤ 2 ^ capexp := Nat.one_le_two_pow
  omega

/-- The `hcapzone` shape: `2^{capexp} − 1 ≤ Ψ v` on the cap zone. -/
theorem le_Psi_of_pow_le {capexp : ℕ} {yhat : ℝ → ℝ} {corner : ℝ} {v : ℕ}
    (hflat : ∀ t : ℝ, 0 ≤ t → yhat t = 0)
    (hv : (2 : ℝ) ^ corner ≤ (v : ℝ)) :
    2 ^ capexp - 1 ≤ Psi capexp yhat corner v :=
  le_of_eq (Psi_eq_cap hflat hv).symm

/-- **`m48`'s integer early return is sound.**  The replay does not test
`2^{corner} ≤ v`; it tests `v.bit_length() − 1 ≥ x_top`, i.e. `⌊log₂ v⌋ ≥ corner`
(`m48_exact_replay.py:245-246`).  That test is *sufficient* — it may miss cap-zone
points, which costs sharpness, never soundness. -/
theorem Psi_eq_cap_of_natLog {capexp : ℕ} {yhat : ℝ → ℝ} {corner : ℝ} {v : ℕ}
    (hflat : ∀ t : ℝ, 0 ≤ t → yhat t = 0) (hv : 1 ≤ v)
    (h : corner ≤ (Nat.log 2 v : ℝ)) :
    Psi capexp yhat corner v = 2 ^ capexp - 1 := by
  refine Psi_eq_cap hflat ?_
  have hstep : (2 : ℝ) ^ corner ≤ (2 : ℝ) ^ ((Nat.log 2 v : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  have hnat : (2 : ℝ) ^ ((Nat.log 2 v : ℕ) : ℝ) = ((2 ^ Nat.log 2 v : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; ring
  have hle : (2 ^ Nat.log 2 v : ℕ) ≤ v := Nat.pow_log_le_self 2 (by omega)
  have hcast : ((2 ^ Nat.log 2 v : ℕ) : ℝ) ≤ (v : ℝ) := by exact_mod_cast hle
  rw [hnat] at hstep
  linarith

/-! ## Lemma C-flat with `hcapzone` discharged -/

/-- **Lemma C-flat, one hypothesis fewer.**  This is `TieBand.cflat_step` with
`hcapzone` supplied: `Ψ_{S−1}` is instantiated as the model `Psi n ŷ (cornerS − a)` and
`F_S` as `2^{cornerS}`, so the geometric law `F_{S−1} = F_S · 2^{−a}` becomes the
identity `2^{cornerS} · 2^{−a} = 2^{cornerS − a}` instead of an assumption.  The only
surviving input about the shape is that it is flat at and above its top knot. -/
theorem cflat_step_capzone {ΨS : ℕ → ℕ} {n : ℕ} {ŷ : ℝ → ℝ}
    {cornerS σ₁ dp a tc : ℝ} {v u w : ℕ}
    (hflat : ∀ t : ℝ, 0 ≤ t → ŷ t = 0)
    (hC1 : σ₁ * (2 : ℝ) ^ dp + (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ tc)
    (hσ0 : 0 ≤ σ₁)
    (hcap : ΨS v ≤ 2 ^ (n + 1) - 1)
    (hu : 2 ^ n - 1 ≤ ΨS u)
    (hv : (2 : ℝ) ^ cornerS * (2 : ℝ) ^ tc ≤ (v : ℝ))
    (hule : (u : ℝ) ≤ σ₁ * (2 : ℝ) ^ dp * (2 : ℝ) ^ cornerS)
    (hw : (w : ℕ) = v - u) (hwr : ((w : ℕ) : ℝ) = (v : ℝ) - (u : ℝ)) :
    ΨS v ≤ 1 + Psi n ŷ (cornerS - a) v
             + min (ΨS u) (Psi n ŷ (cornerS - a) w) := by
  have hgeom : (2 : ℝ) ^ cornerS * (2 : ℝ) ^ (-a) = (2 : ℝ) ^ (cornerS - a) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  refine RevPebbling.TieBand.cflat_step (F := (2 : ℝ) ^ cornerS)
    (Real.rpow_pos_of_pos (by norm_num) _) hC1 hσ0 ?_ hcap hu hv hule hw hwr
  intro x hx
  rw [hgeom] at hx
  exact le_Psi_of_pow_le hflat hx

end

/-! ## The four repaired anchors

The `Shape`s are those of `RevPebbling.ShapeMonotone`; nothing is re-transcribed here.
What is checked below is the one extra fact the cap zone needs: **the last knot is the
origin.**  In the manuscript's relative coordinates that is `rel[0] = (0, 0)` — the
family's top knot, where the normalised shape is by construction `0`.  It is checked
against the anchor cfgs, exactly over `Fraction`s, by `scripts/probe_brw/m69_cap_zone.py`
(row `C1`), and it is the same datum in the ascending Lean lists, whose last entry is
`(0, 0)` (row `C4`).

`ok` and `lastK` are independent checks: `ok` never looks at the last knot's ordinate,
so a mutation of that ordinate passes `ok` and is caught only here — exactly as
`eps0035_yr_head` and `ok` were independent in `ShapeMonotone`. -/

/-- **`ok` and `lastK` are independent.**  This shape passes the `ShapeMonotone` checker
— its abscissae increase and its ordinates do not decrease — yet its last knot is not
the origin.  So a mutation of the final ordinate slips past `ok` and is caught only by
the `lastK` checks below.  (Verified by injection on the real data as well: raising
`t0035`'s final `(0, 0)` to `(0, 1)` leaves `eps0035_ok` green and fails
`eps0035_lastK` alone.) -/
example : Shape.ok { Dx := 1, Dy := 1, ks := [(-1, -1), (0, 1)] } = true := by decide

example : lastK [((-1 : ℤ), (-1 : ℤ)), (0, 1)] ≠ (0, 0) := by decide

theorem eps0035_lastK : lastK eps0035.ks = (0, 0) := by rfl

theorem eps003_lastK : lastK eps003.ks = (0, 0) := by rfl

theorem eps0025_lastK : lastK eps0025.ks = (0, 0) := by rfl

theorem eps002_lastK : lastK eps002.ks = (0, 0) := by rfl

noncomputable section

/-- **ε = 0.0035: the shape vanishes on `[0, ∞)`.** -/
theorem eps0035_flat {x : ℝ} (hx : 0 ≤ x) : eps0035.eval x = 0 :=
  eval_zero_of_nonneg eps0035_ok (rest := t0035) rfl eps0035_lastK hx

/-- **ε = 0.003: the shape vanishes on `[0, ∞)`.** -/
theorem eps003_flat {x : ℝ} (hx : 0 ≤ x) : eps003.eval x = 0 :=
  eval_zero_of_nonneg eps003_ok (rest := t003) rfl eps003_lastK hx

/-- **ε = 0.0025: the shape vanishes on `[0, ∞)`.** -/
theorem eps0025_flat {x : ℝ} (hx : 0 ≤ x) : eps0025.eval x = 0 :=
  eval_zero_of_nonneg eps0025_ok (rest := t0025) rfl eps0025_lastK hx

/-- **ε = 0.002: the shape vanishes on `[0, ∞)`.** -/
theorem eps002_flat {x : ℝ} (hx : 0 ≤ x) : eps002.eval x = 0 :=
  eval_zero_of_nonneg eps002_ok (rest := t002) rfl eps002_lastK hx

/-- The geometric law as an identity on exponents. -/
theorem pow_corner_sub (cornerS a : ℝ) :
    (2 : ℝ) ^ cornerS * (2 : ℝ) ^ (-a) = (2 : ℝ) ^ (cornerS - a) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  ring_nf

/-- **The cap zone at the ε = 0.0035 anchor.**  Residue (i) of §6.11, discharged for
this shape: at level `S − 1`, every `v ≥ F_S · 2^{−a}` sits at the cap. -/
theorem eps0035_capzone {capexp : ℕ} {cornerS a : ℝ} {v : ℕ}
    (hv : (2 : ℝ) ^ cornerS * (2 : ℝ) ^ (-a) ≤ (v : ℝ)) :
    Psi capexp eps0035.eval (cornerS - a) v = 2 ^ capexp - 1 :=
  Psi_eq_cap (fun _ ht => eps0035_flat ht) (by rwa [pow_corner_sub] at hv)

theorem eps003_capzone {capexp : ℕ} {cornerS a : ℝ} {v : ℕ}
    (hv : (2 : ℝ) ^ cornerS * (2 : ℝ) ^ (-a) ≤ (v : ℝ)) :
    Psi capexp eps003.eval (cornerS - a) v = 2 ^ capexp - 1 :=
  Psi_eq_cap (fun _ ht => eps003_flat ht) (by rwa [pow_corner_sub] at hv)

theorem eps0025_capzone {capexp : ℕ} {cornerS a : ℝ} {v : ℕ}
    (hv : (2 : ℝ) ^ cornerS * (2 : ℝ) ^ (-a) ≤ (v : ℝ)) :
    Psi capexp eps0025.eval (cornerS - a) v = 2 ^ capexp - 1 :=
  Psi_eq_cap (fun _ ht => eps0025_flat ht) (by rwa [pow_corner_sub] at hv)

theorem eps002_capzone {capexp : ℕ} {cornerS a : ℝ} {v : ℕ}
    (hv : (2 : ℝ) ^ cornerS * (2 : ℝ) ^ (-a) ≤ (v : ℝ)) :
    Psi capexp eps002.eval (cornerS - a) v = 2 ^ capexp - 1 :=
  Psi_eq_cap (fun _ ht => eps002_flat ht) (by rwa [pow_corner_sub] at hv)

/-- **Lemma C-flat at the ε = 0.0035 anchor with both shape-side residues discharged.**
`hcapzone` comes from `eps0035_flat` (residue (i), this module) and the `u` branch from
`eps0035_ge_neg_one` (residue (ii), `ShapeMonotone`); what remain as hypotheses are the
counting facts and the certified rational enclosure C1♭ of `m65`. -/
theorem cflat_step_eps0035 {ΨS : ℕ → ℕ} {n : ℕ} {cornerS σ₁ dp a tc : ℝ} {v u w : ℕ}
    (hC1 : σ₁ * (2 : ℝ) ^ dp + (2 : ℝ) ^ (-a) ≤ (2 : ℝ) ^ tc)
    (hσ0 : 0 ≤ σ₁)
    (hcap : ΨS v ≤ 2 ^ (n + 1) - 1)
    (hu : 2 ^ n - 1 ≤ ΨS u)
    (hv : (2 : ℝ) ^ cornerS * (2 : ℝ) ^ tc ≤ (v : ℝ))
    (hule : (u : ℝ) ≤ σ₁ * (2 : ℝ) ^ dp * (2 : ℝ) ^ cornerS)
    (hw : (w : ℕ) = v - u) (hwr : ((w : ℕ) : ℝ) = (v : ℝ) - (u : ℝ)) :
    ΨS v ≤ 1 + Psi n eps0035.eval (cornerS - a) v
             + min (ΨS u) (Psi n eps0035.eval (cornerS - a) w) :=
  cflat_step_capzone (fun _ ht => eps0035_flat ht) hC1 hσ0 hcap hu hv hule hw hwr

end

/-! ## Non-vacuity and sharpness

Two things could make the statements above true for the wrong reason: `Psi` could sit at
the cap everywhere (then `Psi_eq_cap` says nothing), or the flat-top hypothesis could be
unsatisfiable (then everything is provable).  Both are excluded here on a shape small
enough to check by hand.

`m69_cap_zone.py` measures the same two things against `m48`'s *real* `PsiEval.psi`
(rows `C3a` / `C3b`): on the cap zone the returned bracket is `(cap, cap)`, and just
below it the value is strictly less than the cap. -/

/-- A hand-checkable flat-topped shape: `(−1, −1) → (0, 0)`, one ramp of slope `1` that
levels off at the origin. -/
def toyFlat : Shape := { Dx := 1, Dy := 1, ks := [(-1, -1), (0, 0)] }

example : toyFlat.ok = true := by decide

theorem toyFlat_lastK : lastK toyFlat.ks = (0, 0) := by rfl

noncomputable section

theorem toyFlat_at (x : ℝ) : toyFlat.eval x = -1 + piece 1 (-1) 0 x := by
  norm_num [RevPebbling.ShapeMonotone.Shape.eval, RevPebbling.ShapeMonotone.Shape.y0,
    toyFlat, pieces, RevPebbling.ShapeMonotone.Shape.xr,
    RevPebbling.ShapeMonotone.Shape.yr]

theorem toyFlat_flat {x : ℝ} (hx : 0 ≤ x) : toyFlat.eval x = 0 :=
  eval_zero_of_nonneg (by decide) (p := (-1, -1)) (rest := [(0, 0)]) rfl toyFlat_lastK hx

/-- The toy shape is genuinely not the zero function: it takes `−1` one octave down. -/
theorem toyFlat_at_neg_one : toyFlat.eval (-1) = -1 := by
  norm_num [toyFlat_at, piece, clamp']

theorem logb_two_two : Real.logb 2 (2 : ℝ) = 1 := by
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp [Real.logb, div_self h2]

/-- **The hypotheses are satisfiable and the conclusion is reached.**  With
`capexp = 3` (cap `7`) and `corner = 2` (threshold `2^2 = 4`), `Ψ(4) = 7`. -/
example : Psi 3 toyFlat.eval 2 4 = 7 := by
  refine Psi_eq_cap (fun _ ht => toyFlat_flat ht) ?_
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    rw [show (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h4]
  norm_num

/-- **`Psi` is not constantly at the cap, so the threshold does work.**  One octave
below the corner the toy shape is at `−1`, so `Ψ(2) = ⌊2^{3−1}⌋ = 4 < 7`: the
conclusion of `Psi_eq_cap` is *false* just below `2^{corner}`. -/
example : Psi 3 toyFlat.eval 2 2 = 4 := by
  have hcast : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  have harg : Real.logb 2 ((2 : ℕ) : ℝ) - 2 = -1 := by
    rw [hcast, logb_two_two]; norm_num
  have hval : (2 : ℝ) ^ (((3 : ℕ) : ℝ) + toyFlat.eval (Real.logb 2 ((2 : ℕ) : ℝ) - 2))
      = 4 := by
    rw [harg, toyFlat_at_neg_one]
    rw [show ((3 : ℕ) : ℝ) + (-1 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  simp only [Psi, hval]
  norm_num

end

/-! ## Axiom audit (printed on every build) -/

#print axioms eval_flat_right
#print axioms Psi_eq_cap
#print axioms Psi_eq_cap_of_natLog
#print axioms cflat_step_capzone
#print axioms eps0035_capzone
#print axioms cflat_step_eps0035

end RevPebbling.CapZone
