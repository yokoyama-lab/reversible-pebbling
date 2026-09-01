import RevPebbling.TieBand

/-!
# Monotonicity of the family shape (the `hmono` input of Lemma C-flat)

`RevPebbling.TieBand.yhat_ge_neg_one` closes the `u` branch of Lemma C-flat from the
hypothesis `MonotoneOn ŷ (Set.Ici x_½)` — monotonicity of the normalised family shape
`ŷ` to the right of its half-way point.  That hypothesis was left *analytic*: it was
stated in `TieBand` but discharged nowhere.  This module discharges it.

`ŷ` is a continuous piecewise-linear function of a rational knot list, so the statement
"`ŷ` is nondecreasing" is a finite check on that list.  The pattern here is the one of
`RevPebbling.XLift`: **a checker whose soundness is an unconditional theorem, applied to
data whose provenance is external.**

* `okList` is the checker: `x` strictly increasing and `y` nondecreasing along the list.
  It looks only at integers, so no rational normalisation happens in the kernel.
* `Shape.eval_mono` is the soundness theorem: `S.ok = true → Monotone S.eval`.  It is
  proved for *every* shape, with no hypothesis on the data beyond what `ok` checks.

## What is and is not proved here

**Proved, unconditionally.** `okList`-soundness (`Shape.eval_mono`), the value at the
first knot (`Shape.eval_head`), and their combination `Shape.le_eval_head_add`, which is
exactly the shape `TieBand.yhat_ge_neg_one` consumes.

**Not proved here: that a given `Shape` *is* `ŷ`.**  Knot data is transcribed from the
repaired anchors of the companion manuscript repository by
`scripts/probe_brw/m68_shape_monotone.py`, which checks the transcription exactly over
`Fraction`s (that the knots are the cfg's knots, that the integer rescaling by
`Dx`/`Dy` is exact, and that `x_½` solves `ŷ(x_½) = −1` on its segment).  That is a
*replay-grade* fact about a particular file, not a theorem, and it is deliberately kept
outside Lean.  What Lean adds is that **no property of the shape beyond the finite `ok`
check is assumed** when the monotonicity hypothesis is used.

The `eval` model is the "sum of clamped ramps" form
`eval x = y₀ + Σᵢ mᵢ · (clamp x to [xᵢ, xᵢ₊₁] − xᵢ)`, which agrees with the usual
"find the segment containing `x`" definition on `[x₀, xₙ]` and extends it by the
constant `y₀` to the left and `yₙ` to the right.  It is used here because each summand
is separately monotone when its slope is nonnegative, so soundness needs no case split
on where `x` falls.  The `example`s at the end pin the agreement on a hand-checkable
shape, including both constant extensions.
-/

namespace RevPebbling.ShapeMonotone

/-- A piecewise-linear shape: knots `(xn, yn)` in ascending `x`, on the lattice
`(1/Dx) ℤ × (1/Dy) ℤ`.  Storing integer numerators against fixed denominators keeps the
checker on `Int` comparisons, so no rational normalisation reaches the kernel. -/
structure Shape where
  Dx : ℤ
  Dy : ℤ
  ks : List (ℤ × ℤ)

/-! ## The checker (computable, integers only) -/

/-- `x` strictly increasing and `y` nondecreasing along the knot list. -/
def okList : List (ℤ × ℤ) → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest => decide (p.1 < q.1) && decide (p.2 ≤ q.2) && okList (q :: rest)

/-- The shape-level checker: positive denominators and an `okList` knot list. -/
def Shape.ok (S : Shape) : Bool :=
  decide (0 < S.Dx) && decide (0 < S.Dy) && okList S.ks

/-! ## The model -/

noncomputable section

namespace Shape

/-- The real abscissa of a knot. -/
def xr (S : Shape) (p : ℤ × ℤ) : ℝ := (p.1 : ℝ) / (S.Dx : ℝ)

/-- The real ordinate of a knot. -/
def yr (S : Shape) (p : ℤ × ℤ) : ℝ := (p.2 : ℝ) / (S.Dy : ℝ)

/-- The ordinate of the first knot (`0` for the empty shape). -/
def y0 (S : Shape) : ℝ :=
  match S.ks with
  | [] => 0
  | p :: _ => S.yr p

end Shape

/-- `x` clamped to `[l, u]`, written `max l (min u x)`. -/
def clamp' (l u x : ℝ) : ℝ := max l (min u x)

/-- One ramp: slope `m`, rising over `[l, u]`, flat outside. -/
def piece (m l u x : ℝ) : ℝ := m * (clamp' l u x - l)

/-- The sum of the ramps of a knot list. -/
def pieces (S : Shape) : List (ℤ × ℤ) → ℝ → ℝ
  | [] => fun _ => 0
  | [_] => fun _ => 0
  | p :: q :: rest => fun x =>
      piece ((S.yr q - S.yr p) / (S.xr q - S.xr p)) (S.xr p) (S.xr q) x
        + pieces S (q :: rest) x

/-- The shape as a function `ℝ → ℝ`: the first knot's ordinate plus the ramps. -/
def Shape.eval (S : Shape) (x : ℝ) : ℝ := S.y0 + pieces S S.ks x

/-! ## Monotonicity of one ramp -/

theorem clamp'_mono (l u : ℝ) : Monotone (clamp' l u) := fun _ _ hab =>
  max_le_max le_rfl (min_le_min le_rfl hab)

theorem piece_mono {m l u : ℝ} (hm : 0 ≤ m) : Monotone (piece m l u) := by
  intro a b hab
  have h := clamp'_mono l u hab
  have h' : clamp' l u a - l ≤ clamp' l u b - l := by linarith
  exact mul_le_mul_of_nonneg_left h' hm

/-- A ramp has not started yet to the left of its foot. -/
theorem piece_of_le {m l u x : ℝ} (hx : x ≤ l) : piece m l u x = 0 := by
  have h : min u x ≤ l := le_trans (min_le_right _ _) hx
  simp [piece, clamp', max_eq_left h]

/-! ## Soundness of the checker -/

theorem okList_cons {p q : ℤ × ℤ} {rest : List (ℤ × ℤ)}
    (h : okList (p :: q :: rest) = true) :
    p.1 < q.1 ∧ p.2 ≤ q.2 ∧ okList (q :: rest) = true := by
  simp only [okList, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Every knot of an `okList` list sits at or to the right of the first one. -/
theorem okList_head_le : ∀ {p : ℤ × ℤ} {rest : List (ℤ × ℤ)},
    okList (p :: rest) = true → ∀ q ∈ p :: rest, p.1 ≤ q.1
  | _, [], _, q, hq => by simp at hq; simp [hq]
  | p, r :: rest, h, q, hq => by
    obtain ⟨hlt, _, htail⟩ := okList_cons h
    rcases List.mem_cons.1 hq with hq | hq
    · simp [hq]
    · exact le_trans (le_of_lt hlt) (okList_head_le htail q hq)

theorem xr_lt_xr {S : Shape} {p q : ℤ × ℤ} (hDx : (0 : ℝ) < (S.Dx : ℝ))
    (h : p.1 < q.1) : S.xr p < S.xr q := by
  have h1 : (p.1 : ℝ) < (q.1 : ℝ) := by exact_mod_cast h
  simp only [Shape.xr, div_eq_mul_inv]
  exact mul_lt_mul_of_pos_right h1 (inv_pos.mpr hDx)

theorem xr_le_xr {S : Shape} {p q : ℤ × ℤ} (hDx : (0 : ℝ) < (S.Dx : ℝ))
    (h : p.1 ≤ q.1) : S.xr p ≤ S.xr q := by
  have h1 : (p.1 : ℝ) ≤ (q.1 : ℝ) := by exact_mod_cast h
  simp only [Shape.xr, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.mpr hDx))

theorem yr_le_yr {S : Shape} {p q : ℤ × ℤ} (hDy : (0 : ℝ) < (S.Dy : ℝ))
    (h : p.2 ≤ q.2) : S.yr p ≤ S.yr q := by
  have h1 : (p.2 : ℝ) ≤ (q.2 : ℝ) := by exact_mod_cast h
  simp only [Shape.yr, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.mpr hDy))

/-- **Soundness, ramp sum.**  An `okList` knot list has nonnegative slopes, hence a
monotone ramp sum. -/
theorem pieces_mono (S : Shape) (hx : 0 < S.Dx) (hy : 0 < S.Dy) :
    ∀ {ks : List (ℤ × ℤ)}, okList ks = true → Monotone (pieces S ks)
  | [], _ => by intro a b _; simp [pieces]
  | [_], _ => by intro a b _; simp [pieces]
  | p :: q :: rest, h => by
    obtain ⟨hlt, hle, htail⟩ := okList_cons h
    have hDx : (0 : ℝ) < (S.Dx : ℝ) := by exact_mod_cast hx
    have hDy : (0 : ℝ) < (S.Dy : ℝ) := by exact_mod_cast hy
    have hxlt : S.xr p < S.xr q := xr_lt_xr hDx hlt
    have hyle : S.yr p ≤ S.yr q := yr_le_yr hDy hle
    have hm : 0 ≤ (S.yr q - S.yr p) / (S.xr q - S.xr p) :=
      div_nonneg (by linarith) (by linarith)
    intro a b hab
    have h1 := piece_mono (l := S.xr p) (u := S.xr q) hm hab
    have h2 := pieces_mono S hx hy htail hab
    simpa [pieces] using add_le_add h1 h2

/-- **Soundness.**  A shape that passes `ok` is monotone on all of `ℝ`. -/
theorem Shape.eval_mono {S : Shape} (h : S.ok = true) : Monotone S.eval := by
  simp only [Shape.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx, hy⟩, hks⟩ := h
  intro a b hab
  have hm := pieces_mono S hx hy hks hab
  simp only [Shape.eval]
  linarith

/-- Monotone on any `Set.Ici`, which is the form `TieBand.yhat_ge_neg_one` asks for. -/
theorem Shape.eval_monotoneOn {S : Shape} (h : S.ok = true) (c : ℝ) :
    MonotoneOn S.eval (Set.Ici c) := (Shape.eval_mono h).monotoneOn _

/-! ## The value at the first knot -/

theorem pieces_left (S : Shape) : ∀ {ks : List (ℤ × ℤ)} {x : ℝ},
    (∀ q ∈ ks, x ≤ S.xr q) → pieces S ks x = 0
  | [], _, _ => by simp [pieces]
  | [_], _, _ => by simp [pieces]
  | p :: q :: rest, x, h => by
    have h0 : piece ((S.yr q - S.yr p) / (S.xr q - S.xr p)) (S.xr p) (S.xr q) x = 0 :=
      piece_of_le (h p (by simp))
    have h1 : pieces S (q :: rest) x = 0 :=
      pieces_left S (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp [pieces, h0, h1]

theorem Shape.y0_cons {S : Shape} {p : ℤ × ℤ} {rest : List (ℤ × ℤ)}
    (hks : S.ks = p :: rest) : S.y0 = S.yr p := by
  simp only [Shape.y0, hks]

/-- **The value at the left end.**  A shape that passes `ok` takes its first knot's
ordinate at its first knot's abscissa. -/
theorem Shape.eval_head {S : Shape} {p : ℤ × ℤ} {rest : List (ℤ × ℤ)}
    (h : S.ok = true) (hks : S.ks = p :: rest) : S.eval (S.xr p) = S.yr p := by
  simp only [Shape.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx, _⟩, hok⟩ := h
  have hDx : (0 : ℝ) < (S.Dx : ℝ) := by exact_mod_cast hx
  have hzero : pieces S S.ks (S.xr p) = 0 := by
    refine pieces_left S ?_
    intro q hq
    rw [hks] at hq
    exact xr_le_xr hDx (okList_head_le (by rwa [hks] at hok) q hq)
  simp only [Shape.eval, hzero, Shape.y0_cons hks, add_zero]

/-- **The packaged statement.**  This is what `TieBand.yhat_ge_neg_one` consumes: to the
right of the first knot the shape stays at or above the first knot's ordinate. -/
theorem Shape.le_eval_head_add {S : Shape} {p : ℤ × ℤ} {rest : List (ℤ × ℤ)}
    (h : S.ok = true) (hks : S.ks = p :: rest) {s : ℝ} (hs : 0 ≤ s) :
    S.yr p ≤ S.eval (S.xr p + s) := by
  have hmono := Shape.eval_mono h (a := S.xr p) (b := S.xr p + s) (by linarith)
  rwa [Shape.eval_head h hks] at hmono

end

/-! ## The model agrees with the naive one (hand-checkable) -/

/-- A three-knot shape: `(0, 0) → (1, 2) → (3, 3)`, i.e. slope `2` then slope `1/2`. -/
def toy : Shape := { Dx := 1, Dy := 1, ks := [(0, 0), (1, 2), (3, 3)] }

example : toy.ok = true := by decide

/-- The checker is not vacuous: it rejects a shape with a descending step. -/
example : Shape.ok { Dx := 1, Dy := 1, ks := [(0, 0), (1, 2), (3, 1)] } = false := by decide

/-- …and one whose abscissae do not advance. -/
example : Shape.ok { Dx := 1, Dy := 1, ks := [(0, 0), (1, 2), (1, 3)] } = false := by decide

section Toy

private theorem toy_at (x : ℝ) :
    toy.eval x = piece 2 0 1 x + piece (1 / 2) 1 3 x := by
  norm_num [Shape.eval, Shape.y0, toy, pieces, Shape.xr, Shape.yr]

example : toy.eval 0 = 0 := by norm_num [toy_at, piece, clamp']

example : toy.eval 1 = 2 := by norm_num [toy_at, piece, clamp']

example : toy.eval 2 = 5 / 2 := by norm_num [toy_at, piece, clamp']

example : toy.eval 3 = 3 := by norm_num [toy_at, piece, clamp']

/-- Constant extension to the right. -/
example : toy.eval 10 = 3 := by norm_num [toy_at, piece, clamp']

/-- Constant extension to the left. -/
example : toy.eval (-5) = 0 := by norm_num [toy_at, piece, clamp']

end Toy

/-! ## The four repaired anchors

Each `Shape` below is transcribed from one repaired anchor cfg of the companion
manuscript repository by `scripts/probe_brw/m68_shape_monotone.py` (`emit-lean`),
restricted to `x ≥ x_½`.  The first knot is `(x_½, −1)`: `x_½` is not a cfg knot, it is
the exact rational solution of `ŷ(x) = −1` on the segment that straddles `−1`, so the
list starts by splitting that segment — which leaves the function unchanged.  The last
knot is `(0, 0)`, and `eval` extends by the constant `0` to the right of it, matching
`ŷ(x) = 0` for `x ≥ 0`.  The integer rescaling by `Dx`/`Dy` is exact, checked over
`Fraction`s by m68 and again by a second, independent transcription; the two agreed on
every one of the 74 + 74 + 73 + 117 knots and on all eight denominators.

`a` does not appear here.  Unlike the band certificates of m67, whose `L1b` row exists
because the certificate had to be pinned to `a`, the shape `ŷ` is a function of the cfg
alone — `family_from_cfg`'s `rel` never reads `a` — so there is nothing for `a` to bind.

**Domain of agreement.**  `eval = ŷ` on `[x_½, ∞)` **only**.  To the left of `x_½` this
`eval` is the constant `−1` whereas `ŷ` keeps descending, so nothing below `x_½` may be
read off these shapes.  Every theorem below is stated at `x_½ + s` with `s ≥ 0`, which
is also the only place Lemma C-flat evaluates the shape.

**What a mutation would and would not catch.**  `ok` catches any break of monotonicity,
down to one unit in the last place of a `y` numerator (verified by injection).
`yr_head` catches a wrong ordinate at the head — and is needed, because a head ordinate
can be wrong while `ok` still passes.  Neither catches a wrong *abscissa* `x_½`: the
statements would stay true, but about the wrong point.  Binding `x_½` to the cfg is
m68's `M2` check, not Lean's.
-/

/-- The half-way knot `(x_½, −1)` of the ε = 0.0035 shape (anchor `b330fix.cfg`, `a = 1341/4000`, `S₀ = 330`). -/
def h0035 : ℤ × ℤ := (-66128364181619517654704, -1000000000000)

/-- The 73 cfg knots of the ε = 0.0035 shape strictly to the right of `x_½`. -/
def t0035 : List (ℤ × ℤ) :=
  [(-65804044958256094180271, -990270423299),
   (-64861293597832188360542, -962239535238),
   (-63918542237380000000000, -934468004709),
   (-62975790876956094180271, -906959474426),
   (-62033039516532188360542, -879721315226),
   (-61090288156080000000000, -852759500192),
   (-60147536795656094180271, -826079074801),
   (-59204785435232188360542, -799681587767),
   (-58262034074780000000000, -773575996442),
   (-57319282714356094180271, -747768026041),
   (-56376531353932188360542, -722265306986),
   (-55433779993480000000000, -697072733722),
   (-54491028633056094180271, -672199759010),
   (-53548277272632188360542, -647651877581),
   (-52605525912180000000000, -623439842197),
   (-51662774551756094180271, -599569151692),
   (-50720023191332188360542, -576049151036),
   (-49777271830880000000000, -552880518121),
   (-48834520470456094180271, -530072927933),
   (-47891769110032188360542, -507634469508),
   (-46949017749580000000000, -485573333200),
   (-46006266389156094180271, -463900829743),
   (-45063515028732188360542, -442622981442),
   (-44120763668280000000000, -421750659162),
   (-43178012307856094180271, -401292540978),
   (-42235260947432188360542, -381256636187),
   (-41292509586980000000000, -361653308326),
   (-40349758226556094180271, -342488656258),
   (-39407006866132188360542, -323768255259),
   (-38464255505680000000000, -305504038954),
   (-37521504145256094180271, -287705208040),
   (-36578752784832188360542, -270383778029),
   (-35636001424380000000000, -253546807611),
   (-34693250063956094180271, -237205576877),
   (-33750498703532188360542, -221367826705),
   (-32807747343080000000000, -206046251939),
   (-31864995982656094180271, -191246139438),
   (-30922244622232188360542, -176981583680),
   (-29979493261780000000000, -163250414991),
   (-29036741901356094180271, -150066104938),
   (-28093990540932188360542, -137434967823),
   (-27151239180480000000000, -125366910540),
   (-26208487820056094180271, -113870582367),
   (-25265736459632188360542, -102948668152),
   (-24322985099180000000000, -92610332828),
   (-23380233738756094180271, -82858007738),
   (-22437482378332188360542, -73696734059),
   (-21494731017880000000000, -65128907570),
   (-20551979657456094180271, -57150287868),
   (-19609228297032188360542, -49752390563),
   (-18666476936580000000000, -42937851749),
   (-17723725576156094180271, -36699084647),
   (-16780974215732188360542, -31034567131),
   (-15838222855280000000000, -25929020873),
   (-14895471494856094180271, -21373364039),
   (-13952720134432188360542, -17352779459),
   (-13009968773980000000000, -13849447751),
   (-12067217413556094180271, -10835882130),
   (-11313016325200000000000, -8792332158),
   (-11124466053132188360542, -8282444665),
   (-10181714692680000000000, -6150150977),
   (-9238963332256094180271, -4406603370),
   (-8484762243900000000000, -3294202325),
   (-8296211971832188360542, -3015102064),
   (-7353460611380000000000, -1939814265),
   (-6410709250956094180271, -1148370397),
   (-5467957890532188360542, -603808476),
   (-4525206530080000000000, -265334049),
   (-3582455169656094180271, -88372879),
   (-2639703809232188360542, -23445429),
   (-1414127040650000000000, -19524337),
   (-848476224390000000000, -2714602),
   (0, 0)]

/-- The ε = 0.0035 family shape on `[x_½, ∞)`: 74 knots. -/
def eps0035 : Shape where
  Dx := 28282540813000000000000
  Dy := 1000000000000
  ks := h0035 :: t0035

/-- The finite check passes: `x` strictly increasing, `y` nondecreasing. -/
theorem eps0035_ok : eps0035.ok = true := by decide

/-- The first knot sits at height `−1`, by construction of `x_½`. -/
theorem eps0035_yr_head : eps0035.yr h0035 = -1 := by
  simp only [Shape.yr, h0035, eps0035]
  norm_num

/-- **The `u`-branch input of Lemma C-flat, ε = 0.0035.**  This is
`TieBand.yhat_ge_neg_one` with `ŷ := eps0035.eval`, both of its hypotheses
supplied — so residue (ii) of §6.11 is discharged for this shape. -/
theorem eps0035_ge_neg_one {s : ℝ} (hs : 0 ≤ s) :
    (-1 : ℝ) ≤ eps0035.eval (eps0035.xr h0035 + s) :=
  RevPebbling.TieBand.yhat_ge_neg_one
    (Shape.eval_monotoneOn eps0035_ok (eps0035.xr h0035))
    (by rw [Shape.eval_head (rest := t0035) eps0035_ok rfl]; exact eps0035_yr_head) hs

/-- The half-way knot `(x_½, −1)` of the ε = 0.003 shape (anchor `b512fix.cfg`, `a = 1339/4000`, `S₀ = 512`). -/
def h003 : ℤ × ℤ := (-66128364181619517654704, -1000000000000)

/-- The 73 cfg knots of the ε = 0.003 shape strictly to the right of `x_½`. -/
def t003 : List (ℤ × ℤ) :=
  [(-65804044958256094180271, -990270423299),
   (-64861293597803905819729, -962239535238),
   (-63918542237380000000000, -934468004709),
   (-62975790876956094180271, -906959474426),
   (-62033039516503905819729, -879721315226),
   (-61090288156080000000000, -852759500192),
   (-60147536795656094180271, -826079074801),
   (-59204785435203905819729, -799681587767),
   (-58262034074780000000000, -773575996442),
   (-57319282714356094180271, -747768026041),
   (-56376531353903905819729, -722265306986),
   (-55433779993480000000000, -697072733722),
   (-54491028633056094180271, -672199759010),
   (-53548277272603905819729, -647651877581),
   (-52605525912180000000000, -623439842197),
   (-51662774551756094180271, -599569151692),
   (-50720023191303905819729, -576049151036),
   (-49777271830880000000000, -552880518121),
   (-48834520470456094180271, -530072927933),
   (-47891769110003905819729, -507634469508),
   (-46949017749580000000000, -485573333200),
   (-46006266389156094180271, -463900829743),
   (-45063515028703905819729, -442622981442),
   (-44120763668280000000000, -421750659162),
   (-43178012307856094180271, -401292540978),
   (-42235260947403905819729, -381256636187),
   (-41292509586980000000000, -361653308326),
   (-40349758226556094180271, -342488656258),
   (-39407006866103905819729, -323768255259),
   (-38464255505680000000000, -305504038954),
   (-37521504145256094180271, -287705208040),
   (-36578752784803905819729, -270383778029),
   (-35636001424380000000000, -253546807611),
   (-34693250063956094180271, -237205576877),
   (-33750498703503905819729, -221367826705),
   (-32807747343080000000000, -206046251939),
   (-31864995982656094180271, -191246139438),
   (-30922244622203905819729, -176981583680),
   (-29979493261780000000000, -163250414991),
   (-29036741901356094180271, -150066104938),
   (-28093990540903905819729, -137434967823),
   (-27151239180480000000000, -125366910540),
   (-26208487820056094180271, -113870582367),
   (-25265736459603905819729, -102948668152),
   (-24322985099180000000000, -92610332828),
   (-23380233738756094180271, -82858007738),
   (-22437482378303905819729, -73696734059),
   (-21494731017880000000000, -65128907570),
   (-20551979657456094180271, -57150287868),
   (-19609228297003905819729, -49752390563),
   (-18666476936580000000000, -42937851749),
   (-17723725576156094180271, -36699084647),
   (-16780974215703905819729, -31034567131),
   (-15838222855280000000000, -25929020873),
   (-14895471494856094180271, -21373364039),
   (-14141270406500000000000, -18156896375),
   (-13952720134403905819729, -17353446126),
   (-13009968773980000000000, -13853447751),
   (-12067217413556094180271, -10843215463),
   (-11124466053103905819729, -8292111332),
   (-10181714692680000000000, -6158150977),
   (-9238963332256094180271, -4412936703),
   (-9050413060160000000000, -4134503109),
   (-8296211971803905819729, -3018102064),
   (-7353460611380000000000, -1942814265),
   (-6410709250956094180271, -1151370397),
   (-5467957890503905819729, -606808476),
   (-4525206530080000000000, -268334049),
   (-3582455169656094180271, -91372879),
   (-2639703809203905819729, -26445429),
   (-1414127040650000000000, -22524337),
   (-848476224390000000000, -2714602),
   (0, 0)]

/-- The ε = 0.003 family shape on `[x_½, ∞)`: 74 knots. -/
def eps003 : Shape where
  Dx := 28282540813000000000000
  Dy := 1000000000000
  ks := h003 :: t003

/-- The finite check passes: `x` strictly increasing, `y` nondecreasing. -/
theorem eps003_ok : eps003.ok = true := by decide

/-- The first knot sits at height `−1`, by construction of `x_½`. -/
theorem eps003_yr_head : eps003.yr h003 = -1 := by
  simp only [Shape.yr, h003, eps003]
  norm_num

/-- **The `u`-branch input of Lemma C-flat, ε = 0.003.**  This is
`TieBand.yhat_ge_neg_one` with `ŷ := eps003.eval`, both of its hypotheses
supplied — so residue (ii) of §6.11 is discharged for this shape. -/
theorem eps003_ge_neg_one {s : ℝ} (hs : 0 ≤ s) :
    (-1 : ℝ) ≤ eps003.eval (eps003.xr h003 + s) :=
  RevPebbling.TieBand.yhat_ge_neg_one
    (Shape.eval_monotoneOn eps003_ok (eps003.xr h003))
    (by rw [Shape.eval_head (rest := t003) eps003_ok rfl]; exact eps003_yr_head) hs

/-- The half-way knot `(x_½, −1)` of the ε = 0.0025 shape (anchor `b915fix.cfg`, `a = 1337/4000`, `S₀ = 915`). -/
def h0025 : ℤ × ℤ := (-66128364181600964690592, -1000000000000)

/-- The 72 cfg knots of the ε = 0.0025 shape strictly to the right of `x_½`. -/
def t0025 : List (ℤ × ℤ) :=
  [(-65804044958227811639458, -990270423299),
   (-64861293597803905819729, -962239535238),
   (-63918542237380000000000, -934468004709),
   (-62975790876927811639458, -906959474426),
   (-62033039516503905819729, -879721315226),
   (-61090288156080000000000, -852759500192),
   (-60147536795627811639458, -826079074801),
   (-59204785435203905819729, -799681587767),
   (-58262034074780000000000, -773575996442),
   (-57319282714327811639458, -747768026041),
   (-56376531353903905819729, -722265306986),
   (-55433779993480000000000, -697072733722),
   (-54491028633027811639458, -672199759010),
   (-53548277272603905819729, -647651877581),
   (-52605525912180000000000, -623439842197),
   (-51662774551727811639458, -599569151692),
   (-50720023191303905819729, -576049151036),
   (-49777271830880000000000, -552880518121),
   (-48834520470427811639458, -530072927933),
   (-47891769110003905819729, -507634469508),
   (-46949017749580000000000, -485573333200),
   (-46006266389127811639458, -463900829743),
   (-45063515028703905819729, -442622981442),
   (-44120763668280000000000, -421750659162),
   (-43178012307827811639458, -401292540978),
   (-42235260947403905819729, -381256636187),
   (-41292509586980000000000, -361653308326),
   (-40349758226527811639458, -342488656258),
   (-39407006866103905819729, -323768255259),
   (-38464255505680000000000, -305504038954),
   (-37521504145227811639458, -287705208040),
   (-36578752784803905819729, -270383778029),
   (-35636001424380000000000, -253546807611),
   (-34693250063927811639458, -237205576877),
   (-33750498703503905819729, -221367826705),
   (-32807747343080000000000, -206046251939),
   (-31864995982627811639458, -191246139438),
   (-30922244622203905819729, -176981583680),
   (-29979493261780000000000, -163250414991),
   (-29036741901327811639458, -150066104938),
   (-28093990540903905819729, -137434967823),
   (-27151239180480000000000, -125366910540),
   (-26208487820027811639458, -113870582367),
   (-25265736459603905819729, -102948668152),
   (-24322985099180000000000, -92610332828),
   (-23380233738727811639458, -82858007738),
   (-22437482378303905819729, -73696734059),
   (-21494731017880000000000, -65128907570),
   (-20551979657427811639458, -57150287868),
   (-19797778569100000000000, -51231970024),
   (-19609228297003905819729, -49753362785),
   (-18666476936580000000000, -42943685082),
   (-17723725576127811639458, -36709779091),
   (-16780974215703905819729, -31050122687),
   (-15838222855280000000000, -25949437540),
   (-14895471494827811639458, -21398641817),
   (-13952720134403905819729, -17382918348),
   (-13009968773980000000000, -13884447751),
   (-12067217413527811639458, -10870882130),
   (-11124466053103905819729, -8316444665),
   (-10181714692680000000000, -6179150977),
   (-9238963332227811639458, -4430603370),
   (-8296211971803905819729, -3035102064),
   (-7353460611380000000000, -1959814265),
   (-6410709250927811639458, -1168370397),
   (-5467957890503905819729, -623808476),
   (-4525206530080000000000, -285334049),
   (-3582455169627811639458, -108372879),
   (-2639703809203905819729, -43445429),
   (-1414127040650000000000, -39524337),
   (-848476224390000000000, -2714602),
   (0, 0)]

/-- The ε = 0.0025 family shape on `[x_½, ∞)`: 73 knots. -/
def eps0025 : Shape where
  Dx := 28282540813000000000000
  Dy := 1000000000000
  ks := h0025 :: t0025

/-- The finite check passes: `x` strictly increasing, `y` nondecreasing. -/
theorem eps0025_ok : eps0025.ok = true := by decide

/-- The first knot sits at height `−1`, by construction of `x_½`. -/
theorem eps0025_yr_head : eps0025.yr h0025 = -1 := by
  simp only [Shape.yr, h0025, eps0025]
  norm_num

/-- **The `u`-branch input of Lemma C-flat, ε = 0.0025.**  This is
`TieBand.yhat_ge_neg_one` with `ŷ := eps0025.eval`, both of its hypotheses
supplied — so residue (ii) of §6.11 is discharged for this shape. -/
theorem eps0025_ge_neg_one {s : ℝ} (hs : 0 ≤ s) :
    (-1 : ℝ) ≤ eps0025.eval (eps0025.xr h0025 + s) :=
  RevPebbling.TieBand.yhat_ge_neg_one
    (Shape.eval_monotoneOn eps0025_ok (eps0025.xr h0025))
    (by rw [Shape.eval_head (rest := t0025) eps0025_ok rfl]; exact eps0025_yr_head) hs

/-- The half-way knot `(x_½, −1)` of the ε = 0.002 shape (anchor `b1470fix.cfg`, `a = 267/800`, `S₀ = 1470`). -/
def h002 : ℤ × ℤ := (-23144099045578347445472, -1000000000000)

/-- The 116 cfg knots of the ε = 0.002 shape strictly to the right of `x_½`. -/
def t002 : List (ℤ × ℤ) :=
  [(-23030785796089966206179, -990287435758),
   (-22766822635100000000000, -967863365992),
   (-22700831844859932412358, -962257352286),
   (-22370877893620000000000, -934486664399),
   (-22271891708250000000000, -926234365793),
   (-22040923942389966206179, -906979016609),
   (-21776960781400000000000, -885189225201),
   (-21710969991159932412358, -879741781640),
   (-21381016039920000000000, -852780934547),
   (-21282029854550000000000, -844777106142),
   (-21051062088689966206179, -826101522875),
   (-20787098927700000000000, -804984378634),
   (-20721108137459932412358, -799705097503),
   (-20391154186220000000000, -773600618050),
   (-20292168000850000000000, -765858570635),
   (-20061200234989966206179, -747793812107),
   (-19797237074000000000000, -727392607957),
   (-19731246283759932412358, -722292312581),
   (-19401292332520000000000, -697101016523),
   (-19302306147150000000000, -689639518922),
   (-19071338381289966206179, -672229379421),
   (-18807375220300000000000, -652592189772),
   (-18741384430059932412358, -647682898864),
   (-18411430478820000000000, -623472330604),
   (-18312444293450000000000, -616311576974),
   (-18081476527589966206179, -599603176610),
   (-17817513366600000000000, -580788457451),
   (-17751522576359932412358, -576084785132),
   (-17421568625120000000000, -552917837501),
   (-17322582439750000000000, -546076081403),
   (-17091614673889966206179, -530112012300),
   (-16827651512900000000000, -512162717463),
   (-16761660722659932412358, -507675402336),
   (-16431706771420000000000, -485616201910),
   (-16332720586050000000000, -479115049298),
   (-16101752820189966206179, -463945725891),
   (-15837789659200000000000, -446925138023),
   (-15771798868959932412358, -442670000914),
   (-15441844917720000000000, -421799902379),
   (-15342858732350000000000, -415663154333),
   (-15111890966489966206179, -401344113109),
   (-14847927805500000000000, -385317331465),
   (-14781937015259932412358, -381310647377),
   (-14451983064020000000000, -361709873928),
   (-14352996878650000000000, -355961267934),
   (-14122029112789966206179, -342547897080),
   (-13858065951800000000000, -327573807270),
   (-13792075161559932412358, -323830297824),
   (-13462121210320000000000, -305569015768),
   (-13363135024950000000000, -300230273536),
   (-13132167259089966206179, -287773257875),
   (-12868204098100000000000, -273918676600),
   (-12802213307859932412358, -270455046221),
   (-12472259356620000000000, -253621446370),
   (-12373273171250000000000, -248720119068),
   (-12142305405389966206179, -237283745611),
   (-11878342244400000000000, -224616489281),
   (-11812351454159932412358, -221449692360),
   (-11482397502920000000000, -206131989359),
   (-11383411317550000000000, -201693152458),
   (-11152443551689966206179, -191335931734),
   (-10888480390700000000000, -179927668674),
   (-10822489600459932412358, -177075622624),
   (-10492535649220000000000, -163348901424),
   (-10393549463850000000000, -159394983228),
   (-10162581697989966206179, -150169249201),
   (-9898618537000000000000, -140068223886),
   (-9832627746759932412358, -137542990203),
   (-9502673795520000000000, -125480041744),
   (-9403687610150000000000, -122032722545),
   (-9172719844289966206179, -113989064012),
   (-8908756683300000000000, -105255994618),
   (-8842765893059932412358, -103072753282),
   (-8512811941820000000000, -92740286456),
   (-8413825756450000000000, -89816403014),
   (-8182857990589966206179, -82994107408),
   (-7918894829600000000000, -75670213932),
   (-7852904039359932412358, -73839270444),
   (-7522950088120000000000, -65278185088),
   (-7423963902750000000000, -62886683014),
   (-7192996136889966206179, -57306625336),
   (-6929032975900000000000, -51394195107),
   (-6863042185659932412358, -49916121874),
   (-6533088234420000000000, -43109326589),
   (-6434102049050000000000, -41240090158),
   (-6203134283189966206179, -36878669239),
   (-5939171122200000000000, -32353818320),
   (-5873180331959932412358, -31222645019),
   (-5543226380720000000000, -26125993739),
   (-5444240195350000000000, -24762046328),
   (-5213272429489966206179, -21579652564),
   (-4949309268500000000000, -18370953656),
   (-4883318478259932412358, -17561947665),
   (-4553364527020000000000, -14035795437),
   (-4454378341650000000000, -13125378065),
   (-4223410575789966206179, -11001899045),
   (-3959447414800000000000, -8943693513),
   (-3893456624559932412358, -8429348922),
   (-3563502673320000000000, -6275918690),
   (-3464516487950000000000, -5746865916),
   (-3233548722089966206179, -4512995056),
   (-2969585561100000000000, -3386230966),
   (-2903594770859932412358, -3104686167),
   (-2573640819620000000000, -2017988108),
   (-2474654634250000000000, -1777381105),
   (-2243686868389966206179, -1216378854),
   (-1979723707400000000000, -773401538),
   (-1913732917159932412358, -662760604),
   (-1583778965920000000000, -316217905),
   (-1484792780550000000000, -260885308),
   (-1253825014689966206179, -132068722),
   (-989861853700000000000, -74945239),
   (-923871063459932412358, -60737480),
   (-494930926850000000000, -49524337),
   (-296958556110000000000, -2714602),
   (0, 0)]

/-- The ε = 0.002 family shape on `[x_½, ∞)`: 117 knots. -/
def eps002 : Shape where
  Dx := 9898618537000000000000
  Dy := 1000000000000
  ks := h002 :: t002

/-- The finite check passes: `x` strictly increasing, `y` nondecreasing. -/
theorem eps002_ok : eps002.ok = true := by decide

/-- The first knot sits at height `−1`, by construction of `x_½`. -/
theorem eps002_yr_head : eps002.yr h002 = -1 := by
  simp only [Shape.yr, h002, eps002]
  norm_num

/-- **The `u`-branch input of Lemma C-flat, ε = 0.002.**  This is
`TieBand.yhat_ge_neg_one` with `ŷ := eps002.eval`, both of its hypotheses
supplied — so residue (ii) of §6.11 is discharged for this shape. -/
theorem eps002_ge_neg_one {s : ℝ} (hs : 0 ≤ s) :
    (-1 : ℝ) ≤ eps002.eval (eps002.xr h002 + s) :=
  RevPebbling.TieBand.yhat_ge_neg_one
    (Shape.eval_monotoneOn eps002_ok (eps002.xr h002))
    (by rw [Shape.eval_head (rest := t002) eps002_ok rfl]; exact eps002_yr_head) hs

#print axioms Shape.eval_mono
#print axioms Shape.eval_head
#print axioms eps0035_ge_neg_one
#print axioms eps003_ge_neg_one
#print axioms eps0025_ge_neg_one
#print axioms eps002_ge_neg_one

end RevPebbling.ShapeMonotone
