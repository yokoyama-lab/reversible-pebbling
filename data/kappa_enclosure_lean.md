# `κ*` enclosed inside Lean — report

Companion to `RevPebbling/KappaEnclosure.lean` and its generator
`scripts/gen_kappa_enclosure.py`.  Written 2026-08-22.

**Stated before measuring anything** — what would be true when this was
done: *the sixteen decimal digits of `c` are fixed inside Lean, with the
two hypotheses `Final.lean` carries from `rocq/KappaStar.v` discharged.*
That is what happened; the enclosure reached is exactly `Final.KHI` and
`Final.KLO`, not a weaker one.

---

## 1. The route, and why (決めた経路と理由)

Three routes were on the table.  The first two were rejected on measured
or arithmetic grounds before any Lean was written.

**(a) Integer-power comparison (`CriticalRootRat`) — dead.**  It turns
`x ≤ s^{m/n}` into `x^n ≤ s^m`, one `decide`, and is why the rational
family reached 8826-digit certificates cheaply.  It cannot reach `κ*`.
The obstruction is not the witness slope's sixteen-digit denominator by
itself (one can pick a shorter rational `q`, since `V` is flat to second
order at `q*`), but the *conversion* `ρ ≤ 2^{m/n}`: pinning `log₂ρ` to
`10⁻¹⁶` needs a continued-fraction denominator `n ≈ 10⁸`, hence a
certificate `B^n` of about `2·10⁹` digits.  Roughly twelve digits is the
practical ceiling of that route (`n ≈ 10⁶`, `2·10⁷`-digit certificates).

**(b) Transcribing the Rocq route — dead without a Taylor model.**
`rocq/KappaStar.v` reduces `V q ≤ K` to the sign of `g` at `2^{1/q−K}`,
a closed form, then calls `interval with (i_bisect q, i_taylor q, …)`.
The `i_taylor` is not decoration: at `q*` the expression is *tangent* to
zero, so a naive interval evaluation loses the cancellation between the
two factors and its width stays `O(h)` instead of `O(h²)`.  With a
margin of `8·10⁻¹⁷` that costs on the order of `10¹⁶` boxes.  Lean has
neither the tactic nor the Taylor model.

**(c) Gibbs' inequality plus convexity — taken.**  The tangency is not
removed but *relocated* into a place where an exact inequality does the
work of interval arithmetic.

At a root, `ρ^{−q} + (1+ρ)^{−q} = 1` is **Kraft's inequality** for two
codeword lengths `ℓ₁ = log ρ`, `ℓ₂ = log (1+ρ)`.  Weighted AM–GM
(`Real.geom_mean_le_arith_mean2_weighted`, standing hypotheses
`0 ≤ w₁`, `0 ≤ w₂`, `0 ≤ p₁`, `0 ≤ p₂`, `w₁ + w₂ = 1`) against any
weight `θ ∈ (0,1)` gives `H(θ) ≤ q·(θℓ₁ + (1−θ)ℓ₂)`, hence

```
V(q) = 1/q − log₂ρ  ≤  Λ(θ, ρ) = (θ·log ρ + (1−θ)·log (1+ρ))/H(θ) − log ρ/log 2
```

with `H(θ) = −θ log θ − (1−θ) log (1−θ)`.  The implicit root function is
gone: `Λ` depends on `ρ` alone.  Equality holds exactly when `θ` is the
Gibbs weight `ρ^{−q}`, so the family `{Λ(θ,·)}` is tight, and its
envelope is the true `V` curve.

The second piece is that `Λ(θ, ·)` is **convex in `log ρ`**, which is
the superadditivity `1 + ρ₁^λρ₂^{1−λ} ≤ (1+ρ₁)^λ(1+ρ₂)^{1−λ}` — two more
AM–GMs, no derivative (`log_one_add_convex`).  A convex function on an
interval is at most its larger endpoint value, so a **finite grid is a
proof**, and each cell costs two point evaluations rather than an
interval evaluation.  That is what replaces `i_bisect`/`i_taylor`.

The lower bound reads the same inequality backwards.  Fix a rational
weight `a ∈ (1/2,1)` first; with `t = log(1−a)/log a > 1` the equation
`ρ^t = 1+ρ` has a root `ρ > 1`, and `q = −log a/log ρ` makes
`ρ^{−q} = a` and `(1+ρ)^{−q} = 1−a` **exactly**, so `(q,ρ)` is a genuine
point of the root curve with `V(q) = log ρ·(−1/log a − 1/log 2)`.  A
rational lower bound `B ≤ ρ` needs only `t·log B ≤ log (1+B)`, because
`x ↦ t log x − log (1+x)` is strictly increasing for `t > 1`
(elementary: `log(1+y) − log(1+x) ≤ log y − log x`).  No covering at all.

The one numerical primitive is `log_enclose`: Mathlib's
`Real.abs_log_sub_add_sum_range_le` (standing hypothesis `|x| < 1`) read
as a rational bracket for `Real.log` of a rational, with range reduction
by powers of two.  `exp_enclose` (from `Real.exp_bound`, standing
hypothesis `|x| ≤ 1`) is used twice, only for the last line.

## 2. Digits reached, and the theorems (届いた桁数と定理名)

**Sixteen digits — the full Rocq interval, not a weaker one.**

| theorem | statement |
|---|---|
| `KappaEnclosure.kappaStar_le_hi` | `κ* ≤ 0.3317423792563106` |
| `KappaEnclosure.kappaStar_ge_lo` | `0.3317423792563105 ≤ κ*` |
| `KappaEnclosure.kappaStar_enclosure` | both |
| `KappaEnclosure.kappaUpperBound_KHI` | `Final.KappaUpperBound Final.KHI` |
| `KappaEnclosure.kappaAttained_KLO` | `Final.KappaAttained Final.KLO` |
| `KappaEnclosure.c_bracket_unconditional` | `2^(1+KLO) ≤ c ≤ 2^(1+KHI)` |
| `KappaEnclosure.c_decimal_bracket` | `2.517064836893816 ≤ c ≤ 2.517064836893817` |

The last two were `Final.c_bracket_of_rocq` applied to hypotheses, and
`rocq/KappaStar.v`'s `c_bracket_of_kappa`, respectively.  The manifest's
statement audit now reports `KappaUpperBound RevPebbling.Final.KHI` and
`KappaAttained RevPebbling.Final.KLO` as **PROVED**, where before they
were carried with no `PROVED by`.

`#print axioms` on all seven: `propext`, `Classical.choice`,
`Quot.sound` only.  No `native_decide`, no `sorry`, no `axiom`.

Margins actually achieved (exact rational arithmetic, from the
generator): the worst endpoint check comes out at `0.33174237925631056`
against `KHI = 0.3317423792563106`; the lower bound clears `KLO` by
`1.986·10⁻¹⁷`.  `κ*` itself is `0.33174237925631051986…`, so both ends
are within `10⁻¹⁶` of the truth by construction and there is no slack to
spare — see the mutation results.

## 3. The covering (区間の個数と各区間で使った評価)

**34 intervals over `ρ ∈ [1, 9/5]`, plus one tail lemma for `ρ ≥ 9/5`.**
(`cover0 … cover33`, `coverTail`; the case analysis is in `V_le_KHI'`.)

Each interval carries its own weight `θⱼ` and needs, per endpoint:

* an enclosure of `log ρ` (both sides — the lower side feeds `log₂ρ`),
* an upper bound for `log (1+ρ)`,
* upper bounds for `log θⱼ` and `log (1−θⱼ)` (these bound `H(θⱼ)` from
  **below**, which is what the division needs),
* an upper bound for `log 2`.

and then one rational inequality (`Lam_le_of_bounds`).  **No
monotonicity argument and no Lipschitz constant is used anywhere**: the
interior of each cell is handled by convexity, which is exact, so the
only numerical inputs are the endpoint values.  This is the substantive
difference from an interval-arithmetic cover, where the interior costs
width.

Sizes: 219 log enclosures in the table (68 endpoint checks share them),
series lengths from **18 to 87 terms**, each targeted at `10⁻²²`;
`ρⱼ` needs at most 12 decimals and `θⱼ` at most 9.  Interval widths run
from `4·10⁻¹¹` at the tangency to `0.36` at the far end — the geometric
refinement near `ρ* = 1.25540834…` is the entire cost of the tangency.

Measured growth of the covering with the target margin (float design,
greedy maximal steps): `10⁻⁴` → 7 intervals, `10⁻⁶` → 11, `10⁻⁸` → 16,
`10⁻¹⁰` → 20, `10⁻¹²` → 24, and `8·10⁻¹⁷` (the real target, with a 3 %
back-off and rounded endpoints) → 34.  About two intervals per decimal
digit.

The tail is `Λ(1/2, ρ) = ½·log₂(1 + 1/ρ)`, decreasing, so `ρ ≥ 9/5`
needs one number: `log (14/9)/(2 log 2) = 0.3187… < KHI`.

Cost: `lake env lean` on the 2921-line file takes **26 s wall**
(207 s CPU, elaborated in parallel); the `.olean` is 31.6 MB.  Nothing
upstream is touched, so the two-and-a-quarter-hour parts of the build
are unaffected.

## 4. Mutation injection (変異注入の結果)

Seven injections, each of which **must** break the file, plus the
unmutated control.  Each run is `lake env lean` on a copy.

| # | injection | result |
|---|---|---|
| M1 | `KHI'` lowered by `10⁻¹⁶` (i.e. to `KLO`'s value) | **caught** — 5 errors: `KHI'_eq` plus three endpoint checks near `ρ*` |
| M2 | `KLO'` raised by `2·10⁻¹⁶` | **caught** — 2 errors: `KLO'_eq` and the final assembly of `kappaStar_ge_lo` |
| M3 | `θ` of interval 17 shifted by `10⁻⁵` | **caught** — 4 errors: the endpoint check, then `cover17` |
| M4 | one log-table lower bound (`lgv102`) raised by `10⁻²⁰` | **caught** — 1 error, inside that entry's `log_enclose` |
| M5 | `θ = 1/2` tail started at `3/2` instead of `9/5` | **caught** — 2 errors: the tail's numeric check, then `coverTail`'s use |
| M6 | decimal lower end of `c` raised past the enclosure | **caught** — `unsolved goals` in the `calc`'s numeric step |
| M7 | `expXlo`'s claimed lower bound raised by `10⁻¹⁶` | **caught** — 1 error, inside that entry's `exp_enclose` |
| M0 | control, unmutated | **0 errors** |

M1 is the informative one: only *three* of the 68 endpoint checks have
more than `10⁻¹⁶` of slack, which is the quantitative statement that the
grid is not over-engineered.  M4 and M7 show the log and exp tables are
load-bearing rather than decorative — a constant `10⁻²⁰` off is caught.

**One injection did nothing at first, and the control is what showed
it.**  M6's original `sed` pattern was written against
`2517064836893816 / 1000000000000000`, but `Fraction` had reduced that
numeral on emission to `314633104611727 / 125000000000000`, so the
pattern matched nothing and the "mutant" was byte-identical to the
control — 0 errors, which would have read as *survived* if the control
had not also been 0.  The generator now emits the two headline decimals
unreduced (they are the numbers the paper quotes, so the readable form
is worth the special case), and M6 was rerun against the real numeral.

## 5. Not done (まだやっていないこと)

* **The Zone I/II ledger is untouched.**  `rocq/` is still needed, and
  still load-bearing, for the *upper-bound programme*'s constants
  (`LedgerCover*`, `EminEps`, `KappaStar.v`'s neighbours).  What this
  file removes is the dependence on Rocq **for the value of `κ*` and
  hence of `c`** — nothing else.  `rocq/KappaStar.v` is now an
  independent second check of the same interval.
* **No interval-arithmetic library was built.**  `log_enclose` and
  `exp_enclose` are two lemmas, and the covering is hand-designed around
  one specific convexity.  A different function would need its own
  monotone/convex structure; nothing here generalises to a tactic.
* **The grid design step is not itself certified.**  It runs in
  `Decimal`.  This is safe by construction — a bad grid can only make
  the emitted file fail to compile, never make it prove something false,
  and every emitted inequality is re-verified in exact `Fraction`
  arithmetic before being written — but the *search* is not a proof.
* **The repository's two remaining carried hypotheses are untouched**:
  `Superadd f` (3 theorems, front-DP layer, does not reach `c`) and
  `Submult RevPebbling.RLEPebble.fRLE` (1 theorem, `c ≤ 2.6106`).
* **The paper repository was not updated.**  `ieice_letter.tex` (in
  `~/dev/overleaf/2026_exact_reversible_pebbling`) still quotes an older
  theorem count and still describes the `κ*` enclosure as carried from
  Rocq.  Both are now wrong; `check_claims.py` cannot see that
  repository, which is the structural gap already recorded in the
  working notes.
* **`scripts/check_claims.py` still does not scan `rocq/`.**  Unchanged
  by this work.
* **The local working notes (`CLAUDE.md`, not tracked) were left alone.**
  Their "current state" block still lists the `κ*` enclosure as carried
  from Rocq and still names `AnchorCertify4798.c_bracket_sharp` as the
  sharp bracket; another session may be reading that file, so it was not
  edited here.

## 6. What more digits would need (16 桁に要るもの — 達成済み、その先)

Sixteen digits was the target and was reached, so this section is about
the *next* digits.  Nothing in the construction saturates:

* the covering grows by about two intervals per decimal digit (measured,
  §3), so 24 digits is ≈ 50 intervals and 32 digits ≈ 66;
* the log enclosures are set at `10⁻²²` and would move to `10⁻³⁰` by
  adding roughly `8/log₁₀(1/|x|)` ≈ 13 more series terms each — the
  numerals grow linearly, and `norm_num` on a 40-term series of 12-digit
  rationals measured at 0.17 s, so the file would stay in the minutes;
* the endpoints `ρⱼ`, `θⱼ` need about `d/2` significant digits, since
  `V` is flat to second order at `q*`.

The real limits are elsewhere: `rocq/KappaStar.v` pins only sixteen
digits, so beyond that there is nothing to check against, and the
published constant `c = 2.517064836893816…` is quoted to sixteen.  The
*sharper* open question is not more digits of `κ*` but the upper-bound
programme (Zone I/II), where the constants are still established at
sampled points rather than on the continuum.

Two things would genuinely need new machinery rather than more of the
same:

1. a **closed form** for `κ*` — ruled out numerically (400-digit PSLQ
   finds no algebraic number of degree ≤ 12 with coefficients below
   `10³⁰`), so this is not a formalisation problem;
2. a **reusable** rigorous-numerics layer in Lean.  The pattern here —
   an exact convexity that turns a tangency into endpoint evaluations —
   is what made this instance cheap, and it is not automatic.  Getting
   `interval`-like coverage would still mean building Taylor models.
