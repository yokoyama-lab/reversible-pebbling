# `rocq/` — `κ*`, `ρ_c`, and Lemma A's ledger, inside a prover

`data/kappa_enclosure_certified.txt` records a 23-digit enclosure of

```
κ* = sup_{q>0} V(q),   V(q) = 1/q − log₂ ρ_c(q),
```

where `ρ_c(q)` is the unique root of `ρ^(−q) + (1+ρ)^(−q) = 1`.  That
enclosure is rigorous — every step is an Arb ball operation, and the
critical point is certified by a Krawczyk operator over 602 adaptive
boxes — but it runs **outside any prover**.  The conjectured exact
growth rate `c = 2^(1+κ*) = 2.5170648369` therefore rested on a program
nobody had proof-checked.

`KappaStar.v` replaces that with a machine-checked enclosure.  It is
written for **Rocq** rather than Lean because the proof needs rigorous
interval arithmetic over the reals, and CoqInterval provides it; Lean 4
has no equivalent.

## What is proved

| theorem | statement |
|---|---|
| `kappa_upper` | `0 < q → 0 < r → g q r = 0 → V q r ≤ 0.3317423792563106` |
| `kappa_lower` | `∃ r, 0 < r ∧ g Q0 r = 0 ∧ 0.3317423792563105 ≤ V Q0 r` |
| `c_bracket_of_kappa` | `KLO ≤ k ≤ KHI → 2.517064836893816 ≤ 2^(1+k) ≤ 2.517064836893817` |

with `g q r = r^(−q) + (1+r)^(−q) − 1` and `V q r = 1/q − ln r / ln 2`.
Together:

```
κ* ∈ [0.3317423792563105, 0.3317423792563106]
c  ∈ [2.517064836893816,  2.517064836893817]
```

The Arb certificate says `c = 2.51706483689381612057…`, inside this
window.  `ρ_c` is never constructed as a function: `kappa_upper`
quantifies over an arbitrary root, and the root `kappa_lower` needs is
produced by the intermediate value theorem (`IVT_interv`).

## How the implicit function disappears

`g q ·` is strictly decreasing (`g_decr`), so for the root `ρ_c(q)`

```
V q r ≤ K   ⟺   r ≥ 2^(1/q − K)   ⟺   0 ≤ g q (2^(1/q − K)),
```

and `g` at that test point has the closed form (`g_test`)

```
g q (2^(1/q − K)) = 2^(qK − 1) · (1 + (1 + 2^(K − 1/q))^(−q)) − 1,
```

an explicit one-variable expression.  So no Krawczyk operator, no
saddle system, no Jacobian — the whole global-supremum problem becomes
one inequality in `q`, in three ranges:

| range | how |
|---|---|
| `0 < q ≤ 2/5` | elementary (`tail_low`): `(1+e)^(−q) ≥ 1 − qe` and `2^(qK) ≥ 1 + qK ln 2`, with `e = 2^(K−1/q) ≤ 2^(K−5/2)` |
| `2/5 ≤ q ≤ 302/100` | `interval with (i_bisect q, i_taylor q, i_prec 200, i_depth 80)` (`core_mid`) |
| `302/100 ≤ q` | elementary (`root_gt_1`): every root exceeds 1 because `g q 1 = 2^(−q) > 0`, so `V q r < 1/q ≤ 100/302 < KHI` |

Only the middle range uses interval arithmetic, and the margin there is
about `8·10⁻¹⁸` at `q* ≈ 1.5154`, where the constraint is tangent.

## Trust base

`Print Assumptions` on the main theorems lists only:

- `ClassicalDedekindReals.*`, `Classical_Prop.*`, `FunctionalExtensionality.*`
  — the axioms of Rocq's classical reals, unavoidable for `R`;
- `PrimInt63`/`Uint63Axioms`/`Sint63Axioms`, `PrimFloat`/`FloatAxioms`,
  `PrimArray` — Rocq's *primitive* machine integers, IEEE-754 floats and
  arrays, axiomatised by their specifications.  CoqInterval computes its
  enclosures with these.  (`Sint63Axioms` appears only in the cover.)

There is no `admit`, no `Axiom`, and nothing of the "trust what this
compiled program printed" kind (the Lean side's `native_decide`).  The
float axioms state the IEEE-754 semantics of the hardware operations;
the interval algorithm built on top of them is proof-checked.

## `RhoEnclose.v` — the value layer

`KappaStar.v` needs `ρ_c` only through a sign test, so it never says what
`ρ_c(q)` *is*.  Zone I of the one-step appendix does need values: its
ledger is built from `f(q) = q log₂ ρ_c(q)` at three slopes.
`RhoEnclose.v` supplies

```
rho_in : q ∈ [qlo,qhi] ∧ g q r = 0  →  a ≤ r ≤ b
```

from two sign tests at the corners.  The mechanism is that `g` is
antitone in **both** arguments — in `ρ` that is `g_decr`, in `q` it holds
as soon as `r > 1` (both bases exceed 1), and every root does exceed 1
(`root_gt_1`).  So monotonicity in `q` replaces interval Newton and
Krawczyk here as well.

| corollary | content |
|---|---|
| `rho_window_qstar` | `q ∈ [1.5, 1.53] → ρ ∈ [1.249, 1.262]` |
| `rho_window_zoneI` | `q ∈ [0.35, 3.2] → ρ ∈ [1.034, 6.77]` |
| `f_window_qstar` | `q ∈ [1.5, 1.53] → f ∈ [0.481, 0.515]` |
| `rho_c_at_1` | `g 1 r = 0 → r² = r + 1` — `ρ_c(1)` is the golden ratio, in closed form |

## `LedgerParam.v` — `β` without a derivative

Lemma A's ledger sits at a point where the E-branch slope is `q₁`, and
`β` is tied to `q₁` by the tangency `f'(q₁) = ε − β`.  That equation was
the **only** place a derivative entered, and formalising it would need
the implicit function theorem for `ρ_c`.

It is avoidable.  The tangency is a consequence of a derivative-free
fact: `E` is the lower envelope of the lines `q ↦ q b + f(q)`, so `q₁`
minimises that family at `b = β − ε`.  Minimality alone brackets `b` by
**difference quotients of `f`**:

```
q = q₁ + h :  q₁b + f(q₁) ≤ (q₁+h)b + f(q₁+h)  ⟹  b ≥ (f(q₁) − f(q₁+h))/h
q = q₁ − h :  q₁b + f(q₁) ≤ (q₁−h)b + f(q₁−h)  ⟹  b ≤ (f(q₁−h) − f(q₁))/h
```

Both endpoints are *values* of `f`, which `RhoEnclose` already encloses.

| theorem | content |
|---|---|
| `root_exists` | `0 < q → ∃ r, 1 < r ∧ g q r = 0` — a root at **every** slope, by IVT between `1` and `2^(1/q)` |
| `EminRel` | minimality of the `q₁`-line, stated over roots (no constructed `ρ_c`) |
| `beta_bracket` | the two-sided bound above, from minimality alone |
| `bracket_at_1_5` | worked: `q₁ = 3/2`, `h = 1/100` ⟹ `b ∈ [0.33361, 0.33601]`; the true `−f'(3/2) = 0.334769` |

**Measured before building this.** A probe over Zone I put the bracket
at width ≈ `2·10⁻⁴` for `h = 10⁻³`, and the ledger's minimum over
*every* `β` in *every* bracket came out `0.011749` against `0.011758`
for the derivative-based version — a loss of 0.07% **at a point**.

**Corrected (measured afterwards).** That 0.07% is the pointwise loss.
A machine-checked Zone I proof must cover *windows* of `q₁`, and there
the derivative-free bracket is not enough:

- `w₁ = 1/(1 + 2^(−μ(S_λ − E)))` with `μ = 30`, so an uncertainty `db`
  in `β` becomes ≈ `20·db` in `w₁`; and the ledger is **not** uniform in
  `w₁` (at `q₁ = 3.0` it is `+0.021` at the true `w₁ = 0.939` but
  reaches `−0.015` at `w₁ = 0.5`).  So `β` must be pinned to ≈ `3·10⁻⁴`.
- Over a window of width `W` the difference-quotient bracket costs
  `|f''|h/2` intrinsically and amplifies the window's own `f`-width by
  `1/h`, giving ≈ `0.26√W` — the **square root** of the window width.
  With the tangency instead it is `|f''|W`, **linear**.  Measured at
  `q₁ = 2.4`: `W = 10⁻³` → `2.09·10⁻²` versus `1.26·10⁻⁴` (166×);
  `W = 10⁻⁶` → `6.55·10⁻⁴` versus `1.26·10⁻⁷` (5185×).
- To reach `3·10⁻⁴`: derivative-free needs `W ≈ 10⁻⁷`, about **30
  million windows** over `[0.35, 3.2]`; with `f'`, `W ≈ 2·10⁻³`, about
  **1400**.

So `beta_bracket` is sound and stays useful, but a window-based Zone I
proof needs the implicit function theorem for `ρ_c` after all — not for
correctness, for tightness.  Details in
`scripts/probe_brw/m43_zone1_windows.py` in the paper repository.

**Still open** for a Zone I proof, in order: (i) `f'` by the implicit
function theorem, giving `β` linearly in the window width; (ii)
assembling `q₂`, `S_λ`, `G`, the softmin weight and the chord deficit
into the ledger; (iii) covering `[0.35, 3.2]` at `W ≈ 2·10⁻³`.  Every
ingredient other than `f'` is already an explicit expression in
enclosed quantities.

## `EnvelopeE.v` — the E-branch of the profile

Both zones are built on the Legendre transform

```
E(β) = min_{q>0} ( qβ + f(q) ),    f(q) = q log₂ ρ_c(q).
```

The two global bounds it needs are **already theorems**, rewritten:

| bound | is | rewriting of |
|---|---|---|
| `f_ge_global` | `1 − q·KHI ≤ f(q)` | `kappa_upper` with the quotient cleared |
| `f_le_one` | `f(q) ≤ 1` | `g_at_top` — every root is below `2^(1/q)` |

From `1 − q·κ* ≤ f(q) ≤ 1`, with no new numerics:

| theorem | content |
|---|---|
| `E_ge_one` | `β ≥ κ* → E(β) ≥ 1` — past `κ*` the E-branch is **at the ceiling** |
| `E_le_one_plus` | …and 1 is approached, so that bound is sharp |
| `E_lower_ratio` | `0 < β ≤ κ* → E(β) ≥ 3β` — split the family at `q = 3`; `1 − 3κ* = 0.0048 > 0` makes both branches clear `3β` |

`E_ge_one` is why the profile is `min(E, 1)` past `κ*` — the cap the
appendix's `S_λ` mollifies — and it comes straight out of the `κ*`
enclosure, so that work is not an island.  `E_lower_ratio` needs **no
interval arithmetic at all** and loses half a percent at `β = κ*`.

## `RhoDeriv.v` — `ρ_c` as a function, and the partials of `g`

The measurement above says the tangency is needed, and a derivative
needs a *function*, so this file finally constructs one.  `IVT_interv`
already returns a `sig`, so `root_sig` loses nothing and

```
rhoc q = proj1_sig (root_sig q H)   for q > 0,   1 otherwise.
```

| theorem | content |
|---|---|
| `rhoc_spec` | `0 < q → 1 < rhoc q ∧ g q (rhoc q) = 0` |
| `rhoc_unique` | `g q r = 0 → r = rhoc q` — strict monotonicity leaves no room |
| `rhoc_in` | every enclosure proved over roots transfers to `rhoc` |
| `rhoc_continuous` | squeeze the root between two levels whose strict signs survive a small move in `q` |
| `derive_g_q` | `∂g/∂q = −ln r·r^(−q) − ln(1+r)·(1+r)^(−q)` |
| `derive_g_r` | `∂g/∂r = −q·r^(−q)/r − q·(1+r)^(−q)/(1+r)` |
| `derive_g_r_neg` | that partial is **strictly negative** — the nondegeneracy the implicit function theorem needs |

`Rpower` has no derivative lemma in Rocq's standard library, so both
partials are built from `exp` and `ln` by the chain rule
(`derive_Rpower_q`, `derive_Rpower_r`).

**Not yet done:** the implicit function theorem itself — the limit
argument that turns these partials into
`is_derive rhoc q (−∂_q g / ∂_r g)`.  All its ingredients are in place:
the function, its continuity, both partials, and the nonvanishing
denominator.

## `SlopeWindow.v` — the window slope, still without differentiating

**The measurement above was right about the arithmetic and wrong about
the remedy.**  The `1/h` amplification comes from evaluating `f` over the
*whole* window and then dividing.  Bracket at the two **endpoints**
instead — single points, where `f` is known to interval precision, so
the amplified term is ≈ `10⁻²⁵/h ≈ 0` — and transport to the interior by
monotonicity.

The monotonicity is free.  Adding two minimality statements against each
other,

```
q₁b₁ + f(q₁) ≤ q₂b₁ + f(q₂)
q₂b₂ + f(q₂) ≤ q₁b₂ + f(q₁)
───────────────────────────
(q₁ − q₂)(b₁ − b₂) ≤ 0
```

so the optimal slope is **antitone in the minimiser** — Topkis's
monotone comparative statics, two applications of the hypothesis and one
`nra`.  No derivative, no convexity, no smoothness.

| theorem | content |
|---|---|
| `topkis` | `(q₁ − q₂)(b₁ − b₂) ≤ 0` between any two minimisers |
| `slope_window` | `qa < q₁ < qb` ⟹ `b(qb) ≤ b(q₁) ≤ b(qa)` |
| `slope_in_24_26` | worked: every minimiser in `(2.4, 2.6)` has slope in `[0.163568, 0.187434]`, width **0.0239** — against **0.116** for the across-the-window bracket |

Measured widths at `q = 2.4` with endpoint brackets at `h = 10⁻⁸`:
`W = 10⁻²` → `1.26·10⁻³`; `W = 10⁻³` → `1.26·10⁻⁴`; `W = 10⁻⁴` →
`1.26·10⁻⁵`.  **Linear in `W`**, matching what the derivative gives, so
`W ≈ 2·10⁻³` and about **1400 windows** — the figure the previous
section attributed to the derivative route.

**Range.** Antitonicity holds between genuine *minimisers*.  Where `f`
is concave (`q ≲ 0.5`) a `q` is not a minimiser, and the point bracket
there comes out **empty** (at `q = 0.6, h = 10⁻⁴` its lower end exceeds
its upper by `2.4·10⁻⁵`) — a machine-checkable certificate rather than a
gap.  The slopes that actually occur in Zone I are `q ∈ [1.42, 3.25]`,
matching the appendix; and past `β = κ* + ε` the E-branch is above the
ceiling, where `E_ge_one` takes over.  Details in
`scripts/probe_brw/m44_slope_window.py`.

**`RhoDeriv.v` is therefore off the critical path.**  Its contents
(`rhoc` as a function, uniqueness, continuity, both partials of `g`,
nondegeneracy) are proved and kept — they are the natural interface if
the implicit function theorem is ever wanted — but Zone I no longer
needs them.

## `LedgerA.v` — the ledger, assembled and closed on a window

The appendix reduces Zone I to the **ledger**

```
δ̃ ≥ w₁q₁ε + w₂(q₂ε + G) − D  >  0
```

with `q₁` the E-branch slope, `q₂` the S-branch slope, `w₁/w₂` the
soft-min weights, `G` the S-tangent's deficit below the corner, and `D`
the chord deficit of `f`.  This file assembles it and closes it on one
window.

Two departures from the appendix, both to remove objects with no closed
form:

- **parameterise by `q₁`, not `β`** — `E` is the Legendre transform of
  `−f`, so the tangency *is* minimality of the `q₁`-line and the inner
  minimisation disappears;
- **use the true chord deficit** `D = w₁f(q₁) + w₂f(q₂) − f(q̃)` instead
  of `(M/2)w₁w₂(q₁−q₂)²` with `M = sup f''` — `D` is what the proof
  consumes, it is explicit once `f` is, it removes the second derivative
  of an implicit function, and it is 1.45× less lossy.

Together with `SlopeWindow` pinning `b` from the endpoints, **no
derivative appears anywhere**.

| theorem | content |
|---|---|
| `ledger_pos` | given enclosures of every primitive, `0.0085 ≤ ledger` — pure interval arithmetic, and the only part a cover repeats |
| `z_encl` / `q2_of_z` / `G_of_z` / `S_of_z` | `z = λ(κ* − b)`, and `q₂`, `G`, `S` explicit in `z` |
| `f1_encl` / `f2_encl` / `ft_encl` | `f` at the three slopes, each two sign tests on a `ρ`-box of width `10⁻⁹` |
| `w1_encl` / `qt_encl` | the soft-min weight and the composite slope |
| **`window_24`** | **the window `(2.4, 2.4005)` closed end to end: `0.0085 ≤ ledger`** |

The measured enclosure is `[0.00857, 0.01496]`; the theorem claims
`≥ 0.0085`.  Every intermediate quantity is enclosed by kernel-checked
interval arithmetic — `z ∈ [4.331171, 4.333272]`, `q₂ ∈ [1.443661,
1.443761]`, `w₁ ∈ [0.759571, 0.761682]`, `q̃ ∈ [2.167020, 2.175540]`,
and the three `f` values.

**The cover is now done** — see the next section.  (This section's
estimate of 3700 windows assumed a uniform `W = 5·10⁻⁴`.  Measurement
says the ledger's slack varies by an order of magnitude across the
range, so an adaptive grid needs **925**.)

## `CoverGlue.v` + `LedgerCoverP*.v` + `LedgerCover.v` — the cover

`window_24` on a grid, generated by `gen/gencover.py`, and **stronger
than `window_24` in one respect**: the slope bracket is no longer
assumed.  At every node it is derived from three point enclosures of `f`
(`slope_upper` / `slope_lower`, on top of `LedgerParam.beta_bracket`)
and transported to the window by Topkis monotonicity (`slope_closed`).

| theorem | content |
|---|---|
| `slope_upper` / `slope_lower` | the two halves of the slope bracket at a node; the neighbour that does not constrain the side being proved is filled with the free bound `f_le_one` |
| `slope_closed` | the node brackets transported to the **closed** window |
| `ledger_window` | the glue of `window_24` with all 23 constants abstracted |
| `LedgerCoverP<k>.window_<i>` | one window, `i = 0 … 924` |

```
q₁ ∈ [1.45, 3.25]      925 closed windows, 926 nodes, 24 parts
window widths          4·10⁻⁷ … 3.45·10⁻²   (adaptive)
ledger ≥               0.002057   at the tightest window
```

Consecutive windows share a node, so the union is the closed interval —
not a union of open windows that misses its own grid points.
`slope_window` needs `q₁` *strictly* inside, which is why `slope_closed`
splits on the endpoint case instead.

**Why `slope_closed` and not `slope_window`.**  Topkis needs strictness
only in order to divide by `q₁ − qₐ`; at an endpoint the node's own
bracket applies to `b₁` directly.  Splitting on that case costs one
`destruct` and closes the gaps.

**On `G`.** `interval` evaluates `G = (q*/λ)(sp z − z·σ(z))` with the two
terms decoupled, which widens it by **13.9×** — measured on the
`window_24` `z`-box: `[0.013772, 0.013990]` (width `2.18·10⁻⁴`) against a
true width of `1.436·10⁻⁵`.  `interval with (i_bisect z, i_prec 120)`
recovers it to `[0.0138730, 0.0138887]`, width `1.57·10⁻⁵` — essentially
the true one.  It is **not** used in the cover: it costs ≈ 1.6 s per
window against ≈ 0.05 s, and `G` enters the ledger with weight
`1 − w₁ ≤ 0.25`, so `2·10⁻⁴` of excess width moves a ledger enclosure
that is `6·10⁻³` wide by `5·10⁻⁵`.  The width that decides whether a
window closes is that of `f` at the composite slope `q̃`, which comes
from `w₁`, which comes from `E = q₁b + f₁`.

**What the cover does not do.**  It certifies the ledger's positivity on
Zone I's slope range.  The appendix's reduction of Zone I *to* that
positivity is not formalised, and neither are Zone 0, Zone II, or the
base row.

## Building

Needs Rocq ≥ 9 and CoqInterval:

```sh
opam install coq-interval        # 4.11.4 here
make -j8                         # from clean: 3 min 21 s wall, 1301 s CPU
make check                       # Print Assumptions on the main theorems
sh check_axioms.sh               # …on every one of the 925 windows (4 min)
make cover                       # regenerate LedgerCover*.v (needs mpmath)
```

Without the cover the seven original files take ≈ 22 s.  The cover's 24
parts are mutually independent, hence `-j`; each costs about 1.1 GB of
prover memory, so do not raise the job count much above 8.

`make check` samples the cover (three windows); `check_axioms.sh` runs
`Print Assumptions` over **all** of them, generated from the theorems
that exist rather than from a hand-kept list, and fails if any assumption
outside the whitelist appears.  The whitelist is the one described under
*Trust base*, plus `Sint63Axioms` (signed primitive integers, which the
cover's larger `interval` calls reach and the earlier files did not).

This is deliberately **not** wired into CI: installing CoqInterval takes
about twenty minutes, against four to check the proofs.
