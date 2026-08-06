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
- `PrimInt63`/`Uint63Axioms`, `PrimFloat`/`FloatAxioms`, `PrimArray`
  — Rocq's *primitive* machine integers, IEEE-754 floats and arrays,
  axiomatised by their specifications.  CoqInterval computes its
  enclosures with these.

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

## Building

Needs Rocq ≥ 9 and CoqInterval:

```sh
opam install coq-interval        # 4.11.4 here
make                             # ≈ 25 s
make check                       # Print Assumptions on the main theorems
```

This is deliberately **not** wired into CI: installing CoqInterval takes
about twenty minutes, against twenty-five seconds to check the proofs.
