# `rocq/` — `κ*` and `ρ_c`, inside a prover

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

`Print Assumptions` on the three theorems lists only:

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

**Scope.** This is the value layer only.  Lemma A's ledger also uses
`f'(q)`; its closed form comes from the implicit function theorem, and
formalising that derivative is separate work that is **not** done here.
See `scripts/probe_brw/m40_ledgerA_explicit.py` in the paper repository
for the ledger written out explicitly — parameterised by the E-branch
slope `q₁` (which removes the inner minimisation) and using the true
chord deficit instead of `M = sup f''` (which removes the second
derivative of an implicit function).

## Building

Needs Rocq ≥ 9 and CoqInterval:

```sh
opam install coq-interval        # 4.11.4 here
make                             # ≈ 19 s
make check                       # Print Assumptions on the main theorems
```

This is deliberately **not** wired into CI: installing CoqInterval takes
about twenty minutes, against twenty seconds to check the proofs.
