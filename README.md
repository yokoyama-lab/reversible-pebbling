# reversible-pebbling-lean

Machine-checked (Lean 4) results on exact reversible pebbling of
chains — the artifact accompanying the paper *"Exact Reversible
Pebbling at Minimal Space: Machine-Checked Structure Theorems and the
Growth Rate of Space-Optimal Simulation"* (in preparation).

Its subject is the **Knill constant** `c`, the growth rate of Knill's
space-optimal cost `f_p = F(2^{p-1}, p)`.  The name is attached to `c`
itself (`BlockSim.c`), which provably exists and is bracketed below;
`2^{1+κ*}` is its *conjectured* value, not its definition.

To our knowledge this is the first machine-checked treatment of the
reversible-pebbling literature (Knill 1995, Královič 2004,
Pesu–Phillips 2015).

## What pinning `c` would settle

`c` is the growth rate of the time cost of reversible simulation at
**exactly minimal space**: uncomputing an `n`-step chain with the
smallest possible number of pebbles costs `Θ(n^{log₂ c})` moves, and
`log₂ c = 1.33…`.  Before this work that exponent was only known to lie
between `1` (Královič's `Ω(n lg n)`) and `log₂ 3` (Li–Vitányi) — an
interval of width more than one half.  What a sharp value buys:

- **Resource estimation for reversible and quantum computation.**
  Bennett's pebble game is what decides how many ancillas and how many
  gates an uncomputation costs, and the minimal-space corner is the
  regime that matters when qubits, not gates, are scarce.  The gap
  between the old bounds is a factor `n^{log₂ 3 − log₂ c}`, which is
  already more than an order of magnitude at `n = 10⁶`.
- **The trade-off curve closes.**  Knill settled the asymptotics for
  `(log n)/S ≤ 1/2`; the minimal-space end was open.  With both ends
  known, the profile `g(β)` interpolates between them, so `F(n,S)` has a
  known exponent throughout.
- **Memory-hard functions.**  Reversible-pebbling bounds feed the
  post-quantum security analysis of iMHFs (e.g. *The Parallel Reversible
  Pebbling Game: Analyzing the Post-Quantum Security of iMHFs*,
  eprint 2024/334); sharper constants give sharper parameters.
- **The method transfers.**  The route here — a supersolution family for
  a dual counting recursion, made exact by a zero-duality-gap identity —
  is not specific to this problem.  The recursion's value is a
  branching-random-walk front velocity, and the residual error of any
  finite-time evaluation is the Bramson logarithmic correction
  (measured here as `≈ 1.37·ln T/T`, see `CLAUDE.md`).  That structure
  recurs in other pebble games and in min-max divide-and-conquer
  recurrences.

Two honest limits.  *Pinning* `c` means proving the conjecture
`c = 2^{1+κ*}`; the lower bound already agrees to nineteen decimals, so
what is missing is an analytic upper bound — the anchor DP cannot get
there, its error being the `ln T/T` correction above.  And `c` is the
constant of a **chain**; pebbling general DAGs is PSPACE-hard, so what
generalises is the method and the exact answer at the extreme point of
the trade-off, not the number.

## `data/` — numerical certificates

The Lean development is accompanied by exact DP certificates that the
machine-checked composition theorem (`count_composition` /
`midpoint_composition`) turns into unconditional bounds on `c`.  Each
file records the exact integer `v*` with `L(T0, v*) ≥ 2^{T0−2}`, whence
`c ≤ 2·(v*)^{1/(T0−2)}`.

| file | T0 | grid | `c ≤` |
|---|---|---|---|
| `anchor_t598.txt` | 600 | mant 5 | 2.547097 |
| `anchor_t1198.txt` | 1200 | mant 5 | 2.536842 |
| `anchor_T7500_m7.txt` | 7500 | mant 7 | 2.521235 |
| `anchor_T141000_m10.txt` | 141000 | mant 10 | 2.5174496 |
| `anchor_T98500_m11.txt` | 98500 | mant 11 | 2.5174407 |
| **`anchor_T700000_m12.txt`** | 700000 | mant 12 | **2.5171540** |

Together with `CriticalRoot25366` this brackets the growth rate as

  **2.5170648368938161205 ≤ c ≤ 2.5171539807**,

a window of 8.9·10⁻⁵ — all of it on the upper side — around the
conjectured exact value `2^{1+κ*} = 2.5170648368938161205744…`, which
the lower bound now matches to **nineteen decimal places**.
Note that a finer grid beats a longer run: `anchor_T141000_m10.txt`
uses 43% more time steps than `anchor_T98500_m11.txt` and is still the
weaker bound, because the round-down loss per step scales with the
octave resolution `2^{-m}`.
The three large anchors were produced by `m33_anchor_c.c` (paper
repository), which reproduces the earlier bignum certificates bit for
bit while running ~600x faster; `base_check_T3000_eps001.txt` and
`kappa_enclosure_certified.txt` are the base-row check and the certified
23-digit enclosure of `κ*`.

### `κ*` is now enclosed inside a prover too

`kappa_enclosure_certified.txt` is rigorous but runs outside any prover
(Arb balls, a Krawczyk operator, 602 adaptive boxes).  `rocq/KappaStar.v`
re-derives a machine-checked enclosure with **Rocq + CoqInterval** —
Lean 4 has no interval-arithmetic tactic, so this one file lives in
Rocq:

```
κ* ∈ [0.3317423792563105, 0.3317423792563106]
c  = 2^(1+κ*) ∈ [2.517064836893816, 2.517064836893817]
```

`ρ_c` is never built as a function; the trick is that `g q ·` is
monotone, so `V q ≤ K` becomes the sign of `g` at `2^(1/q−K)`, which
has a closed form.  Only `2/5 ≤ q ≤ 302/100` needs interval arithmetic;
the two tails are elementary.  Details, and the exact trust base, in
`rocq/README.md`.

`RevPebbling/Final.lean` now **carries those two Rocq theorems by name**
rather than restating their numerals: `KappaUpperBound KHI` transcribes
`kappa_upper` and `KappaAttained KLO` transcribes `kappa_lower`
(`g q r = 0` is `CriticalRoot.G q r = 1`, and `V` is the same function).
Given them, `c_bracket_of_rocq` proves **in Lean**

```
2^(1+KLO) ≤ c ≤ 2^(1+KHI),     KHI − KLO = 10⁻¹⁶
```

— the upper end through the whole subsolution chain
(`Assemble.psi_le_count` → the readout → `Readout` → `Unconditional`),
the lower end through `CriticalRoot.c_ge_two_pow_V`.  Both hypotheses
were **carried**, and the manifest's statement audit listed them with no
`PROVED by`, until the file described next discharged them.

### The same enclosure, with no interval arithmetic at all

`RevPebbling/KappaEnclosure.lean` proves both of those hypotheses **in
Lean**, so the sixteen-digit value of `c` no longer rests on the Rocq
layer:

```
KappaEnclosure.kappaStar_enclosure     : KLO ≤ κ* ≤ KHI
KappaEnclosure.kappaUpperBound_KHI     : Final.KappaUpperBound Final.KHI
KappaEnclosure.kappaAttained_KLO       : Final.KappaAttained Final.KLO
KappaEnclosure.c_bracket_unconditional : 2^(1+KLO) ≤ c ≤ 2^(1+KHI)
KappaEnclosure.c_decimal_bracket       : 2.517064836893816 ≤ c ≤ 2.517064836893817
```

Lean still has no interval-arithmetic tactic; what replaces it is
Gibbs' inequality.  At a root, `ρ^(−q) + (1+ρ)^(−q) = 1` is Kraft's
inequality for the two lengths `log ρ` and `log (1+ρ)`, so weighted
AM–GM against **any** weight `θ ∈ (0,1)` bounds `V(q)` by

```
Λ(θ, ρ) = (θ·log ρ + (1−θ)·log (1+ρ)) / H(θ) − log ρ / log 2
```

— an explicit function of `ρ` alone, with the implicit root function
gone.  `Λ(θ, ·)` is convex in `log ρ` (two more applications of AM–GM,
no derivative anywhere), so over an interval it never exceeds its larger
endpoint value, which is what makes a finite grid a proof: 34 intervals
cover `ρ ∈ [1, 9/5]`, each with its own `θ`, and `θ = 1/2` closes
`ρ ≥ 9/5`.  Their widths run from 4·10⁻¹¹ at the tangency to 0.36.  The
lower bound reads the same inequality backwards — fixing the weight
first makes one point of the root curve *exact* — and needs no covering.

The single numerical primitive is a rational enclosure of `Real.log` of
a rational, from Mathlib's `Real.abs_log_sub_add_sum_range_le`; the file
uses 219 of them.  The last line needs one more: `c = exp(log 2·(1+κ*))`,
so two applications of `Real.exp_bound` (`exp_enclose`, 24 terms each)
turn the enclosure into the decimal — the step `KappaStar.v` did with
`interval`.  No `native_decide`, no carried hypothesis, the three
standard axioms.  `rocq/KappaStar.v` is now an independent second check
of the same interval rather than the only one.

**The enclosure is not needed for the identity, though.**  Define `κ*` as
the supremum of `V` over the roots (`Final.kappaStar`) and

```
c = 2^(1+κ*)          -- Final.c_eq_two_rpow_kappaStar, no hypotheses
```

holds outright: the upper side is the subsolution chain applied at
`κ = κ*`, where `hsup` is `le_csSup` and the bound above that makes the
supremum exist is `KappaLtHalf.V_lt_half`; the lower side is
`CriticalRoot.c_ge_two_pow_V` at every root, turned into a bound on the
supremum by `csSup_le`.  The only numeral anywhere is `33/100 ≤ κ*`, from
the `q = 3/2` root bound already in Lean.  What Rocq adds is *what `κ*`
is* — `kappaStar_mem_enclosure` reads its enclosure back against the
identity.

## Build

```
lake build                              # Lean 4 (see lean-toolchain)
python3 scripts/build_proof_manifest.py # rebuild + audit + pin hashes
make -C rocq                            # Rocq + CoqInterval (see rocq/README.md)
```

All theorems are checked by the Lean kernel; `native_decide` theorems
are exhaustive finite certificates (marked BOUNDED in docstrings),
the rest are general (unbounded) proofs.  Of the 861 theorems the
manifest lists, **73 rest on a `native_decide` certificate and 17 need
no axiom at all**; the rest use only `propext` / `Quot.sound` /
`Classical.choice`.  Which theorems fall in which class is recorded
per stage in `proof-manifest.json` (`native_decide_theorems`,
`axiom_free_theorems`) — generated from `#print axioms`, so the prose
in each stage's `scope` cannot drift away from what the kernel reports.
The same file records, per stage, which theorems carry a hypothesis
(`carried_hypotheses`) and which theorems *prove* one
(`proves_hypotheses`), with the verdict per hypothesis in the top-level
`hypotheses` field, **keyed by the argument**: `Submult fRow` and
`Submult fRLE` are different assumptions and only the first is a
theorem.  **Two remain unproved**: superadditivity of the count profile
(`Superadd`, 3 theorems in the front-DP layer, which does not touch `c`)
and `Submult fRLE`, since `fRLE = fRow` is certified only at the six
points `S = 10, 20, …, 60`.  The four the growth rate used to rest on
are now **theorems** — submultiplicativity of `fRow`
(`BlockSim.submult_fRow`, the letter's Lemma 1) and the `≥` half of
Knill's Theorem 2.1 (`RowExact.gameOptimal_holds`,
`RowExact.gameAttain_holds`, `RowExact.lowerRowExact_all`).  Statements
that still take them as arguments are the ones written before they were
proved; `RevPebbling/Unconditional.lean` instantiates the headline ones,
including `c_bracket : 2.51706472 ≤ c ≤ 2.536842`, and
`RevPebbling/UnconditionalLink1.lean` the four inside link (1) that
carried `LowerRowExact`, so every theorem carrying a *proved* hypothesis
now has a named unconditional version (the mapping is tabulated in that
file's docstring); the sharpest form
of that, with both ends internal, is
`AnchorCertify4798.c_bracket_sharp : 2.5170648368936010208 ≤ c ≤ 2.5240034`.
All of this is read off the statements with `#check`, splitting
each type at its conclusion, not asserted in prose, so "relative to X"
cannot drift either.

`scripts/check_claims.py` additionally checks that what this README
says — the counts above, the constants it quotes, the file paths and
theorem names in it — agrees with the manifest and the sources; CI runs
it, so a claim cannot quietly go out of date.

A full build takes about two and a quarter hours
(67 stages, 861 theorems), nearly all of it three checks: the composition anchor at
`T₀ = 4800` on the mantissa-6 grid (4.9·10⁸ cells, ~1.8 GB, 5695 s
and 6084 s on two timed runs),
which carries the sharpest internal bound `c ≤ 2.5240034`; the
certification of row 60 (13.1 M runs, ~5.6 GB, 384 s), which carries the
published bound `c ≤ 2.6106`; and the earlier anchor at `T₀ = 1200`
(1.8 M cells, ~1.8 GB, 364 s), which carries `c ≤ 2.536842`.  `.github/workflows/build.yml` runs the
same thing on a clean machine — build, re-audit, and check that the
committed `proof-manifest.json` is reproduced byte for byte.

## Contents

- `RevPebbling/PebblingGame.lean` — the clean-reach game, BFS, exact
  `M*(n)` tables (`mstar_table`, `pmin_table`).
- `RevPebbling/PebblingFoundations.lean` — GENERAL theorems:
  time-reversal symmetry (`legal_reverse`, `exec_reverse_cancel`,
  `maxOnes_reverse`, `reverse_append_roundtrip`), full correctness of
  Bennett's recursive schedule (`bennett_general`), and
  `reach_two_pow` : reach(p) ≥ 2^(p−1) for all p.
- `RevPebbling/PebblingTheory.lean` — literature verification and the
  paper's new results: Knill's recursion/tables/characterisation,
  Královič's complete-variant theorems, exact T(2^p−1,p) values, the
  T = 2H bridge and the T < F reversal, the corner-forced half-split
  recurrence, the Merge-Lemma row structure (count laws, missing-value
  law, cumulative correction P₃ ≡ 1), the midpoint sandwich and
  amplification, and the tail-invariance base S = 11 / step S = 12 on
  1024/2048-wide tables.

- `RevPebbling/MinimaxDuality.lean` — ZERO duality gap: the elementary
  minimax duality identity for monotone functions
  (`minimax_duality`), making the maximin lower recursion
  (`count_recursion_split`) and the minimax upper recursion
  (`count_recursion_minmax`) EXACT (`count_recursion_split_exact`,
  `count_recursion_minmax_exact`, `bcount_maximin_exact`) — the dual
  DP pair is one exact self-referential recursion.
- `RevPebbling/DispersionBound.lean` — the dispersion lower bound,
  rational instance q = 1, λ = 13/8: `dispersion_main`
  (`8^s C_S(v) ≤ 64 v 13^s`, unconditional) and
  `dispersion_midpoint_16` (`16^s ≤ 64 m_S 13^s + 8^s`), certifying
  `c = 2d ≥ 32/13 ≈ 2.4615` — the first machine-checked improvement
  over the entropy lower bound `2^{1+ε*} ≈ 2.4518`.
- `RevPebbling/DispersionBound32.lean` — the q = 3/2 instance (σ = 9/8,
  integralised via `W v = ⌊1000 v^{3/2}⌋`): `dispersion32_main` and
  its midpoint corollary certify `c ≥ 2^{5/3}·64/81 ≈ 2.5085`;
  `DispersionBound32b.lean` refines to σ = 11231/10000, certifying
  `c ≥ 2^{5/3}·10⁸/11231² ≈ 2.5169802`, and
  `DispersionBound32c.lean` goes to the critical σ = 112308717/10⁸,
  certifying `c ≥ 2^{5/3}·10¹⁶/112308717² = 2.5170377412` — within
  3.4·10⁻⁸ of the q = 3/2 ceiling `2^{5/3}/ρ_c(3/2) = 2.5170377753`.
  At q = 3/2 the rational rounding of ρ therefore costs essentially
  nothing; the whole remaining 2.7·10⁻⁵ shortfall to the conjectured
  exact value `2^{1+κ*} = 2.5170648369` is the choice of q itself
  (`q* = 1.5153832…`).
- `RevPebbling/IntRoot.lean` + `RevPebbling/DispersionBound4731.lean` —
  removing that last loss: the integer `r`-th root (`iroot`, with the
  three characterising lemmas, all unconditional) lets the dispersion
  argument run at **q = 47/31**, the convergent of `q*` within 7.5·10⁻⁴
  of it.  With `s = 1007357123/10⁹`, `ρ = s³¹`, `λ = s⁴⁷ = L/10⁴²³` and
  `W v = ⌊10⁸·v^{47/31}⌋ = iroot 31 (10²⁴⁸·v⁴⁷)`, `dispersion4731_main`
  certifies `c ≥ 2^{1+31/47}·10²⁷⁹/1007357123³¹ = 2.5170647241` —
  **within 1.1·10⁻⁷ of the conjectured exact `2^{1+κ*}`**, so the
  rational dispersion family now matches it to eight decimals.
- `RevPebbling/DispersionGeneral.lean` +
  `RevPebbling/DispersionBound197130.lean` +
  `RevPebbling/DispersionGeneralGrowth.lean` +
  `RevPebbling/Dispersion197130Growth.lean` — **the last affordable
  member of *this* family** (the sharpest lower bound overall is now
  `CriticalRoot25366`, below).  With the
  constants and the extraction both parameterised, a new exponent is an
  application rather than a new file of digits.  Which exponents are
  worth the application is settled by `q*`: the deficit
  `2^{1+κ*} − 2^{1+V(q)}` falls like `(q − q*)²`, so only the
  convergents of `q*` matter — `3/2`, `47/31`, `50/33`, **`197/130`**,
  `8324/5493`, … — and `197/130` is the last one whose constants fit
  (the next needs `L^r` with ~7·10⁸ digits against 5·10⁵ here).  Taking
  `σ = ρ_c(q)^{1/r}` rounded **up** to 20 decimals keeps `ρ` and
  `λ = L/D` exactly rational and is itself what leaves the slack
  `E = L − D − B ≥ 1` that absorbs the `+1` of the recursion.  With
  `λ₀ = 12585324184474105104/10¹⁹`, the largest 19-digit rational that
  passes the master inequality, `c_ge_2_5170648368936010208` gives
  **`2.5170648368936010208 ≤ c`** — `2.2·10⁻¹³` below the conjectured
  value, and what is left is the deficit of the exponent, not slack in
  `λ₀`.  No `native_decide`; `master` needs no axiom but `propext`.
- `RevPebbling/DispersionReal.lean` +
  `RevPebbling/DispersionRealGrowth.lean` +
  `RevPebbling/CriticalRoot.lean` — **the same family with no
  certificate at all**.  Running the dispersion induction with the real
  potential `Φ(v) = M·v^q` (rpow, not an integer root) makes the
  exponent, the ratio and the split ordinary reals subject to one real
  inequality, and `c_ge_real` turns any admissible quadruple into
  `2·(2/λ)^{1/q} ≤ c`.  `CriticalRoot` then optimises `λ`: the two
  branches of the step condition balance exactly at `λ = ρ^q`,
  `θ = 1/(1+ρ)` where `ρ` is the root of
  `ρ^{−q} + (1+ρ)^{−q} = 1`, so `c_ge_critical` gives
  **`c ≥ 2·2^{1/q}/ρ_c(q) = 2^{1+V(q)}` for every real `q > 0`** —
  existence of the root by the intermediate value theorem, uniqueness by
  strict antitonicity, and the passage to the critical `λ` by a limit in
  one real parameter (it is a genuine limit: `1/M > 0` always, so the
  step condition fails *at* the critical value).  This is what the
  rational family cannot do — there, lowering `λ` means certifying a new
  instance and the certificates grow without bound.  Sanity-checked at
  `q = 1`, where the root equation is `ρ² = ρ + 1`: the golden ratio,
  giving the closed form **`2√5 − 2 = 2.4721… ≤ c`** with nothing
  certified.  What is *not* here is `κ* = sup_q V(q)`, which needs the
  enclosure of the critical `q` and therefore the Rocq layer; each
  individual `q` is now unconditional inside Lean.
- `RevPebbling/CriticalRootRat.lean` + `CriticalRoot197130.lean` +
  `CriticalRoot8324.lean` + `CriticalRoot25366.lean` — **the real
  theorem, as a decimal.**  `c_ge_critical` names `ρ_c(q)` rather than a
  number, and extracting a number normally needs a rigorous enclosure of
  it — which Lean cannot do, having no interval arithmetic.  *Unless `q`
  is rational*: then every `rpow` collapses into an integer comparison
  (`x^{N/R} ≤ s ⟸ x^N ≤ s^R`), so pinning `2^{R/N}` from below and
  `ρ_c` from above — the latter using only that `G q ·` is strictly
  decreasing — is **four `decide`s**, packaged once and for all by
  `c_ge_of_certs`.  **The certificates grow linearly in the
  convergent**, not exponentially: 8826 digits at `q = 197/130`,
  372891 at `8324/5493`, 1136320 at `25366/16739`, and 6·10⁶ at
  `143675/94811` — *all deciding in about a second*.  That is why this
  route reaches convergents the rational-instance family cannot: there
  the constants are `L^r` with `r` the denominator of `q`, already
  `5·10⁵` digits at `197/130` and about `7·10⁸` at the next one.
  `CriticalRoot25366.c_ge_2_5170648368938161205` gives
  **`2.5170648368938161205 ≤ c`**, nineteen decimal places of the
  conjectured `2^{1+κ*}`, where the rational-instance family stopped at
  thirteen.  **We stop there** for reasons that are not about
  certificate size: the bound saturates in the digits one would quote;
  the certified enclosure of `κ*` pins the target to only sixteen
  digits, so further digits cannot be corroborated inside the
  development; and none of it narrows the bracket, whose width is
  entirely on the upper side.  Pinning one rational `q` is easy
  *because the expression is not tangent to its bound there*; at `q*` it
  is, which is why the supremum, and only the supremum, still needs
  interval arithmetic with Taylor models.

(The modules above were renamed from the historical `GenJanus.*`
namespace in the 2026-07-28 unification; see below.)

## Canonical home (2026-07-28 unification)

This repository is now the **single source of truth** for the pebbling
formalisation: the 13 legacy modules were renamed from the historical
`GenJanus.*` namespace (they originated in the private genjanus
benchmark workspace) to **`RevPebbling.*`**, and the corresponding
files were retired from that workspace.  `scripts/build_proof_manifest.py`
rebuilds everything, audits every listed theorem's axioms
(kernel axioms only for general theorems; `native_decide` permitted
for bounded certificates), and pins source hashes in
`proof-manifest.json`.

## `RevPebbling/` — the supermultiplicativity and front-DP layer

Newest results (require mathlib, pinned in `lakefile.toml`):

* `RevPebbling/SeamIdentity.lean` — the seam identity
  `N_t(b) = N_{t-1}(b) + β_t(b) + 1`, the rank and constant-run
  lemmas, the witness lemma, and the CLOSED composition induction
  (`supermult_closed`): `N_S(a) N_t(b) (1 − ε(t,b)) ≤ N_{S+t}(ab)`
  with `ε` defined by well-founded recursion and `ε < 3/5` — the
  machine-checked core of the supermultiplicativity theorem and the
  existence/concavity of the count profile `g(β)`.
* `RevPebbling/FrontDP.lean` — the autonomous front DP `L`, the split
  lower bound, the ceiling `L ≤ 2^(t−2)`, the fully proved binomial
  Pascal subsolution (Zone 0), and the transfer principle
  `subsolution_le` for the four-zone subsolution architecture toward
  `FrontExp(L) ≤ κ*`.
* `RevPebbling/GameReach.lean` + `RevPebbling/GameKnill.lean` +
  `RevPebbling/GameCost.lean` + `RevPebbling/GameEnvelope.lean` — the
  pebble game's own cost.  `ReachIn n p t` says a chain of `n` cells can
  be cleanly pebbled with peak `p` in `t` moves by a schedule staying
  inside the chain; `reach_compose` proves the `≤` half of Knill's
  Theorem 2.1 at the level of plays (reach the cut, stand on it and
  play a *lifted* schedule, then retreat by running a schedule
  *backwards*), and `reachIn_Fpre` runs that along the recursion, so the
  cost this artifact computes from `rowIter` is **attained by an
  explicit legal schedule**.  `gameF n S = sInf {t | ReachIn n S t}`
  makes the optimum a function, and `gameF_envelope` bounds it by
  `2^{S+1}·2^{⌊S/2⌋} ≤ 4√2·n^{3/2}` — an inequality between two concrete
  naturals, so unlike every statement about the real number `c` it needs
  neither submultiplicativity nor the `≥` half of Theorem 2.1 (the
  latter is named `GameGap.GameOptimal`).  `ReachLimit` states Knill's
  Theorem 2.3 as an iff about playability and generalises the corner
  forcing; `CutAccounting` supplies the time accounting of a cut.
* `RevPebbling/UpperPersist.lean` + `RevPebbling/HpkResolved.lean` +
  `RevPebbling/RowExact.lean` — the `≥` half of Knill's Theorem 2.1,
  **proved**.  An optimal play is cut at `CutFull.cutFull`; the three
  parts are accounted for separately, and the one claim about plays that
  the accounting needed — that the region above the cut never empties
  once it has been used — follows from an exchange argument, since moves
  below the cut never consult the cells above them
  (`upper_nonempty_of_optimal`).  That makes the recursion an equality
  for the game optimum (`gameF_recursion_eq_final`), and an induction on
  the number of pebbles identifies the optimum with the generated row on
  the whole reach range (`gameF_eq_row`), so `gameF (2^{S-1}) S = f_S`
  unconditionally.  The values it predicts were checked against a
  breadth-first search written outside Lean.  The published proof of
  this direction (Knill 1995, p. 5) has a gap at the step that bounds the
  middle part; the three-part decomposition follows Královič
  (RAIRO-ITA **38** (2004) 137–161, proof of Thm 3.4).
* `RevPebbling/AnchorRun.lean` + `RevPebbling/AnchorCertify4798.lean` —
  **the same anchor, one pass and one grid size larger**.  `certRun`
  runs the DP once, checks every row and reads the certificate cell,
  where `AnchorCertify` runs the same DP twice (once for `verify`, once
  for `cert`); the verdict rides in an accumulator so the recursion
  stays tail-recursive at `K ≈ 5000` transitions, and `runAux_eq`
  identifies the two components with `verifyAux` and `iter`, so nothing
  is weakened.  The grid is also cut to `N = istar + 1`, the smallest
  that holds the certificate cell.  Measured, the `T₀ = 1200` anchor
  takes 226 s this way against 364 s.  The cost is about `2^m·κ·K²`
  cells at `8.1`–`8.7·10⁴` cells/s — quadratic in `T₀`, exponential in the
  mantissa — which makes `T₀ = 4800, m = 6` the best `c` reachable in a
  few hours: **`c_le_2_5240034`**, cutting the internal gap to
  `2^{1+κ*}` by 2.9.  (`data/anchor_T7500_m7.txt`, `c ≤ 2.521235`, is
  `2.4·10⁹` cells ≈ 8 h at that rate, so it stays outside the
  prover.)  `c_bracket_sharp` puts both internal ends together.
* `RevPebbling/AnchorPacked.lean` + `RevPebbling/AnchorGrid.lean` +
  `RevPebbling/AnchorDP.lean` + `RevPebbling/AnchorCertify.lean` — the
  **composition anchor, run inside the prover**.  `CompositionAnchor`
  recorded that the large anchors came from a C computation ("their
  Lean-internal replay is future work"); `anchor_1198` replays
  `T₀ = 1200`, giving `m_{S+1198} ≤ m_S · 62·2^405` for every space
  level.  `AnchorGrowth` turns that into a statement about the real
  number — `c_le_2_536842`, the same `c` the lower bound
  `2.51706472 ≤ c` is about, and better than the artifact's previous
  internal upper bound `c ≤ 2.6106`; the earlier in-Lean anchor
  `midpoint_anchor_44` gave only `c ≤ 3.21`.  The `t`-th root needs no
  real powers: one *chooses* a rational `B` with `v* ≤ B^t`, a
  7300-digit kernel `decide` that needs no axioms at all.  Values are carried as
  `exponent · 2^32 + mantissa` so that each cell stays in machine
  arithmetic and every representable value is an exact natural number;
  addition and the grid both round **down** (`kval_flAdd_le`,
  `norm_le`), which is the only direction a lower-bound certificate can
  afford.  The DP's two-pointer needs no optimality proof: the recursion
  asks only for *some* split, so `step` returns the split it chose and a
  `Bool` checker confirms each cell's shape — a worse split would weaken
  the certificate, never break it.
* `RevPebbling/BlockSim.lean` — **submultiplicativity**,
  `f_{p+q-1} ≤ f_p · f_q`, proved by block simulation.  A chain of
  `N · L` cells is read as `N` blocks of `L`; each move of an outer play
  becomes a whole inner play lifted to the block it acts on, forwards to
  build it and backwards to clear it.  The lengths multiply and **the
  peaks add minus one**, because while the inner play runs in one block
  the others hold one pebble each and there are at most
  `(outer peak) − 1` of them.  With `N = 2^{p−1}` and `L = 2^{q−1}` that
  is a play on the reach limit for `p + q − 1` pebbles costing
  `f_p · f_q`.  Since this was the last hypothesis the growth rate
  rested on, `c` is now a real number with nothing attached and
  `c_ge_2_51706472`, `c_le_2_6106`, `c_le_two_sqrt_two` hold outright.
* `RevPebbling/Sandwich.lean` + `RevPebbling/TwoD.lean` +
  `RevPebbling/GrowthLower.lean` + `RevPebbling/DispersionGrowth.lean` +
  `RevPebbling/Dispersion4731Growth.lean` — the growth rate from both
  sides.  The sandwich `2^{S-1} m_S ≤ f_S ≤ 2^S M_S ≤ 2^S S m_S` (with
  midpoint monotonicity `m_{S-1} ≤ m_S`) gives `c = 2d`
  (`tendsto_rowMax_root : M_S^{1/(S-1)} → c/2`), and
  `growth_ge_of_geometric` — the direction `GrowthRate` was missing —
  turns geometric lower envelopes into lower bounds on `c`, so the
  dispersion certificates finally speak about the same real number as
  the upper bounds: **`2.51706472 ≤ c ≤ 2.6106`**.
* `RevPebbling/MergeFixUnique.lean` + `RevPebbling/RLEFix.lean` +
  `RevPebbling/RLECertify.lean` — the link between the general theorems
  (all about the generated row `rowIter`) and the machine-checked values
  (all produced by the imperative run-length generator).  Instead of
  verifying that generator, its output is **checked**: `mergeFix_unique`
  proves that the self-referential row equation
  `cur = 1 :: smerge prev (cur + prev)` has at most one solution, so any
  row satisfying it *is* `rowIter`; the run-length simulation lemmas
  (`expand_rleMerge`, `expand_rleZipAdd`, `expand_normRuns`) make the
  equation checkable on run-length data, and `mergeFix_of_checkFix` is
  the checker's soundness proof — all with kernel axioms only.  One
  `native_decide` per space level then turns the generator's rows into
  theorems about `rowIter`, so `f_10` … `f_60` are now values of `fRow`
  — including the 13.1 M-run row 60 (8 min 26 s, 5.5 GB) behind the
  published bound, so `GrowthCertified.growth_le_2_6106` states
  **`c ≤ 2.6106` for the row-based cost**: the numerical upper bound and
  the structure theorems finally speak about the same object.  The
  generator stays untrusted, like an unverified solver whose certificate
  is checked.
* `RevPebbling/RowMax.lean` + `RevPebbling/GrowthClosedForm.lean` —
  the closed-form upper bound **`c ≤ 2√2`** (space-optimal time
  `O(n^{3/2+o(1)})`, improving Královič's published `O(n^{log₂ 3})`),
  now general in the space level.  `rowMax_succ` proves the
  Merge-Lemma max decomposition `M_S = m_S + M_{S−1}` (previously a
  bounded check for `S ≤ 8`), so the row maxima telescope into the sum
  of the midpoint values; with the general midpoint bound
  `m_S ≤ 2^{(S−2)/2}` and the trivial `f_S ≤ 2^S M_S` this gives a
  geometric envelope of ratio `2√2`, which `growth_le_two_sqrt_two`
  runs through `GrowthRate.growth_le_of_geometric`.  Unlike
  `growth_le_2_6106` it consumes no computed value — kernel axioms
  only, no `native_decide` — but like everything in that layer it is
  stated relative to submultiplicativity.
* `RevPebbling/ChordDeficit.lean` — the algebraic core of Zone I.  The
  dispersion exponent `f` is only *M*-semiconcave (`f'' > 0` for
  `q ≳ 0.5`), so Jensen runs the wrong way and the chord deficit
  `(M/2)·w₁w₂(q₁−q₂)²` has to be carried; `chord_deficit` derives it
  from concavity of `f − (M/2)q²`, and `ledger` / `ledger_pos`
  assemble Lemma A of the one-step analysis from it plus the two
  branch gaps — reducing the analytic side to explicit hypotheses.

Both build with `lake build` (Lean 4.31.0); no `sorry`, axioms are
`propext` / `Quot.sound` / `Classical.choice` only.
