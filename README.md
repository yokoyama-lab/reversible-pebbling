# reversible-pebbling-lean

Machine-checked (Lean 4) results on exact reversible pebbling of
chains — the artifact accompanying the paper *"Exact Reversible
Pebbling at Minimal Space: Machine-Checked Structure Theorems and the
Growth Rate of Space-Optimal Simulation"* (in preparation).

To our knowledge this is the first machine-checked treatment of the
reversible-pebbling literature (Knill 1995, Královič 2004,
Pesu–Phillips 2015).

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
| **`anchor_T98500_m11.txt`** | 98500 | mant 11 | **2.5174407** |

Together with `DispersionBound4731` this brackets the growth rate as

  **2.5170647241 ≤ c ≤ 2.5174406519**,

a window of 3.8·10⁻⁴ around the conjectured exact value
`2^{1+κ*} = 2.5170648369`, which sits 1.1·10⁻⁷ above the lower bound.
The two large anchors were produced by `m33_anchor_c.c` (paper
repository), which reproduces the earlier bignum certificates bit for
bit while running ~600x faster; `base_check_T3000_eps001.txt` and
`kappa_enclosure_certified.txt` are the base-row check and the certified
23-digit enclosure of `κ*`.

## Build

```
lake build     # Lean 4 (see lean-toolchain); no external dependencies
```

All theorems are checked by the Lean kernel; `native_decide` theorems
are exhaustive finite certificates (marked BOUNDED in docstrings),
the rest are general (unbounded) proofs.

## Contents

- `GenJanus/PebblingGame.lean` — the clean-reach game, BFS, exact
  `M*(n)` tables (`mstar_table`, `pmin_table`).
- `GenJanus/PebblingFoundations.lean` — GENERAL theorems:
  time-reversal symmetry (`legal_reverse`, `exec_reverse_cancel`,
  `maxOnes_reverse`, `reverse_append_roundtrip`), full correctness of
  Bennett's recursive schedule (`bennett_general`), and
  `reach_two_pow` : reach(p) ≥ 2^(p−1) for all p.
- `GenJanus/PebblingTheory.lean` — literature verification and the
  paper's new results: Knill's recursion/tables/characterisation,
  Královič's complete-variant theorems, exact T(2^p−1,p) values, the
  T = 2H bridge and the T < F reversal, the corner-forced half-split
  recurrence, the Merge-Lemma row structure (count laws, missing-value
  law, cumulative correction P₃ ≡ 1), the midpoint sandwich and
  amplification, and the tail-invariance base S = 11 / step S = 12 on
  1024/2048-wide tables.

- `GenJanus/MinimaxDuality.lean` — ZERO duality gap: the elementary
  minimax duality identity for monotone functions
  (`minimax_duality`), making the maximin lower recursion
  (`count_recursion_split`) and the minimax upper recursion
  (`count_recursion_minmax`) EXACT (`count_recursion_split_exact`,
  `count_recursion_minmax_exact`, `bcount_maximin_exact`) — the dual
  DP pair is one exact self-referential recursion.
- `GenJanus/DispersionBound.lean` — the dispersion lower bound,
  rational instance q = 1, λ = 13/8: `dispersion_main`
  (`8^s C_S(v) ≤ 64 v 13^s`, unconditional) and
  `dispersion_midpoint_16` (`16^s ≤ 64 m_S 13^s + 8^s`), certifying
  `c = 2d ≥ 32/13 ≈ 2.4615` — the first machine-checked improvement
  over the entropy lower bound `2^{1+ε*} ≈ 2.4518`.
- `GenJanus/DispersionBound32.lean` — the q = 3/2 instance (σ = 9/8,
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

The namespace `GenJanus.*` is kept identical to the private benchmark
repository so that theorem names and file hashes match the pinned
proof manifest referenced by the paper.

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
* `RevPebbling/ChordDeficit.lean` — the algebraic core of Zone I.  The
  dispersion exponent `f` is only *M*-semiconcave (`f'' > 0` for
  `q ≳ 0.5`), so Jensen runs the wrong way and the chord deficit
  `(M/2)·w₁w₂(q₁−q₂)²` has to be carried; `chord_deficit` derives it
  from concavity of `f − (M/2)q²`, and `ledger` / `ledger_pos`
  assemble Lemma A of the one-step analysis from it plus the two
  branch gaps — reducing the analytic side to explicit hypotheses.

Both build with `lake build` (Lean 4.31.0); no `sorry`, axioms are
`propext` / `Quot.sound` / `Classical.choice` only.
