# reversible-pebbling-lean

Machine-checked (Lean 4) results on exact reversible pebbling of
chains — the artifact accompanying the paper *"Exact Reversible
Pebbling at Minimal Space: Machine-Checked Structure Theorems and the
Growth Rate of Space-Optimal Simulation"* (submitted to IEICE Trans.
Fundamentals A).

To our knowledge this is the first machine-checked treatment of the
reversible-pebbling literature (Knill 1995, Královič 2004,
Pesu–Phillips 2015).

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
  `c ≥ 2^{5/3}·10⁸/11231² ≈ 2.5169802` — within 6·10⁻⁵ of the q = 3/2
  optimum and of the conjectured exact value `2^{1+κ*} = 2.517065`.

The namespace `GenJanus.*` is kept identical to the private benchmark
repository so that theorem names and file hashes match the pinned
proof manifest referenced by the paper.
