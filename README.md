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

The namespace `GenJanus.*` is kept identical to the private benchmark
repository so that theorem names and file hashes match the pinned
proof manifest referenced by the paper.
