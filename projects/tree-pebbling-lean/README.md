# tree-pebbling-lean

Lean 4 / Mathlib proofs for the paper

> 完全二分木の空間最適な可逆ペブリングの手数（多項式上界の Lean 4 による証明と高さ 8 までの厳密値）, WiNF 2026.

Komarath, Sarma and Sawlani (JCSS 2018, arXiv:1604.05510) asked whether complete binary trees can be
reversibly pebbled with the minimum number of pebbles in a polynomial number of steps.
This repository proves, with no assumptions beyond the standard axioms, that they can:

* **Theorem 1.** For every rooted tree `T`, `M(T, R•(T)) ≤ F(T, R•(T)) ≤ 3^(R•(T) - 1)`,
  where `M(T, S)` is the minimum number of moves of a persistent reversible pebbling with at most
  `S` pebbles, `R•(T)` is the minimum number of pebbles, and `F` is the tree version of Knill's recursion.
  The DAG version `M(G, R•(G)) ≤ 3^(R•(G) - 1)` is also proved, for every acyclic `G` that can be pebbled. The construction is
  Chan's (CCC 2013, Lemma 3.22: run `P1`, then `P2`, then `P1` in reverse); the theorem counts its moves.
* **Corollary.** For the complete binary tree `T_h` with `n = 2^h - 1` vertices,
  `R•(T_h) ≤ h + ⌈log₂ h⌉`, `M(T_h, R•(T_h)) ≤ 3^(h + ⌈log₂ h⌉ - 1) ≤ (n + 1)^4`, and
  for every `ε > 0`, `M(T_h, R•(T_h)) ≤ (n + 1)^(log₂ 3 + ε)` for all large `h`.

## Rules of the game

A configuration is a finite set of vertices. A move toggles one vertex `v` (places or removes a pebble),
and it is legal only when all children of `v` carry pebbles. A persistent pebbling goes from the empty
configuration to the configuration `{root}`. Pebbles = maximum size of a configuration; moves = length.
(Komarath et al., Definition 3, persistent version; Chan, Definition 3.20.)

## Files

| File | Contents |
|---|---|
| `TreePebbling/Game.lean` | The game on a general DAG; Chan's Raz–McKenzie recursion `ValLE`; `M_Rb_le_three_pow` (DAG version of Theorem 1) |
| `TreePebbling/Strat.lean` | Rooted trees, strategy trees, `stratTree_iff_pebbling` (Komarath et al., Lemma 10, derived from Chan's Lemmas 3.22, 3.23, 3.25), `theorem1`, `M_Rb_le` |
| `TreePebbling/F.lean` | The recursion `F`, `F` is non-increasing in `S`, `M_le_F`, `theorem1_F` |
| `TreePebbling/Exists.lean` | Removes the hypothesis "the tree can be pebbled at all": `exists_pebbling`, `M_Rbullet_le`, `theorem1_Rbullet`, `theorem1_F_Rbullet` |
| `TreePebbling/CBT.lean` | The corollary for complete binary trees (heap numbering): `cbt_Rb_le`, `cbt_M_le`, `cbt_M_le_card_pow`, `cbt_M_le_rpow` |
| `TreePebbling/Tests.lean` | Bounded sanity checks against the paper's Python implementation (uses `native_decide`; not used by the theorems) |
| `CheckAxioms.lean` | `#print axioms` for the main statements |

## Build

```
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

Every statement listed in `CheckAxioms.lean` depends only on `propext`, `Classical.choice` and `Quot.sound`.
There is no `sorry` and no `axiom`. `native_decide` appears only in `Tests.lean`.

## What is not formalized

* The exact values of `M` in the paper (exhaustive searches up to height 8) and of `F` (up to height 12).
* `R•(T_h) = h + Θ(log* h)` (Královič 2004) and the exact value of Chan, Lauria, Nordström and Vinyals.
  The corollary uses only the weaker bound `R•(T_h) ≤ h + ⌈log₂ h⌉` proved here.
* Whether `F = M` on binary trees (it is false on general rooted trees; see the paper).

Comments in the source are in Japanese.

The Lean code was written with the assistance of an AI system (Claude) and checked by the Lean kernel.

## License

MIT. See `LICENSE`.
