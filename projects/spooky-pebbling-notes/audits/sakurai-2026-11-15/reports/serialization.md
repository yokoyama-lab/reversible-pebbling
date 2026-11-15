# Parallel spooky serialization model audit

Source: https://arxiv.org/html/2610.09434v1 , sections 2.2–2.3.

Work = placements + unpebblings; ghost actions cost zero work. First-phase active sets {v} union predecessors(v) are pairwise disjoint; preconditions are tested before the phase. Second phase ghosts any subset of the post-first-phase pebble set. Round space is |P_before union P_after_firstphase|, NOT round-end space.

Verified finite result: all configurations and all legal first-phase subsets and ghost subsets on one leaf, two independent leaves, chain3, full binary3 and full binary5. No counterexample to legal Unpebble/Pebble/Ghost serialization, same final (P,G), or intermediate-set containment in round union.

Important correction: peak is not preserved as equality. On a full three-vertex binary tree, start with only leaf b pebbled; simultaneously unpebble b and pebble the other leaf a. Parallel union-space is 2, but removal-first serialization peaks at 1. This refutes the stronger equality, not the paper's budget nonincrease statement.

Round-end counting is unsound even on one leaf: pebble then ghost in one round has empty pebble sets at both endpoints, but round space 1.

No new research theorem: the budget-preserving serialization is already explicitly stated by the paper. This is a finite model-regression audit for subsequent Pareto search. No Lean binary available in this executor; no Lean proof/compile claimed. General DAG proof, exhaustive all graphs, and whole-schedule work/depth Pareto correctness are unproved.

Next concrete theorem: a certified finite-horizon DP over (P,G), with transition cost (union-space,work,depth), computes exactly the feasible Pareto frontier, by induction on number of rounds. Zero-work ghost-only transitions still consume a round; this prevents incorrect zero-cost closure from erasing depth. Validate full binary3 expected optimum (space3,work5,depth3) before binary7.
