# Concrete parallel spooky round enumerator → bounded DP, 2026-11-15

This is verification infrastructure, grade C, not an S novelty result.

## Scope and evidence
Source: https://arxiv.org/html/2610.09434v1 §2.2–2.3 (read 2026-11-15).
Owner /root/spooky_dp; reservation SPOOKY-CONCRETE-ROUND-20261115-A1.
Parent assigned the abstract/concrete DP scope separately from completed serialization work; serialization worker previously confirmed no DP reservation. A fresh conflict-check message was sent; response still pending at this report boundary. No other worker's job was restarted or stopped.

Finite n vertices, Boolean dependency matrix. A round is a length-n word over idle/pebble/unpebble, followed by a length-n ghost mask. The enumerator tries all such words (6^n candidates), filters explicit legality, and maps to weighted successors. Legal means disjoint initial pebble/ghost sets; pebble requires absence and unpebble presence; both require all predecessors initially pebbled; selected operations have pairwise disjoint active sets {v}∪pred(v); ghosting only on post-first-phase pebbles. Pebbling clears a ghost. Space is cardinality of initial P union first-phase P+, not final endpoints. Work counts first-phase non-idle vertices. Every DP step is one round, including ghost-only rounds. Empty rounds are admitted; exact-depth results therefore include padding.

## Checked Lean theorems
- mem_words: finite alphabet words are exactly lists of the requested length whose letters lie in the alphabet.
- mem_actions: all well-sized first-phase and ghost words are enumerated.
- mem_legalActions: legal action membership iff dimensions and explicit Legal predicate.
- mem_next: enumerated successor iff existence of a legal action with matching weighted result.
- dp_iff_paperRuns: weighted depth-d DP membership iff an exact-d-round execution of the explicit concrete relation.
- feasible_iff_paperRuns: same equivalence with space/work upper bounds.
- afterRound_disjoint: the concrete update preserves disjointness of pebble/ghost sets under Legal.

Lean 4.35.0 arm64 Apple, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Final A4 real compile START 2026-11-15T13:51:24.552167Z; STOP 13:51:24.989704Z; rc0; CPU 0.439149 s; wall0.437310375 s; peak672907264 bytes. Limits Lean -j1 -M1024, subprocess timeout30 s; entire finite assignment budget600 s. Source SHA256 98f33cdd4218895e1051f36f592b6940c3590f7799c96c15ebc9f9512adea460. Output SHA256 8149b1fee59522e09ad29a4f48c3bc56bead3436adac06ce3d4a9c9887effaee.

No sorry/admit. DP and enumeration proofs depend on propext, Classical.choice, Quot.sound; disjointness uses propext only. No sorryAx. One unused simp-argument warning inherited from abstract DP. One-vertex empty-state enumeration actually evaluates to 3 legal rounds (idle; pebble; pebble then ghost).

## Not established
The name PaperRuns denotes our explicit formal model; Lean does not verify that the paper's prose matches this encoding. That external modeling correspondence was reviewed, not machine proved. No concrete complete-tree instance, terminal/root goal theorem, Pareto-dominance pruning correctness, efficient algorithm, global optimality or asymptotic lower bound has been established here. The executable enumerator is exponential; no large experiment was run. Tree axioms are not required for enumeration correctness, but would be required for any tree-specific result. Exact-depth-0 space is defined as 0; this agrees with the empty initial configuration, not arbitrary nonempty initial configurations.

## Persistence
Mac local source and all recorded compile logs retained. A1 scaffold compile succeeded but did not have separately persisted exact START/STOP; no timestamp was reconstructed. A2–A4 have recorded START/STOP. Existing shared-drive files not changed. New report/source archive will be saved under authorized Sakurai folder. <host> route requested from recovery owner; no inference that existing remote jobs stopped.
