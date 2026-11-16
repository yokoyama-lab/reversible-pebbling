# General signature-cover theorem → fixed-event pebbling: application audit

Fixed manuscript v15 SHA256: 2cd638db0a28b2ca68098f0725937354634ec5631070c995e74cbc23fb2efd94.
Fixed LocalCertificate.lean SHA256: ab087e2a09ad672be9248e409381581905e98fa0635cae3b111a65a1c06fa9cf.
Fixed CommonExtension.lean SHA256: 9dd1fad2783efc577f1b489472cf17bb3080314a0d43c8dd1423d5bea36ac59d.

## What the verified general theorem requires
A finite set of event IDs, a Nodup universe word U, a supported strict base order Q, integer event weights, initial height, an exact cumulative-cost value, and a guard depending ONLY on the weight/sign sequence. Components are full ordinary-poset languages over exactly the same IDs, without filtering or auxiliary events.

## Proposed concrete instantiation
For local I use Fin 10; for M use Fin 12. IDs are event-list indices, NOT vertex numbers: placement and removal at the same vertex remain different IDs. U is the complete ID enumeration. Weight is +1 for place and -1 for remove. Initial height is 4 in both fixed local certificates. Capacity guard is that all post-event prefix heights lie between 0 and 5. Concrete cost is the sum of those post-event board sizes, not the initial size and not number of transitions. Exact-cost layers, not upper-budget unions, are the theorem's target.

The intended base Q is the intersection of precedence relations of ALL legal local words. Do not build Q from only the six I or fourteen M lower-bound witnesses: those are not the full 200/584-word languages.

## Evidence and remaining obligations
1. Fixed distinct IDs and ±1 event flags are explicit in the source. The source legal predicate uses length/Nodup/in-range; its equivalence to List.Perm of the full Fin enumeration remains a Lean bridge.
2. Each successful placement inserts an absent vertex; each successful removal requires membership and erases that vertex. A direct theorem about the original imported step can connect board lengths to ±1. This is the next finite proof unit, not yet established by this audit.
3. Replay must preserve the board invariant and accumulate heights/cost; capacity success then matches the sign-word guard. These general replay bridges remain unproved here.
4. Predecessor, lifetime, actual-erasure and final-board tests are ID/board-dependent. They cannot simply be moved into a sign-only guard. They must already be captured by Q on its entire extension language.
5. v15 §資源ガードを残す表現との対照 reports finite replay evidence: Q extensions 472/2916, guarded languages 200/584, with non-capacity conditions satisfied. This is manuscript-recorded finite evidence, NOT an imported Lean theorem. The archived concrete Q-edge data and complete non-capacity equivalence proof must be recovered or proved before a formally verified physical application is claimed.
6. Global k uses renamed, disjoint IDs and fixed-order composition of factors/tail. Its unique physical decomposition and cost shifts require separate bridges; neither local evidence nor the general theorem alone proves the global formula.

## Manuscript-safe statement now
A general finite-ID theorem for exact cumulative-cost layers with a sign-sequence guard is formally verified, including the minimum number of ordinary-poset components and uniqueness of their languages. Its application to the manuscript's fixed-event pebbling family is conditional on the explicit Q/physical-language and cost-replay bridges above. The theorem is not a result for arbitrary pebbling schedules. Novelty relative to trace/heap theory remains under investigation.

This audit changes no manuscript or Overleaf project and reruns no enumeration. Grade C: precise application obligations, not a completed physical-model proof.
