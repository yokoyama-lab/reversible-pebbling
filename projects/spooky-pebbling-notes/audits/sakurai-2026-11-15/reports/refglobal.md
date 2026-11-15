# REFGLOBAL V3: global nonduplicated reference charge
Owner /root/spooky_dp, continuation of REFSUM S4 STOP rc0. No other research worker/job started.

RefGlobal.compute_slots proves the sum over List.finRange n of scalar compute counts equals actualComputes: sum, over original action occurrences, of the number of Move.pebble entries in that action's first list. This is an exact connection to physical compute slots, using the ActionRuns length invariant, indexed_moves, scalar event expansion, and interchange of finite sums. Each (action occurrence, vertex index) is counted once. Equal action values at different rounds are still different list occurrences. This is a count correspondence; an explicit injective witness function from individual charges to slots is NOT constructed.

RefGlobal.all_vertices proves sum over all vertices of interior-chunk (ghost+uncompute) charges <= actualComputes of the original action list. RefGlobal.total_charge_le_work bounds this by actual run work; RefGlobal.paper_charge extracts the action list from a PaperRuns with exactly d rounds and both bounds.

Reference marking is a Boolean any, not a count of referencing parents. Multiple parents referencing the same child in a round therefore cannot create duplicated chunks. References to distinct children use distinct child-indexed scalar compute budgets. The terminal chunk has no next reference and remains excluded. No overlapping arbitrary pair-of-reference gap is summed. This unit found no counterexample to these exact statements and proves them for every ActionRuns, including zero vertices or zero actions when such runs exist. It does not assert an area inequality or C4 lower bound.

V3 compile: 2026-11-15T20:09:41.164779Z to 20:09:41.458673Z, rc0 CPU .286543 s peak 673988608 bytes. Lean4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. -j1 -M1024, 30CPU/60wall per compile, 600wall unit limit. Axioms propext and Quot.sound only, no native_decide/sorry in accepted results.
V1 arithmetic normalization failure; V2 edit transport/Python encoding error meant source unchanged and compile failed identically; both compile logs retained. V3 corrects the source. Failed diagnostic sorryAx is not accepted proof evidence.

Remaining: explicit per-charge matching if needed for later construction; original-round union-area; second-scale structure; C=4 lower bound and same-budget fast upper. This is a proof infrastructure lemma, not a new S-level theorem. No novelty claim.

Mikawa transfer remains blocked awaiting approval, no attempt. New showa artifact only, no existing file modified.
