# Descendant cleanup and work aggregation, D4
Lean 4.35.0; no sorry/admit/native_decide. cleanup_propagates and descendant_cleanup depend on propext,Quot.sound; descendant_counts additionally Classical.choice. actual_work_sum only propext.

cleanup_propagates proves any active occurrence of v in an actual ActionRuns forces a later cleanup of a distinct dependency u if u ends empty. descendant_cleanup inducts this along arbitrary dependency Paths, with final-empty explicitly required at each new endpoint. Thus cleanup in the root-cut suffix propagates from an immediate child to arbitrary descendants on such paths. descendant_counts connects these witnesses to actual scalar compute/uncompute counts and exceptional-vertex charge. actual_work_sum proves run work equals the sum of roundWork over its actual actions.

Remaining: instantiate the Paths for all nonroot vertices of complete binary tree; collect earlier computations before root cut; commute per-vertex/per-round sums and scalar-event counts with exact roundWork; derive global B<=e+2s+1; good-forest uniqueness/timestamps and occupancy-area. Proposed C3 asymptotic lower bound NOT fully proved; novelty NOT established.

Budget wall600s CPU30/call memory1GiB; all STOP. D1 list lemma/pattern errors, D3 invalid roundWork parameter; retained as failures. D2/D4 successful. D4 START2026-11-15T15:49:48.318405Z STOP15:49:48.555464Z CPU0.232447s peak660275200B rc0. Previous R4 STOP verified; no completed old compile rerun. Same owner spooky_dp, no competing implementation assignment.
