# FLEETORDER S2
O1 STOP rc0 and no concurrent Lean verified. New parent-authorized finite unit on sf2; reservation600wall/4attempts, same effective cgroup1GiB/swap0/CPU100%/Tasks16/Runtime20s/LimitCPU18s/Nice10. Existing dependencies and sources remain unchanged in prior directories.
T1 START22:37:23 STOP22:37:29 UTC rc0 CPU5.564s runtime5.566s.
S2 START22:38:51 STOP22:38:57 UTC rc0 CPU5.640s runtime5.640s.
MemoryPeak256KiB display remains unreliable; exact RSS not asserted. Both jobs stopped, files recovered and SHA verified sf2-><host>->m3.

Lean4.35.0, new accepted results:
1 take_counter_mono: actual prefix count indexed by round is monotone.
2 label_formula: parentLabel(t)=old prefix ID +1 iff current first-phase move is compute. second-phase ghost adds no compute. Valid t<length explicit.
3 parent_ids_order_child_refs: strict parent label inequality at t,s forces t<s, hence OLD child labels nondecreasing. This theorem applies to any action sequence; legality is not needed for chronological counters, and is not falsely claimed as a conclusion.
4 initial_branch: actual ActionRuns ending occupied with no compute of u starts pebbled, has ID1, and its scalar events are all idle. Covers the previously missing initial-P/no-recompute case.
5 EpochReferenceSet.Member: existential round witnessing active C/U parent, pred v u=true, specified parentLabel and OLD child label. Set-valued Prop means repeated identical pair references are deduplicated, not counted twice.
6 EpochReferenceSet.ordered: parent labels i<j imply every referenced child label from i <= every one from j.
7 EpochReferenceSet.intersection_unique: any child labels shared between current parent epoch k and arbitrary earlier epochs i,j<k are equal. Earlier witnesses need not belong to the same epoch. This directly discharges the chronological-order assumption of the static set-intersection argument for the defined actual action-sequence reference relation.

Printed axioms standard3 only; no sorryAx/native_decide. New general count/ordering/set theorems propext+Quot.sound; initial_branch includes Classical.choice. No failed attempts this unit.

Still missing: finite list/set enumeration of Member, positivity/range and membership-to-OLD-configuration witness for arbitrary interior round of a full ActionRuns, union-cardinality telescoping/double counting and tree-wide sum. Earlier prefix positivity theorem provides the required component once prefix splitting is assembled. All-epoch geometric area/second-scale/C4 depth theorem remains unproved. ParentLabel formula is a compute counter label, not by itself a definition of an occupied interval; R2 continuity and O1 last-start results provide separate bridges. No worldwide novelty/S-grade claim.
