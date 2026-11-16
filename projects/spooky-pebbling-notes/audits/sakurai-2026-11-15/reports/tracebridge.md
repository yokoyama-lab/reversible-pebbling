# PaperRuns to real cleanup order: general Lean bridge

Task SPOOKY-TRACEBRIDGE-20261115, sole owner /root/spooky_dp. Previous CUTBOUND finite jobs STOP; independent lower_audit only reviews mathematics. Bounds600wall total, per callCPU30/wall60, Lean-j1-M1024. All jobs now STOP; no prior exact7 shards or31-vertex certificate reruns.

## Newly connected to the ORIGINAL model
TraceBridge.lean imports the existing ConcreteRound.lean, not a replacement rule set, and CutBound.lean from the preceding lower-bound unit.
1. scalar_round: every Legal action induces a valid scalar three-state trace for each vertex, explicitly separating first-phase compute/uncompute and second-phase ghost. This preserves old-configuration preconditions and permits ghost-only and compute-then-ghost rounds correctly.
2. extract_actions / paperRuns_scalar: EVERY PaperRuns proof yields an actual Action list with length exactly its depth, an ActionRuns execution preserving the original weighted result, and the scalar trace for every vertex. This is not merely a theorem about hand-supplied cut accounts.
3. cleanup_action_exists: a vertex starting nonempty and ending empty in an actual ActionRuns suffix has an actual uncompute action in that suffix. A ghost cannot disappear for free.
4. dependency_nonempty_after: when a parent is active, a DISTINCT dependency cannot simultaneously be active (active-set disjointness). Its pebble survives the first phase; after possible ghosting it remains pebble-or-ghost, not empty.
5. cleanup_after_occurrence: for a run with action list xs ++ [parentAction] ++ ys, if that parent is active and a distinct child/dependency finishes empty, some CHILD uncompute lies in ys. This is strict suffix order, not same-round order. In particular final child uncomputations are later than the last active parent occurrence, once final positions are selected.
6. compute_before_occurrence: if the child starts nonpebbled, some CHILD compute lies in xs, strictly before the active parent action.
7. parent_bracketed combines both: any active parent occurrence is bracketed by a prior child compute and a later child uncompute, under the explicit initial/final child-state assumptions.
These are arbitrary-n/pred general theorems. No tree shape or numerical experiment is assumed. For good vertices after the last-root cut, the initial nonpebbled and final empty conditions are exactly the intended conditions. Applying the bracket theorem to the parent's unique compute/uncompute will yield strict interval nesting once uniqueness and integer indices are assembled.

## What is still NOT proved end-to-end
The entire C3 lower bound is NOT yet a Lean theorem. Missing: selecting the last root computation and proving all vertices visited by that cut; extracting exact action counts and good/exception sets from the global work bound; selecting unique compute/uncompute indices and showing continuous occupancy; binary-tree forest component and shallow-node bounds; charging those intervals to actual roundSpace sums. Earlier generic CutBound/Intervals lemmas cover arithmetic and nested-interval charging but are not yet fully wired into those semantic constructions. New results close the scalar-trace and parent/child strict-order portions only.
The mathematical proof draft remains the previous spooky-cutbound report. Novelty unverified. No S-grade claim or claimed improvement of Lee's general joint bound is made here.

## Trust and execution
Lean4.35.0. Successful final T7 has no sorry/admit/native_decide. scalar_round and paperRuns_scalar depend on propext; cleanup/order/bracket results on propext,Quot.sound. T2/T3 failed due implicit constructor parameter typing; T5 failed a dependent name after cases. Failed logs retained, not accepted proofs. T4/T6/T7 succeeded progressively.
Final T7 START2026-11-15T15:38:19.688281Z STOP15:38:20.107028Z rc0 CPU0.413247sec peak681984000bytes. Previous T6 CPU0.332512sec. Logs and receipts contain exact per-call times and output SHA. Saved .olean corresponds to T7 source.
Reproduce final proof with LEAN_PATH=. lean -j1 -M1024 TraceBridge.lean using bundled imports/olean, or rebuild ConcreteRound then CutBound then TraceBridge for same Lean version. No expensive graph enumeration.
