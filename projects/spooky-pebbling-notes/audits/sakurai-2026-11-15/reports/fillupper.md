# FILLUPPER F5: concrete full-tree filling and cleanup

Owner spooky_dp, previous BATCHUPPER B3 STOP (log1709 readback confirmed). Independent upper literature audit is separate. Reservation600s wall, each callCPU30/wall60/1GiB; allSTOP. Mikawa export pending approval, not attempted.

## General actual schedule proof
`layers n H` is a concrete list of H compute batches, bottom-up heap levels [2^k-1,2^(k+1)-1) in descending k, without ghost moves.
`Saturated q L` specifies all vertices with index>=L pebbled, others not, with P/G disjoint. `fill_layer` proves actual legality and updates threshold 2L+1 to L. Thus `fill_correct` discharges every reachable-state admissibility condition for the whole concrete schedule, not an arbitrary admissibility hypothesis.
`pebs_evolve` and `fill_work` telescope exact compute work across actual states; `fill_space` bounds true union-space.
`full_storage_fill`: for n=2^H-1, initial P empty and consistent arbitrary ghosts, exists actual PaperRuns with D=H, W=n, S<=n, final allP and noG.
`reverse_execute` lifts existing one-round reverse lemma to an entire ghost-free concrete compute schedule with identical work/space and reversed endpoints.
`full_storage_cleanup`: for n=2^H-1, initial P empty and consistent arbitrary ghosts, exists actual PaperRuns D=2H, W=2n, S<=n, final empty. It computes from ghosts to allP, then reverses the empty-start fill, removing allP without restoring ghosts.
These claims hold for all H, including empty H0 (degenerate zero run). No finite/native enumeration.

## Remaining matching-upper tasks
This is a complete general full-storage terminal-fringe cleanup component, NOT the small-space whole-tree upper theorem. Arbitrary heap subtree embedding with untouched outside state, batching many fringe blocks within s, retained global output, and optimized first-stage preparation/top skeleton still need a general schedule proof and W<=3n,D=O(HlogH),S=Theta(n/H) aggregation. Underlying algorithm is known Lee construction/method; no novel upper claim.

## Execution
Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. F1/F2/F4 failed and retained; F3 fill-only succeeded; F5 full cleanup succeeded. F5 UTC2026-11-15T17:05:29.932079--17:05:30.403932, CPU0.462907s, peak686915584bytes, rc0. Main successful theorem axioms only propext,Quot.sound. No sorry/admit/native_decide. Failed compilation output is not accepted evidence.
