# BATCHUPPER B3: constructive general physical batch bridge

Prior LOGLOWER L3 STOP, work log1707 readback confirmed. Owner spooky_dp. Scope differs from independent novelty/upper audit. Reservation600s wall, percallCPU30/wall60/1GiB, allSTOP. Mikawa export prohibited pending approval, not attempted.

## Verified general components
`batch C G` constructs a concrete finite Action for arbitrary n: simultaneously compute Boolean-selected vertices C, then ghost G. Old ghosts on computed vertices are cleared. `batch_legal` proves legality from concrete freshness/dependency/noninterference/ghost-target conditions, including initial P/G disjointness. It does not assume Legal or PaperStep.
`after_batch` exact P'=(P union C) minus G; G'=(G_old minus C) union G.
`work_batch` actual roundWork=card C.
`space_batch` actual union-space=card(P union C), including pebbles removed by second-phase ghosting. This avoids the endpoint-space underestimate.
`batch_step` constructs actual PaperStep with these exact resources.
`heap_layer_independent`: any selection from integer heap layer interval [L,2L+1) has pairwise disjoint active neighborhoods under actual HeapPath.pred. `heap_layer_step` removes the abstract noninterference premise for such selections.
`execute_runs` physically realizes any admissible list of compute/ghost batches, exact depth=list.length.
`execute_work` actual work=sum selected vertex counts.
`execute_space` derives global budget from concrete union occupancy at every reachable prefix.
`runs_append` composes physical PaperRuns, exact depth/work addition, max-space.

## Important remaining obligations
This is a finite proof-development step, NOT the full matching upper theorem. `Admissible` still requires freshness/dependencies/ghost targets at each reachable prefix. General full-tree/fringe schedule generation and discharge of these invariants, cleanup uncompute phase, concrete W<=3n and D=O(HlogH),s=Theta(n/H) bounds remain to be connected. Prior FixedWork is abstract recurrence proof; old247-case Python audit did not establish fast parallel depth. Do not treat either as completed general physical construction.
Underlying preparation/block algorithm is Lee prior art; this unit formalizes construction infrastructure, no novel upper/S claim. Lower bound L3 remains a separate complete formal-model theorem.

## Verification
Lean4.35.0 arm64 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. B1 failed and retained; B2 and B3 rc0. B3 UTC2026-11-15T16:59:25.083376--16:59:25.448855 CPU0.358812s peak683327488bytes. Successful main axioms only propext,Quot.sound; no sorry/admit/native_decide. B1 failure output sorryAx is not accepted proof.
