# LIFTCOST C3: exact transported work/union-space and global fringe cleanup

Owner spooky_dp, FRINGEEMBED E7 STOP/log1717 readback confirmed. Reservation600s wall, eachCPU30/wall60/1GiB. AllSTOP, m3 no s3 long job. Mikawa export pending approval, unattempted.

## General verified cost transport
`decode_sum`: arbitrary Nat-weight sum over global partial-inverse fibers equals corresponding local sum, using embedding injectivity and complete finite image. No enumeration/native_decide. Classical decoder retained.
`lift_work`: exact equality of actual roundWork of lifted Action and local Action (requires actual local first-list length=m).
`lift_space`: exact equality of actual first-phase union-space to local round-space plus pebble count outside image. Outside ghost count is irrelevant. This is a real union-space identity, not a maximum endpoint estimate.
`lift_actions_cost`: physical global ActionRuns for any local ActionRuns under finite embedding/closed-dependency conditions, exact final lifted state and work, depth unchanged via list.map, peak space<=local peak+outside pebbles. Inequality, not equality, is used for zero-depth runs where resource measure is0.
`fringe_cleanup_cost`: those structural conditions are discharged for actual terminal binary-heap fringe rooted at depth D with height h in global height D+h. Initial local pebbles empty, arbitrary consistent local ghosts and arbitrary consistent outside. Produces actual global PaperRuns with D=2h, W=2(2^h-1), S<=2^h-1+outsideCount, final local fringe empty and outside unchanged. Combines full F5 concrete cleanup and E7 physical embedding, not merely abstract recurrence.

## Unfinished
Simultaneous merging/batching multiple disjoint fringe traces remains unproved. Geometry/nonoverlap already proved in E7 is not enough to claim resource aggregation without merged round/trace proof. First-stage preparation/top skeleton and exact overall W<=3n at s=Theta(n/H),D=O(HlogH) are still unproved. Underlying upper method is known Lee construction; no novel upper/S claim.

## Validation
Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. C1 failed saved, C2/C3 successful. C3 UTC2026-11-15T17:23:30.991431--17:23:31.287393 CPU0.290912s peak675266560B rc0. Axioms propext,Classical.choice,Quot.sound only; no sorry/admit/native_decide. New showa files only, no public push/merge, budget/security unchanged.
