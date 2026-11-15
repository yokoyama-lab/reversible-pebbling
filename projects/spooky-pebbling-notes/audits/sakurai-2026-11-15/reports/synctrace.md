# SYNCTRACE T4: full synchronized two-fringe traces, outside space once

Owner spooky_dp, prior M5 STOP/log1720 confirmed. 600s wall reservation, CPU30/wall60 percall/1GiB, allSTOP m3. Mikawa export pending approval, unattempted.

## General physical trace theorem
`pair` combines two disjoint fringe local configurations with fixed outside state. `config_commute`, `pair_round`, `pair_first` establish the actual product-state invariant. `pair_legal` derives both individual lifted rounds' legality on this common configuration, so no common-state legality premise remains in final `fringe_sync_paper`.
`pair_space` EXACTLY equals local round union-space A + local round union-space B + pebble count outside BOTH images. Shared outside storage counted once, not twice.
`fringe_sync_actions`: synchronizes full arbitrary-length local action traces using zipWith merge and proves real global ActionRuns, final product configuration, exact work sum, peak<=peakA+peakB+outside. Actual terminal heap geometry discharges independence and dependency-closure conditions. Empty traces use inequality because measured peak0 need not equal initial outside count.
`fringe_sync_paper`: two arbitrary local PaperRuns of the SAME depth d produce actual global PaperRuns depth d with those exact work/finalstate and space guarantees. No local action list or per-step admissibility assumptions in theorem.
`two_fringe_cleanup`: for distinct roots at depth D and fringe height h, local initial P empty/arbitrary consistent ghosts, produces actual global PaperRuns depth2h, work4*(2^h-1), space<=2*(2^h-1)+outside, both local fringes empty at end. This is a complete two-fringe batching instance for all h,D, not merely one-round merging or finite testing.

## Remaining
Arbitrary K-fringe family synchronization/budget grouping is not yet proved; do NOT extrapolate two-fringe theorem by claiming completed arbitrary K. First-stage preparation/top skeleton and total W<=3n at smallspace remain. Underlying construction known Lee method; no novel upper/S claim.

## Verification
Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. T1/T3/T4 successful, T2 failure retained. T4 UTC2026-11-15T17:35:26.800334--17:35:27.314579 CPU0.505135s peak687161344B rc0. Axioms propext,Classical.choice,Quot.sound only. No sorry/admit/native_decide.
