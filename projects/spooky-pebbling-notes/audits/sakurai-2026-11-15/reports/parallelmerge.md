# PARALLELMERGE M5: simultaneous noninterfering fringe rounds

Owner spooky_dp, prior LIFTCOST C3 STOP/log1719 confirmed. 600s wall reservation, percallCPU30/wall60/1GiB. AllSTOP on m3; no long s3 process. Mikawa export remains blocked pending approval, not attempted.

## Verified general simultaneous physical step
`merge` constructs one Action, selecting the nonidle first-phase move from independent sources and OR-ing ghosts. `Apart` covers all touched vertices, including ghost-only actions; `Cross` requires cross-source active-neighborhood disjointness. Both are essential; disjoint active targets alone is insufficient.
`merge_legal`: from both local-to-current-configuration legal rounds and these structural conditions, merged round is Legal under OLD-configuration prerequisites.
`merge_round`: merged final configuration equals afterRound(afterRound(q,a),b) as an algebraic state identity. This DOES NOT assert sequential b is legal after a; ghosting a dependency can invalidate a sequentialization, so only combined legality is used.
`merge_work`: exact sum of work with valid list lengths.
`merge_space`: true union-space <= sum of the two original round union-spaces. This coarse upper bound double-counts shared outside storage; refined single-count outside identity remains.
`simultaneous_step`: constructs actual PaperRuns of depth1 with those state/work/space guarantees.
`decode_disjoint`, `fringe_apart`, `fringe_cross` discharge touch-set and cross-active-neighborhood hypotheses for distinct terminal fringes rooted at the same depth. `fringe_simultaneous_step` gives actual PaperRuns1 and exact sum of original LOCAL roundWork. Individual lifted-round legality on the common current configuration remains explicit, derivable using E7 when the two local configurations are combined consistently.

## Still unfinished
Full synchronized trace composition requires a product-configuration invariant through every merged round. Arbitrarily many fringe batching and sharpened outside-space counted once are not completed. Therefore no whole-tree W<=3n,D=O(HlogH),s=Theta(n/H) upper proof yet. This unit is the genuine one-round merge component, not a completed multiple-trace theorem. Known Lee algorithm remains baseline; no novelty/S claim.

## Verification
Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. M1/M2/M4 failed saved, M3/M5 succeeded. M5 UTC2026-11-15T17:29:56.732315--17:29:58.022750 CPU1.283698s peak696991744B rc0. General simultaneous_step uses propext/Quot.sound; fringe specialization adds Classical.choice. No sorry/admit/native_decide in successful theorem.
