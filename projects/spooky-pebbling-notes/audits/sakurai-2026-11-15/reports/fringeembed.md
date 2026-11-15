# FRINGEEMBED E7: concrete terminal subtree into global PaperRuns

Owner spooky_dp. Prior FRAMEUPPER R4 STOP/log1715 confirmed. Reservation600s wall, CPU30/wall60 percall,1GiB; allSTOP. Runs on m3, no s3 long job affected by announced reboot. Mikawa export still pending approval, not attempted.

## General verified embedding
E_r(i)=2^(floorlog2(i+1))*r+i. Proved left/right child identities, strict monotonicity/injectivity, depth(E_r(i))=D+depth(i) when root r has depth D, finite bound into global height D+h for local height h, proper root exclusion r>0, and disjointness of all vertices of distinct fringes rooted at same depth.
`decode` is a partial inverse defined using Classical.choose, with soundness and image completeness. `liftAction` maps all local operations into global coordinates and idles/noGhosts outside. No executable decoder claim; noncomputable classical definition, no native evaluation.
`liftConfig` combines local state with untouched outside configuration.
`lift_after_first/lift_after_round` exact transition commutation.
`lift_legal/lift_actions` physical run lifting under dependency closure; `fringe_dep_closed` discharges that closure for actual terminal heap fringes (same global bottom depth). Thus no closure assumption remains in `fringe_paper`.
`fringe_paper`: any local PaperRuns on height h becomes actual global PaperRuns of SAME depth on height D+h, starting/ending at embedded configs, all outside vertices unchanged. It preserves dependencies, active-neighborhood disjointness, ghosting, and legality. For r>0, global root is outside; `lifted_root_avoids` and frame connection verify it is never computed/uncomputed/ghosted.

## Remaining work
Exact global lifted work equality and space<=localpeak+outsidepebbles are NOT proved in this unit. Neither is simultaneous union of multiple fringe traces or budgeted batching. Although arithmetic injectivity and fringe disjointness needed for this are proved, cardinality transport remains. W<=3n matching smallspace upper is still unproved; E7 must not be reported as completing it. This is known-construction formalization infrastructure, no new upper/S claim.

## Validation
Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. E1/E2/E4/E6/E7 successful; E3/E5 failed retained. E7 UTC2026-11-15T17:18:53.368475--17:18:54.065188, CPU0.691549s, peak697663488bytes, rc0. Main dependencies propext,Classical.choice,Quot.sound; no sorry/admit/native_decide. No previous completed expensive computation repeated. New showa upload only; existing files unchanged.
