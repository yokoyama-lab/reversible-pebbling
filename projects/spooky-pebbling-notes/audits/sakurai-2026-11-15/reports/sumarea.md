# SUMAREA S3: original PaperRuns finite lower bound

Finite unit owner spooky_dp. Prior DEPTHAREA D3 STOP and log row1704 confirmed. No parallel assignment for this same sum/cut bridge known; no old successful computation rerun. Reservation: 600 wall seconds total; each Lean CPU30s/wall60s/1GiB, one thread. All calls stopped.

## Main verified theorem
`SumArea.paper_finite_lower` for every H,ell with n=2^H-1>0:
- original `PaperRuns HeapPath.pred d q r`;
- every initial vertex non-pebbled (stronger empty start included);
- final root pebbled and every nonroot empty;
- actual work <= 3*n+e; actual union-space <= s;
proves

    (2*ell+1) * (n-(e+2*s+1)-(2*e+4*s+3)*(2^ell-1)) <= d*s.

All subtraction is truncated Nat subtraction. NO separately assumed cut, good forest, counts, clocks, coverage, or area premise. H and ell are arbitrary, not finite instance checking. Common last-root-compute cut selected from actual run. Union-space bounds both cut configuration and suffix. Forest good count is n minus accounted removed vertices, components bounded by 2e+4s+3. Each actual good vertex contributes 2*forestDepth+1 minimum clock span. The shallow count and complementary deep weight are summed and connected by heap-label coverage to actual per-vertex area; actual round area <= suffix depth*s <= d*s.

## New source chain
`pair_labels`, `filter_sum`, `pair_sum`, `actual_pair_sum`: exact sum bridge.
`deep_weight`, `partition`, `forest_deep`: weighted deep-node bound.
`actual_weight_area`, `actual_forest_lower`: arbitrary actual suffix.
`size_labels`, `good_removed`, `occurrence_space`: final size/cut/space bridges.
`paper_finite_lower`: final finite inequality.

## Verification
Lean4.35.0 arm64 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
S1 failed (rewrite matching and arithmetic proof); failure output retained; its sorryAx is not an accepted result.
S2 rc0 sum/suffix layer. S3 rc0 full original-run connection.
S3 UTC 2026-11-15T16:49:44.676814 to 16:49:45.119564, CPU0.441984s, peak687079424bytes.
Successful main theorem axioms ONLY propext, Classical.choice, Quot.sound. No sorry, admit, native_decide; no native evaluation axiom.

## Scope and remaining work
The proposed asymptotic consequence D=Omega((n/s) log(n/(s+e+1))) in a suitable nondegenerate range is NOT formalized here; finite theorem only. Model-to-original-paper prose independent audit remains separate. Prior-paper novelty not established; do not claim S-grade outcome or novel theorem merely from formalization. Existing Lee joint bounds and fixed-stage constructions remain comparison baselines.
No Git merge/publication, new costs, permission expansion, or existing showa overwrite. Mikawa export remains blocked pending approval and was not attempted; local archive and authorized new showa upload are separate.
