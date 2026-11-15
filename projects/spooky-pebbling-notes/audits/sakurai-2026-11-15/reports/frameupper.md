# FRAMEUPPER R4: retaining a protected root through cleanup

Owner spooky_dp, prior FILLUPPER F5 STOP/log1712 confirmed. Finite reservation600s wall, eachcallCPU30/wall60/1GiB, allSTOP. Existing unrelated novelty audit retained. Mikawa blocked pending approval and not attempted.

## General physical frame theorem
`frame F q` adds pebbles on F and removes ghosts there. `Avoids F a` requires all selected vertices idle and not ghosted by each round. `frame_first/frame_round` prove exact transition commutation. `frame_legal` proves legality in the framed configuration from original legality, including old-configuration dependency checks. Added fixed pebbles cannot invalidate operations off F.
`frame_space` proves true first-phase-union space <= old round-space + card F, not endpoint space.
`frame_actions` and `protected_run` lift a whole actual ActionRuns trace into actual PaperRuns, preserving exact depth and work, framing final state, with peak space <= old peak+card F.
`protected_root` specializes F to one vertex: a run not computing/uncomputing/ghosting the protected root can retain its pebble throughout, same depth/work and at most one extra space. Exact singleton cardinality1 is proved. Initial and final configurations are framed explicitly; no assumption that ghosting is charged as work.

## Remaining scope
This completes general root/frame retention, not arbitrary heap subtree relabeling or all fringe batching. The F5 complete-tree cleanup must still be embedded on proper disjoint subtrees to establish Avoids on global root; F5 itself operates its own local root and must NOT be plugged directly into protected_root at that same vertex. Also remaining: cross-block dependencies and active-set disjointness, resource bound per parallel batch, first-stage preparation/top skeleton, exact W<=3n overall and fast depth/smallspace. No matching upper theorem claimed. Existing Lee construction is baseline, no novel upper claim.

## Verification
Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. R1/R3 failed and retained; R2/R4 succeeded. R4 UTC2026-11-15T17:11:05.100957--17:11:05.467373, CPU0.361057s, peak675217408bytes, rc0. protected_run axioms propext/Quot.sound; protected_root adds Classical.choice. No sorry/admit/native_decide in successful results. Failed output does not count as proof.
