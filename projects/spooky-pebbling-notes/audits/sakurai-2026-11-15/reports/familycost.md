# FAMILYCOST C6
Completed concrete arbitrary-K synchronized fringe traces in original PaperRuns. No abstract RoundProduct premise remains in fringe_sync/fringe_cleanup.
Assumptions: pairwise distinct heap roots at common depth D, terminal fringe height h (local m=2^h-1, global N=2^(D+h)-1); consistent exterior and local states; equal local trace depth d. Arbitrary K including zero.
work: exact global roundWork=sum local roundWork, with proper action lengths.
space: exact global union-space=sum local round union-spaces + exterior pebble count ONCE. This exterior is the untouched complement of all selected fringe images, not summed K times.
product/fringe_product: actual simultaneous PaperStep plus exact state/work and space. Uses concrete decoder/Legal theorem from F13.
fringe_sync: actual PaperRuns common depth d, final product state, work exact sum, peak<=sum local peaks+exterior. No sequential-legality substitution.
fringe_cleanup: local initial P empty, arbitrary consistent ghosts; actual global PaperRuns depth2h, final all selected fringes empty/outside unchanged, W=2K(2^h-1), S<=K(2^h-1)+exterior.

Remaining for matching upper: batches under total space budget, initial/top-skeleton construction and retained-root cleanup; full global W<=3n and O(HlogH) at S=Theta(n/H). Current theorem is a construction component, not full matching upper or novel S result. Lee baseline and original-paper prose-model audit remain separate.

Lean4.35.0 arm64 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, C6 rc0, propext/Classical.choice/Quot.sound only, no sorry/native. Failed C1/C2/C3/C5 logs retained; C4/C6 succeeded. Generated matcher conversion handled with explicit equality transitivity, no axioms.
Budget600s, per callCPU30s/wall60s/1GiB/-j1. AllSTOP. Predecessor F13 STOP and worklog1726 confirmed. No duplicate task/job or reexecution. Mikawa approval-blocked transfer never retried. New local/showa only.

SourceSHA 13b11e474ab74e06f8f0ed27390e21c66de0f260c91ded837902a5914959e541
{
  "id": "SPOOKY-FAMILYCOST-20261115-C6",
  "start": "2026-11-15T18:01:59.526322+00:00",
  "cmd": [
    "<home>/.local/bin/lean",
    "-j1",
    "-M1024",
    "-o",
    "FamilyCost.olean",
    "FamilyCost.lean"
  ],
  "stop": "2026-11-15T18:01:59.823620+00:00",
  "exit_code": 0,
  "wall": 0.29707249999999996,
  "cpu_seconds": 0.291717,
  "peak_bytes": 676380672,
  "output_sha256": "ef324122c80921843ebf996086b3ca104e2789c5f7162cad6fa7f7c68c40c436"
}