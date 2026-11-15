# FAMILYSYNC K4
Arbitrary finite K synchronized PaperRuns lifting, with an EXPLICIT RoundProduct one-round interface. sync proves common depth, exact sum of work, and peak <= sum of local peaks + exterior ONCE, including K=0. sync_uniform specializes equal work/space budgets. family_cleanup composes existing full_storage_cleanup to depth 2h, work K*2*(2^h-1), space <= K*(2^h-1)+exterior.

CRITICAL LIMIT: RoundProduct.step is an explicit hypothesis, not yet constructed for arbitrary K physical fringes. It requires actual simultaneous PaperStep, product-state update, exact work, and per-round space bound. The preceding T4 only discharges concrete two-fringe composition. This unit must not be called unconditional arbitrary-fringe synchronization or a matching W<=3n upper theorem. Remaining: concrete finite-family decoder and independent simultaneous legal action, exterior counting; batching/first-stage/top-skeleton/root preservation; global small-space W<=3n and depth O(H log H).

This is proof infrastructure, NOT a new lower bound, novelty result, or S claim. Existing Lee upper constructions remain the baseline. Original-paper prose/model correspondence remains separate.

Lean 4.35.0 arm64, source commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Successful K4 exit0. Axioms: propext, Classical.choice, Quot.sound. No sorry/native_decide dependency. K1/K2 were failed compile attempts retained; their placeholder/sorryAx output is NOT proof. K3/K4 succeeded.
Finite budget: 600s overall, 30CPU seconds per call, 60s subprocess wall, 1GiB Lean -M1024, -j1. No background job. Scope owned solely by spooky_dp; preceding T4 STOP/readback row1722 confirmed. No existing research job restarted. All original dependencies are copied unchanged. Mikawa transfer remains approval-blocked, never retried; this artifact is independently authorized local/showa NEW save.

Source SHA256: 73d20681ec73a2eae3a570ba1408cd040bdde8bfad71919d657b15129d9af237

K4 execution:
```json
{
  "id": "SPOOKY-FAMILYSYNC-20261115-K4",
  "start": "2026-11-15T17:43:41.076255+00:00",
  "cmd": [
    "<home>/.local/bin/lean",
    "-j1",
    "-M1024",
    "-o",
    "FamilySync.olean",
    "FamilySync.lean"
  ],
  "stop": "2026-11-15T17:43:41.663524+00:00",
  "exit_code": 0,
  "wall": 0.587099875,
  "cpu_seconds": 0.328561,
  "peak_bytes": 678723584,
  "output_sha256": "b66d51df4405be56094d559b708f6abd7525206fd2f10df7c7af0bda92b2d15a"
}
```
