# BATCHEDCLEANUP B4
Actual original-PaperRuns cleanup batch composition from an arbitrary global configuration.
restrict/reconstruct: local projection at actual embedded heap labels reconstructs original global configuration.
global_cleanup: selected fringe vertices initially have no pebbles (arbitrary consistent ghosts). Cleans ghosts/pebbles there, outside unchanged; all initial pebbles pointwise preserved, including a retained root. D2h,W2K(2^h-1),peak<=K(2^h-1)+initial pebble count.
batches: for b valid batches of K distinct roots at common depth D, terminal height h, actual PaperRuns D=2hb,W=2bK(2^h-1),peak<=K(2^h-1)+initial pebble count. Batch count does NOT multiply the space bound. Validity means initial selected regions are pebble-free; pebble preservation makes this remain valid. Exact final state cleaned is sequential clear of each selected region.
cleaned_no_new_ghost/cleaned_selected: no ghost introduced; any vertex covered by a batch has no final ghost.

IMPORTANT limits: batches may repeat regions; no partition/no-duplicate claim here. Complete whole-tree preparation/budget grouping/top-skeleton cleanup is not proved, so W<=3n and D=O(HlogH),S=O(n/H) global upper remains incomplete. Simply emptying every terminal fringe leaves upper skeleton dependencies absent. A next construction component should retain fringe-root pebbles at the end, then recompute/uncompute the upper skeleton while retaining global root. Current theorem preserves pre-existing outside/root pebbles, not newly creating/retaining every fringe root. No novel/S outcome claim. Lee baseline maintained; original prose-model audit separate.

Lean4.35.0 arm64 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. B4 rc0 standard propext/Classical.choice/Quot.sound only; no sorry/native. B1/B4 success; B2/B3 failed retained. Finite600s/per callCPU30s/wall60s/1GiB/-j1. All STOP. PredecessorC6 stopped/worklog1727 readback. No duplicate jobs or reexecution. Mikawa approval-blocked export never retried; local/showa new only.

SourceSHA 8a6f56096bd8f4050badb781ce25c09d4e74f17853bdc05c87b72698a564b517
{
  "id": "SPOOKY-BATCHEDCLEANUP-20261115-B4",
  "start": "2026-11-15T18:07:37.511965+00:00",
  "cmd": [
    "<home>/.local/bin/lean",
    "-j1",
    "-M1024",
    "-o",
    "BatchedCleanup.olean",
    "BatchedCleanup.lean"
  ],
  "stop": "2026-11-15T18:07:38.030380+00:00",
  "exit_code": 0,
  "wall": 0.518225125,
  "cpu_seconds": 0.51113,
  "peak_bytes": 682098688,
  "output_sha256": "6058d6297268e683155917d5801dd940800f0508cff19108fb8d8b23ed3d2aa8"
}