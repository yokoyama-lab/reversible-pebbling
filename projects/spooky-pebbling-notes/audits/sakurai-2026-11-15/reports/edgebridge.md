# Legal-to-edge-table bridge: partial finite verification checkpoint

SPOOKY-EDGE-BRIDGE-20261115, sole owner /root/spooky_dp. This is not a completed physical Pareto theorem or an S novelty result.

## Structural Lean progress
SpookyRound.mem_optActions proves exact membership equivalence between the original Legal action-word enumerator and a factored enumerator. First-phase words are filtered for pairwise-disjoint active sets and all old-state preconditions; ghost masks are then filtered separately. The proof does NOT weaken the original Legal predicate. Dependency: propext, Classical.choice, Quot.sound, no native axiom.
EdgeBridge.checkOne_sound translates a canonical-list equality check into weighted successor-set equivalence. Sorting/duplicate removal preserve membership; the check compares actual decoded configurations and weights, not only hashes. mem_real identifies the factored successor relation with PaperStep.
EdgeBridge.transfer_runs: assuming every one of2187 finite configuration checks succeeds, every physical PaperRuns is transferred to the embedded edge-table Runs with identical depth/work/space and decoded state.
EdgeBridge.physical_lower: under that SAME explicit all-configuration-check assumption, every goal-reaching physical run is dominated by one of the five (D,W,S) points. Thus the remaining gap is a concrete finite certificate, not an unproved pruning algorithm. The statement starts at decode(table.start); this is intended empty and must be explicitly connected to an independently stated empty configuration in the final theorem.

## Completed versus unfinished checks
Initial16 configurations and the next256 configurations (indices0..271) passed native certificate checks. Shard0 real CPU25.231307s, rc0. Completed .olean files are preserved for reuse with the fixed Lean version. Later256-state shards hit CPU30sec, signal exit-24; that means resource limit, NOT counterexample or completed verification. Exact final shard status is in checkpoint.json and the per-call execution receipts. No successful shard should be rerun just because this finite assignment ends. Split only stopped/unfinished index ranges into smaller shards, e.g.64 or32 states, or optimize canonicalization while retaining the membership proof.

## Trust and scope
Lean4.35.0 arm64 Apple commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Structural transfer proof has no native axiom. Concrete per-state checks use native_decide. Conditional physical_lower additionally depends on native checks for goal decoding and the earlier closed-frontier/start/goal-table facts. No sorry in successful structural compilations; failed attempt outputs are retained and are NOT counted as proofs.
BridgeBase.lean SHA256 a5af77e5a97683c031fe34fd2f51d9b1c1d015a8c950fe664d9542cce3814220.
Transfer.lean SHA256 701343026c1f7f3c365e964e2f91221b09241b8ac6556ec0ca4fbe55632f3e4f.
Transfer compile START2026-11-15T14:40:19.637138Z STOP14:40:19.920063Z rc0 CPU0.277992s peak665960448bytes. Per-call CPU30/wall60/Lean-j1-M1024, total600wall reservation. No time or memory limit was raised; maxRecDepth was adjusted only to elaborate finite array syntax. CPU-limit signal was delivered around31seconds by the OS.

Prose-to-formal Legal model remains human-reviewed, even after full edge verification. Lee et al. §5.3 existing joint bounds remain prior results; no asymptotic novelty follows from n7. Earlier five feasible witnesses are retained separately. Full physical frontier requires completing ALL finite configurations, removing the explicit hall assumption, and joining those witnesses in one theorem.
