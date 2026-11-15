# Exact 7-vertex work–depth–space frontier in the formal PaperRuns model

Task SPOOKY-EDGEFAST-20261115, sole owner /root/spooky_dp. This completes the previous finite edge-table verification gap. It is a rigorously checked small instance, NOT an S-level asymptotic result or a claim of novelty.

## Final theorem
ExactFrontier.exact_frontier states, for every natural budget D,W,S:
there exists a formal PaperRuns execution from empty to root-only/no-ghost, using at most D rounds, W work and S peak space
IFF one of these five triples (D,W,S) is componentwise at most the budget:
(5,13,7), (7,14,6), (8,16,5), (9,15,5), (12,17,4).

Consequently these are exactly the Pareto-minimal triples of this 7-vertex formal model. In work/depth/space order they are (13,5,7),(14,7,6),(16,8,5),(15,9,5),(17,12,4). Depth is unbounded in the theorem; this is not merely an experiment through depth12.

## Proof chain
Original Legal action-word enumerator → proven equivalent factored enumerator (mem_optActions).
Every one of2187 decoded configurations has equal weighted successor sets in the formal enumerator and embedded table (all_edges). Original checks0..271 were reused from saved .olean; only indices272..2186 were newly evaluated in15 shards.
A closed6947-label frontier on that table bounds all-depth executions.
transfer_runs preserves state/work/depth/peak from PaperRuns into the table. The initial empty state and final root-only condition are explicitly connected.
Five existing concrete certificates are translated by check_sound into PaperRuns witnesses.
Lower and upper directions combine in exact_frontier. No outstanding all-edges assumption remains in this formal theorem.

## Efficiency change, not a model change
canonFast caches each edge's ordering key before sorting and duplicate elimination. mem_canonFast proves it preserves membership. It compares actual results, not hashes alone. This reduced new128-state shard times to roughly1.6–5.4 CPU seconds; old256-state shards had exceeded30 seconds. The failed older jobs were confirmed STOP before resuming. Successful prior272 configurations were not recomputed.

## Trust and limits
Lean4.35.0 arm64 Apple commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
No sorry/admit/sorryAx in final successful theorem. Dependencies: propext, Classical.choice, Quot.sound, plus23 native_decide evaluation axioms (17 edge shards, index coverage, goal decoding, empty-start check, frontier closure, frontier goal values and start coverage). Therefore this relies on Lean's compiled/native evaluation and is NOT purely kernel-evaluated or axiom-free. Full axiom list is in output-EXACT2.log.

Original paper https://arxiv.org/html/2610.09434v1 §§2.2–2.3 was human-read and modeled using old-phase dependencies, pairwise-disjoint active sets, second-phase ghosts, one depth per round, work on compute/uncompute only, space |P_before union P_after_firstphase|, empty start, root-only/no-ghost goal. The correspondence of that prose and intended application to our formal definitions remains a separate HUMAN modeling check, not something Lean proves. No general-n or general-DAG result follows.
Lee et al. §5.3 already gives joint work–depth lower bounds and optimal-depth regimes; those are prior results, not rediscovered contributions here.

## Execution and reproduction
New reservation600wall total; each subprocessCPU30/wall60, Lean-j1-M1024. Existing budgets not raised. All new finite shards exited0. Limits preserved; no external job, schedule, permission or public repository changed.
Final EXACT2 compile START2026-11-15T14:52:41.459170Z STOP14:52:42.365692Z rc0 CPU0.900049s wall0.906310s peak711901184bytes.
ExactFrontier.lean SHA25603bca4e515bb7dc5bb41a241b401c06a4ccfe2a6ee5e5ed7e90fea144140e005.
Complete.lean SHA25640fc68edebd6aca8faae4cb4d87ec7db4666d40f5a8395f2e5c4fd315f0043db.
FastBase.lean SHA2565f9f7cca6cb4abfc0bfaf683183ce0db9d667d17df2b103fe6ff5d54167af0cd.
Output SHA25635e6e4c28cff050acfc102278851c435a1b4dc62397e5739b69c76aaf81bb872.

Bundle contains all imported source and saved .olean checkpoints. With the same Lean4.35.0 use LEAN_PATH=. lean -j1 -M1024 ExactFrontier.lean. To rebuild source-only, compile BridgeBase and Shard0 first, FastBase, Fast0..Fast14, Physical, Complete, ExactFrontier in that order, using -o MODULE.olean. Rebuilding is optional independent verification, not a task to repeat completed work automatically. Failed aggregation attempts are retained but not proofs; successful EXACT2 supersedes them. checkpoint-complete.json records all15 new shard receipts and full source hashes.
