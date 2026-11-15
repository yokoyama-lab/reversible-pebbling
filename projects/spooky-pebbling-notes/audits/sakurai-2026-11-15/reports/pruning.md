# Same-state Pareto pruning and witness-checker soundness

Finite task SPOOKY-PRUNING-CHECKER-20261115, owner /root/spooky_dp. Verification infrastructure, not an S novelty claim. Parent-assigned continuation of the same sole DP owner. All earlier finite computations had exited; no existing job restarted. No large experiment, n15 run, new schedule, permission or cost.

## Lean-proved connections
1. Certificates.check_sound: if the recursive witness checker returns true from q with accumulated work w/space s, an actual PaperRuns execution of exactly the list length exists, ending in goal7, with w+r.work=W and max(s,r.space)=S.
2. Certificates.feasible0..4: the five n7 schedules give actual PaperRuns witnesses for (W,D,S)=(13,5,7),(14,7,6),(16,8,5),(15,9,5),(17,12,4). These are feasibility, not optimality assertions.
3. SpookyRound.append_runs: concatenate two PaperRuns, adding depth and work and taking maximum peak space.
4. SpookyRound.same_state_prune_safe: a feasible prefix reaching the SAME configuration with no larger depth,work,peak can replace a dominated prefix for every feasible continuation, preserving the continuation's final state and not increasing any cost. It does not say that prefixes to different configurations can be compared. The dominated prefix's feasibility assumption is logically unused because the conclusion only constructs the dominating continuation; retained for interpretation, with a compiler warning.
5. SmallTree.run_three/result_three: a 3-round run on the n3 tree achieves work5,peak3 and the exact goal.
6. SmallTree.no_goal_lt_three/depth_min_three: no goal run with depth<3 exists in the formal model. This uses finite DP completeness plus native_decide evaluation (see trust below), giving optimal depth3 with the previous witness. No full work/space Pareto lower bound is asserted by this theorem.

## Trust and compile
Lean4.35.0 arm64 Apple, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Source Pruning.lean SHA256 b3601d6d49edfb89bb7bbeb1fb8080e5195071ae1a5e477a287141e4cc73ef2a.
check_sound, same_state_prune_safe, feasible0..4 use propext and Quot.sound; append_runs uses propext. The actual n7 Boolean certificate checks use propext. No sorry/admit/sorryAx in the final successful compile.
IMPORTANT: depth_min_three and no_goal_lt_three additionally depend on Classical.choice and shallow_no_goal_eval._native.native_decide.ax_1_1. Direct kernel decide exceeded the configured1GiB memory bound (SOUND3); the limit was NOT increased. Re-evaluation with native_decide succeeded. Thus these depth lower bounds trust Lean's compiled/native evaluation, unlike the purely kernel-checkable structural proof units. Do not describe the entire file as axiom-free or native-free.

Final compile SOUND6 START2026-11-15T14:20:17.936577Z STOP14:20:19.311973Z rc0, CPU1.381431s, wall1.375213s, peak734937088bytes. Output SHA256 7daa994ad922df072e88f4995266f53f218d5c9beeb08bc5e6ca15634554b27a. Limits single thread, Lean-M1024, CPU30sec/wall60sec per subprocess; total600wall reserved. Warnings unused and_assoc and h2 only. Failed attempts and memory-stop logs retained. First attempt receipt inherited an older ID prefix; its actual source/log remains and was not rewritten; later receipts use the correct task prefix.

## What finite optimality still needs
The original Legal relation uses beginning-of-phase dependencies, pairwise-disjoint active sets, second-phase ghosting, and P_before union P_after_firstphase space from https://arxiv.org/html/2610.09434v1 §§2.2–2.3. Prose/model agreement remains human-reviewed.
The structural dominance theorem does NOT certify Python's actual implementation. To prove the n7 frontier complete, still establish:
- equivalence between Python's bitmask/independent-set edge generator and the Lean action-word successor relation;
- finite frontier invariant: every reachable bounded label is represented or dominated by a retained label at the SAME configuration;
- correctness of insertion, deletion, per-depth history replacement, and stopping/convergence checks;
- connection of the final exported table/certificate to the executed input source, with a checkable closure certificate;
- either a proved simple-path/state-count cutoff or a finite closed-frontier certificate, so omitted depths cannot hide a better run.
Feasibility witnesses already connect to PaperRuns; the outstanding proof is exhaustive exclusion, not existence. No general work-depth lower bound or S result follows from these small cases.
