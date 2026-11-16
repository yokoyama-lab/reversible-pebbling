# Small complete-tree Pareto experiment and Lean witnesses

ID SPOOKY-SMALL-PARETO-20261115. Owner /root/spooky_dp. Finite assignment only, no S novelty claim.

## Results (W,D,S)
- n=3 (height2): (5,3,3). Python all27 configurations/340 edges. Existing concrete Lean DP executed depths0,1,2,3 and returned no goal at0..2 and exactly (W,S)=(5,3) at depth3.
- n=7 (height3): (13,5,7), (14,7,6), (16,8,5), (15,9,5), (17,12,4). Python reached all2187 configurations, generated558592 weighted/action edges, and nondominated propagation converged after depth12.
- At space5, the experiment exhibits the work/depth alternatives (15,9) and (16,8). This small example is not a general work-depth theorem.

Each of the five n7 schedules is checked against the existing Lean concrete-round Legal predicate. Certificates.certificate0 through certificate4 prove that the recursive checker returns true with the claimed work/peak and that the list has the claimed depth. All five use only propext, no sorry or native_decide axiom. check uses the original Legal, afterRound, roundWork and union roundSpace definitions, ending at root-only/no-ghost. These are feasibility witnesses, not machine-checked lower bounds.

## Exact convention and unresolved connections
Read source https://arxiv.org/html/2610.09434v1 §2.2–2.3. Edges child→parent; root0, children2v+1/2v+2. Initial empty; goal root pebble only and no ghosts. First-phase compute/uncompute active sets pairwise disjoint, old-state predecessor preconditions. Second-phase arbitrary ghost subset. Ghost-only rounds cost depth1 and work0. Space is |P_before union P_after_firstphase|. Idle rounds admitted but dominance removes them.

Python enumerates every independent first-phase vertex subset; operation at a selected vertex is uniquely pebble/unpebble according to initial presence. Every subset of post-first-phase pebbles is then ghosted. Same-state labels (work,depth,peak) are discarded only when componentwise dominated. Costs are nonnegative; repeated configurations can be removed from a path without increasing work,depth,peak, giving simple-path bound3^n-1. These are algorithm correctness arguments, NOT Lean proofs for this Python implementation or its pruning. The existing Lean DP theorem covers the unpruned action-word DP, not Python's optimized independent-set graph or dominance. General checker→PaperRuns soundness, full n7 exhaustive kernel evaluation, and lower-bound certificates remain open. Prose-to-formal-model matching is human-reviewed, not a Lean theorem.

## Reproduction and bounds
Files: pareto.py, run.py, SmallTree.lean, Certificates.lean, make_cert.py, pareto-n3.json and pareto-n7.json, reservation, START/STOP receipts and logs. Run python3 run.py NEWID python3 pareto.py 7; Lean command <home>/.local/bin/lean -j1 -M1024 Certificates.lean.
Lean4.35.0 arm64 Apple commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Python3.9.6.
Reserved max600 wall seconds total, each subprocess CPU30/wall60, Lean memory1GiB. Python memory was measured (peak105054208 bytes) but not OS-hard-limited; this is a bound-enforcement limitation, not a claim of enforced1GiB. No large-tree job started. Observed all processes exited; no pending attempt.

PY7B START2026-11-15T14:11:02.197949Z STOP14:11:03.117231Z rc0 CPU0.916331s peak105054208 bytes.
CERT7B START2026-11-15T14:12:39.963667Z STOP14:12:41.041153Z rc0 CPU1.080028s peak734527488 bytes.
LEAN3B START2026-11-15T14:10:24.567669Z STOP14:10:25.182591Z rc0 CPU0.617977s.
Failed attempts retained: LEAN3 absent order instance for printing; PY3/PY7 Python3.9 bit_count absent; CERT7 generation variable collision causing missing file. Corrected only after observed exit; no unresolved job restarted.

No private/public repository changed; no merge; no new cost or permissions. Completed serialization/abstract DP reserved scopes remain unchanged. Local spooky-critic files concerned different relaxed large-height inequality searches, not this exact small configuration enumeration. Outcome is verified witness infrastructure plus finite Python evidence, not S-level general result. A useful next finite proof unit is checker soundness and dominance-pruning soundness.
