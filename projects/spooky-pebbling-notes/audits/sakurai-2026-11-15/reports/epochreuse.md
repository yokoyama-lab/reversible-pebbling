# EPOCHREUSE E2: a quantitative two-epoch incidence candidate and a wrong charge refuted
Owner /root/spooky_dp, F2 stopped, no duplicate job. 600wall unit; each compile30CPU/60wall/-M1024/-j1. No <host> transfer.

## Precise candidate: parent-side merge budget (not yet formalized from ActionRuns)
An occupancy epoch of v starts at compute(v) (or initial pebble) and ends at its next ghost/uncompute. Create one vertex for each epoch. For each compute/uncompute of parent v, connect its parent epoch to the current OLD-state epoch of each child u. Collapse multiple references of the same parent epoch to the same child epoch into ONE incidence. For child epoch e, let r_e be the number of DISTINCT parent epochs incident to e. In a binary tree let k_v be the number of epochs of internal v.
Candidate geometric lemma:
  sum over child epochs e of max(r_e-1,0) <= 2 * sum over internal v of max(k_v-1,0).
For an empty-start run k_v=C_v. For a suffix starting with pebbles, add the initial-pebble indicator. This is a merge budget, NOT an area or depth lower bound.

Reason to expect factor2: for a fixed physical parent/child edge, each parent epoch references at most two child epochs (its compute and possible uncompute). Their child-epoch labels are ordered. Between consecutive parent epochs the endpoint labels satisfy a<=b<=c<=d, so the sets {a,b} and {c,d} share at most one label. Over k parent epochs there should be at most k-1 repeated memberships; two children give factor2. ordered_overlap proves the four-label intersection lemma in Lean. Actual epoch extraction, global telescoping and the displayed full sum are still unproved in Lean. Do not silently treat the desired event graph as a forest: merge incidences remain and may be linear in n at C4.

## Stronger but false child-side charge
Rejected claim: reuse of a child epoch by two parent epochs requires an extra compute of that CHILD. Legal full binary7 clean example:
round0 compute leaves3,4,5,6;
round1 compute internal1 then ghost1;
round2 compute internal1 and internal2;
round3 compute root0;
round4 uncompute internal1 and2;
round5 uncompute all leaves.
Lean actual proves the complete ActionRuns; properties proves work14, peak7, clean root-only/no ghosts, child3 compute1/ghost0, parent1 compute2/ghost1, child3 referenced3 times. child_held proves four occupied child-boundary rounds after leaf compute. One child epoch is reused by two parent epochs without any child recompute. Both children3 and4 do this: two merge incidences for one additional PARENT epoch, realizing candidate factor2. This is finite actual validation of the candidate's sharpness, not proof of its general statement. It is not a small-space asymptotic C4 counterexample.

## Relation to C4
Parent-side extra epochs must be charged to actual work, not duplicated across children without the binary factor. Even if the candidate holds, W<=4n still permits O(n) merges. A separate scale/area argument must show why those merges cannot eliminate all second-scale branch cost. Nothing here yields Omega(H logH) at C4; such a conclusion would contradict the known repeated-block upper order O(H loglogH). No C4 area theorem/S novelty claim.

E2 2026-11-15T20:49:41.684743Z–20:49:42.059874Z rc0 CPU.36837s peak685867008B. Lean4.35.0 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Actual finite theorems propext only (kernel decide); ordered_overlap propext,Quot.sound. No native/sorry. E1 also succeeded before abstract overlap lemma. Existing sources/artifacts unchanged.
