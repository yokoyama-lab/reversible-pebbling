# Last-root-cut charging and a C=3 depth lower-bound candidate

Task SPOOKY-CUTBOUND-20261115, owner /root/spooky_dp; previous FIXEDC STOP. Finite reservation600wall, per subprocessCPU30/wall60; Lean-j1-M1024. No old exact7 search/shard restarted. This unit supplies a mathematical proof draft, partial general Lean lemmas and finite falsification checks. It is NOT yet a fully connected Lean theorem about arbitrary PaperRuns, nor a verified novelty/S claim.

## Mathematical proof draft: universal work cut
Fix a successful execution of a complete binary tree with n vertices, empty input and root-only/no-ghost output. Let tau be the end of the round containing the LAST computation of the root. There can be no later ghost or uncompute of root: either would require another root computation for the final output. Let p<=s be the pebbles at this cut (root included).
Every vertex has been computed at least once by tau, by following root dependencies backwards. Every nonroot vertex has a final uncomputation AFTER tau. For a child of root this follows because it is pebbled during the last root computation and ends empty; ghosting does not by itself achieve an empty final state, so some later uncompute is necessary. Induct downwards: at the parent's last uncompute its children must be pebbled, and they must later become empty. Parent and child cannot uncompute in the same round, since their active sets overlap. Thus each child's final uncompute is strictly later. The scalar no-ghost-debt disappearance fact is formalized in CutBound.cleanup_required.
Every vertex absent as a PEBBLE at tau needs a later compute before that final uncompute. Ghost and empty cut states both count as absent. Work therefore pays at least n pre-cut computes, n-1 post-cut uncomputes, and n-p post-cut computes:
  W >= 3n-p-1 >= 3n-s-1.
This is a simple accounting lower bound, possibly known. Novelty not established. It implies C<3 infeasible asymptotically when s=o(n).

## Stronger candidate with additive excess
Assume W<=3n+e, e>=0. The above mandatory operations leave at most e+p+1 extra work. Remove (i) all p cut-pebbled vertices; (ii) every other vertex with more than one post-cut compute or more than one post-cut uncompute. Every vertex in(ii) consumes at least one EXTRA charged operation, so the removed set has size B<=e+2p+1<=e+2s+1. Any uncomputes before the cut or extra pre-cut computes only reduce the remaining slack; they cannot invalidate this bound.
The good induced forest has N=n-B vertices and K<=2B+1 connected components (removing a vertex of undirected degree at most3 increases component count by at most2). Each component is rooted in the original direction and has at most two children per vertex. Every good vertex has exactly one compute c(v) and one uncompute u(v) after the cut. It cannot be ghosted between them, because that would require a second compute before uncompute. Thus it has one continuous live interval.
For a good parent v and good child w,
 c(w)<c(v)<u(v)<u(w).
Preconditions use the old configuration; adjacent active sets cannot share a round. Hence intervals are strictly nested, and a good vertex at component-depth d has live boundary duration at least2d+1. (Using round-union occupancy gives an extra unit, not needed here.) The total of these durations is at most A, the sum of actual round-space unions, and A<=sD.
At most K*(2^ell-1) good vertices have component-depth below ell. Therefore, for EVERY integer ell>=0,
 sD >= (2ell+1) * max(0, N-K*(2^ell-1)).
This explicit finite inequality avoids applying a logarithm at an invalid/empty-forest boundary. Together with B<=2s+e+1,K<=2B+1 it gives the coarse form Omega(n log(n/(s+e+1))) cumulative area whenever s+e+1=o(n), hence
 D = Omega((n/s) log(n/(s+e+1)))
in that regime. For e=0 and s=Theta(n/H), this becomes Omega(H log H), matching the prior-based W<=3n-1 upper construction in order. For e=Theta(n), the argument need not give a useful logarithmic bound; do NOT extend it to C4 or claim a full fixed-C hierarchy. The fixedc report already supplies a C4 O(HloglogH) counterexample to such an extension.
This is the promising new proof direction, but full semantic formalization and novelty review are outstanding. The statement is not labeled a completed research theorem yet.

## Independent audit
/root/lower_audit independently read Lee §2.2–2.3 and found no structural counterexample. It confirmed strict interval nesting and binary-forest depth-sum argument, with the warning to restrict asymptotic parameter ranges and separately justify round-union area. Parent received this report. This is human/agent mathematical review, not a Lean replacement.

## Lean-proven components
CutBound.lean defines a scalar three-state legal trace (empty/pebble/ghost). cleanup_required says ending empty from nonempty requires uncompute; missing_requires_recompute says an initially nonpebbled vertex whose trace includes uncompute must compute first. Abstract per-vertex accounts then imply3*vertexCount<=work+space+1 when explicitly supplied valid cut accounts and exactly one root.
Intervals.lean defines nested compute/uncompute intervals. span_by_depth proves duration>=2depth+1. depth_layer_charge sums this at any depth threshold; forest_charge converts an EXPLICIT shallow-node-count hypothesis to the displayed finite area charge.
All successful theorems are general in list lengths/numeric parameters, no native_decide/sorry/admit. Dependencies propext,Quot.sound (scalar recompute lemma propext only). Lean4.35.0.
MISSING connections: arbitrary PaperRuns to scalar traces; existence/order of final uncomputations; constructing valid cut accounts; bounding/removing bad vertices from total work; heap-tree forest decomposition and shallow-node counts; charging extracted intervals to actual roundSpace sums. Thus these Lean modules do NOT yet prove the claimed complete C3 lower bound.

## Finite audits, not universal proof
49 ghost-block schedules, heights2..8, single cut or two-cut chain terminating at height1. New analyses of cut-time counts and good intervals, not reruns of an optimum search. All valid-account, exception-count, component-count, strict nesting, layer-charge and area<=sD checks passed. Audit uses original before/after-first-phase union. It does not search all schedules, prove no counterexample exists, or imply optimality.
B1 compile START2026-11-15T15:24:39.374090Z STOP15:24:39.695323Z rc0 CPU0.315311sec peak673923072bytes.
INTERVAL1 failed proof tactic simplification; INTERVAL2 START2026-11-15T15:28:15.829497Z STOP15:28:16.125878Z rc0 CPU0.290116sec peak668991488bytes.
CUTAUDIT rc0 CPU0.035239sec; INTERVALAUDIT START15:29:12.637003Z STOP15:29:12.671838Z rc0 CPU0.032478sec, measured peak13893632bytes. Python memory measured/not hard-capped, bounded schedules n<=255.

## Literature status
https://arxiv.org/html/2610.09434v1 §5.3 eq38 remains the known joint-bound baseline. It yields Omega(H lambda(n)^2) at fixed C,s~n/H but does not itself yield the proposed C3-specific log H bound. Search phrases spooky pebbling 3n and reversible pebbling 3n space did not locate an exact match; this limited search is NOT evidence of novelty. A targeted audit of bounded-recomputation/read-once reversible-pebbling lower bounds is required before making any novelty claim.
