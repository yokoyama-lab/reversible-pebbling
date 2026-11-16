# EPOCHSTATIC S1: static proof plan, not a Lean theorem
Owner /root/spooky_dp. No new computation reservation; no Lean, witness generation, or research shard executed. Old research reservation expired. Input: fixed audit.py SHA 7408d9f744424b71cf0718b4aa5bcb9b4342f7aef3370c7af88821b0e982f898, recovered from EPOCHINCIDENCE ZIP b04ed68da114bdb967d05532a78b0dc6557cbe89bfeda6f2b14579b697232573. Source inspected statically. Formal ActionRuns source not present in this cloud directory and NOT newly reread in this unit; comparison below uses prior validated model semantics and recovered executable audit, not a fresh Lean-source equivalence check.

## Definitions and phase convention
At OLD configuration of round t define c_v(t)=number of computes of v in rounds strictly before t; k_v(t)=1[v initially pebbled]+c_v(t). An initial ghost does NOT create an occupied epoch. An occupied epoch begins at initial pebble or a compute, and ends at uncompute or subsequent ghost, whichever removes that pebble. IDs are k_v(t) on an OLD pebble, and k_v(t)+1 on a compute in round t. Closed or ghosted epochs retain their historical integer counter but may not be used as an occupied reference.

For parent operation C or U on v in round t, and child u, record pair ((u,k_u(t)),(v,k_v(t)+1[C_v(t)])). All child IDs and membership preconditions refer to OLD state. Distinct occurrences of the SAME pair are collapsed. Define S_{v,i,u} as the SET of child IDs referenced by C/U occurrences belonging to parent epoch i. Ghosts are not parent reference operations. Let k_v=1[v initially pebbled]+total computes of v. Empty S are permitted.

## Concrete boundary checks against audit.py
* children(v,n)<=P is tested before Q=(P|C)-U; a child computed in this round cannot satisfy a dependency that was absent in OLD P.
* Closed active neighborhoods are disjoint. Thus child and its parent cannot both perform C/U in one round. Different compatible branches can act simultaneously; no ordering between them is needed in the per-edge proof.
* Ghosting is a second phase, gh<=Q. A child can be referenced in first phase and ghosted in the SAME round. This closes its epoch only after the reference; do not assume reference implies next-boundary occupancy.
* A parent can compute and then ghost itself in one round. Its epoch has a C reference but no later U reference. This epoch still contributes one to k_v. It cannot be discarded as a zero-duration boundary epoch.
* Initially pebbled parent can have only U as its first-epoch reference; initially pebbled child uses ID1. Initial ghost counters start0 and a later compute gives1. Final pebbled or ghost configurations require no invented terminal U.
* Within a parent epoch there is at most one C and at most one U; U ends the epoch. A ghost-ended epoch has no U in that epoch. Hence |S|<=2, but the proof below does not rely on this bound.
* Repeated C/U references to the same child epoch must be deduplicated within S. Counting occurrences instead of distinct pairs gives a false zero-recompute charging claim, even for a parent computed and uncomputed while its child stays pebbled.

## Abstract finite-set lemma (hand proof)
Fix a tree edge v->u and retain only nonempty S_1,...,S_q in parent-epoch order. Required hypothesis: for i<j and x in S_i,y in S_j, x<=y. For j>1, any x in S_j intersect union_{i<j} S_i satisfies x<=min S_j by the hypothesis, while x>=min S_j by membership. Thus the intersection has cardinal at most1. Finite union cardinality gives
  sum_j |S_j| - |union_j S_j| <= q-1 <= max(k_v-1,0).
For q=0 both sides on the left are0; q=1 the difference is0. The max convention handles k_v=0.

Time monotonicity should establish the hypothesis: every C/U reference of earlier parent epoch precedes every reference of a later parent epoch. First-phase active disjointness and one action per vertex exclude same-round U/C epoch changes. The child's compute counter is monotone in time. At a legal reference it is the ID of the actual occupied child epoch, not merely a stale counter. An initially occupied epoch behaves as the first epoch and does not alter the argument.

For this fixed edge, double-count distinct incidence pairs: sum |S_j| = sum_e r_e and |union S_j| = number of e with r_e>0. Therefore left side is sum_e max(r_e-1,0). In a tree every nonroot vertex has ONE parent, so summing over edges introduces no cross-parent reuse of a child epoch. For a full binary tree:
  sum_child_epochs max(r_e-1,0) <= 2 sum_internal_v max(k_v-1,0).
For a DAG with shared children the one-parent step fails; no DAG generalization is claimed. With arbitrary indegrees on the dependency orientation, use number of children per parent on the RHS, but still require each child to have at most one parent.

## Needed Lean bridges, in dependency order (all pending in this unit)
1. Define finite round indices and prefix compute counts in ActionRuns; prove recurrence and monotonicity with explicit OLD phase.
2. Prove OLD P implies positive epoch ID and existence of its unique start with no intervening pebble-removing action. At compute/ghost in one round preserve a non-boundary epoch.
3. Assign each C/U to a valid parent epoch in [1,k_v], and show strictly ordered reference times for distinct parent epochs. Initial-P epoch has no C start in the trace.
4. Define finite sets S using deduplicated pairs, not event multisets. Prove all-members ordering from (1)-(3).
5. Formalize the finite-union telescoping lemma, explicitly handling q=0 and omitted empty S. Then double-count pair incidences.
6. Instantiate heap parent uniqueness and two children; sum the per-edge inequalities.
7. Connect k_v to actual work via existing WorkBridge, with initial-P correction retained. k_v is C+initialP, NOT C in cut traces. A cut-space term is necessary when summing initial contributions.
8. Only later connect this combinatorial reuse bound to a geometric area inequality. Bounded number of merges does not by itself produce a forest with long occupied intervals, nor any lower bound on interval lengths.

## Scope and nonclaims
This hand argument identifies a plausible complete combinatorial proof conditional on chronological epoch extraction. It does not certify Lean compilation, axioms, absence of sorry in a new theorem, or exact equivalence with PaperRuns. Existing 200 random tests are not rerun and do not prove it. This is not a C=4 depth lower bound: an O(n) merge budget can still destroy the naive good forest, and geometry/second scale remains missing. S-grade novelty remains unestablished. No <host> transfer or existing showa file changes.
