# C4AREATARGET Q1: one quantified global conjecture, NOT a theorem
Owner /root/spooky_dp, stopped P3 continuation; no duplicate worker. Reads saved H12 witness only, no rerun of schedule construction/legality audit. Fixed <=8464 rounds/4095 vertices, CPU30/wall60/RSS stop1GiB (not OS hard memory cap).

## Concrete candidate C4-Area (unproved)
For every integer H>=1, let n=2^H-1 and use HeapPath.pred with the established two-phase union-space convention. For every finite actual clean run from the entirely empty configuration to only root pebbled/no ghosts, with work W<=4n and peak<=s, where 1<=s<=n, define
 A = sum over ALL rounds t and ALL vertices v of 1[v in P_before(t) union P_afterFirst(t)].
For every integer ell>=0 satisfying 8*s*2^(2^ell)<=n, conjecture
             8*A >= n*(ell+1).
The constants8 are explicit trial constants, NOT derived. No assertion of validity. This weights each occupied vertex-round cell once and includes off-path holds, initial computation, ghost handling and cleanup, rather than just last-compute evaluation suffixes.

## Why it would reach C4 if proved
A<=s*d is already proved in the actual model. Choose fixed budget s_H=ceil(6*2^H/H). For H>=1, H*s_H<=7*2^H and n>=2^(H-1). Thus H>=112*2^(2^ell) suffices for the conjecture's scale condition; combining would give 112*d>=H*(ell+1). With maximal such ell this is Omega(H loglog H). These are mathematical consequences CONDITIONAL on the unproved conjecture, not Lean-certified new conclusions. s_H<=n holds only H>=7; the displayed sufficient thresholds imply that automatically.

Consistency: the previously audited Lee-derived j=1 upper has W<=4n-1 and depth O(H loglog H) at s=Theta(n/H), so the proposed order does not contradict it. Exact same s_H constants for that fast upper remain unconnected. The proved W<=3n sandwich gives a stronger lower in its stricter work domain, so there is no contradiction. Lee eq38 and the small-excess lower at e=n do not establish this candidate. Worldwide novelty/validity remains unverified.

## Bounded finite check and its lack of positive evidence
Saved H12 witness SHA d33aa9426d7e2346c6f00702aa97c9e5df4439cf33d518cf7852b184021317b7.
Measured A=178955, W15101, actual peak511, fixed budget2048.
Area by vertex depth: [7433,6,20,56,144,352,832,1920,135424,3072,13312,16384].
Before/including first root compute area141825; later cleanup area37130. Exact sums agree. The zero-suffix rightmost path misses the large off-path depth8 contribution.
For ell0..4 the scale premise is FALSE even at actual peak511 (already 8*511*2>4095); also false at fixed budget2048. Therefore these checks provide NO substantive support for the conjecture. Moreover for ell<=7 its RHS is already below the elementary A>=n computation-volume baseline. Small explicit trees cannot validate the intended asymptotic strengthening, and absence of a counterexample here must not be sold as evidence.

## Concrete structural task still needed
Construct scale-indexed charges to actual occupied vertex-round cells, using both sibling branches and mandatory cleanup references. A possible proof certificate would assign at least n charge units at each of ell+1 scales with total cell multiplicity<=8, while charging broken obligations against the explicit excess work over3n. None of the existing reference partition, ghost budget, or last-live lemmas gives these two properties. In particular count budgets alone do not bound missing duration. This is the missing global lemma, not a request to keep proving local tautologies. If it fails, save an actual clean schedule violating the numeric inequality or an obstruction to the charge certificate, and distinguish the two.

No new Lean theorem: validity has NOT been established. Q1 analysis rc0 2026-11-15T20:36:42.515771Z–20:36:42.656254Z CPU.137934s peak18874368 bytes. Python3.9.6. No <host> transfer. Existing files unchanged; new showa save only.
