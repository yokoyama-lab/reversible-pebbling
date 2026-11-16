# General PaperRuns lower-bound certificate bridge

Owner /root/spooky_dp; task SPOOKY-POTENTIAL-20261115. Independent scope confirmed by /root/pebble_review; that agent's cumulative accounting is for a different LocalCertificate model. No search jobs or successful exact7 edge shards were rerun. Existing ConcreteRound source was copied and compiled as a standalone import dependency.

## Proven (Lean 4.35.0)
Potential.lean proves, for arbitrary graph size n, dependency relation pred, peak cap S, natural objective weights a,b and a configuration potential phi:
- actions_to_local: checking phi(q) <= a*roundWork + b + phi(afterRound) for every well-sized Legal action with roundSpace<=S yields the step certificate.
- all_runs_bound: every PaperRuns execution with peak<=S satisfies phi(start) <= a*totalWork + b*depth + phi(end).
- budget_bound: if phi(end)=0 and work<=W, depth<=D, then phi(start)<=a*W+b*D.
Proofs use induction over actual PaperRuns, not a generated successor table. No native_decide/sorry/admit. Dependencies propext, Quot.sound (actions_to_local only propext). This is the standard telescoping/dual-potential method, NOT a novel lower bound.
P1 failed due an implicit dimension annotation; P2 fixed q:Config n and succeeded. All failed/successful receipts retained. CPU cap30s, wall60s, -j1 -M1024, total reservation600 wall. Final P2 START2026-11-15T14:59:45.830098Z STOP14:59:46.076639Z rc0 CPU0.239609sec peak660209664bytes.

## Specific next research target, not a result
Define D_lin(h,C,s) as the minimum depth with W<=C*n and peak<=s for fixed C.
Lee et al. https://arxiv.org/html/2610.09434v1#S5.SS3 eq38 has W>=c*n*L-s*D/L, L=lambda(n). Therefore at s=Theta(n/h), fixed linear work implies D=Omega(h*L^2) as L grows. This is an algebraic consequence of PRIOR work, not our improvement. Their theorem5.2 already establishes the distinct optimal-depth endpoint with work Theta(n*lambda(h)).
Promising question: determine D_lin, then extend to W/n varying between constants and lambda(h). A candidate elementary upper construction partitions into k~s/constant boundary-root subtrees, m~n/s vertices each; computes each cleanly with all m vertices available, retains roots, computes/uncomputes top skeleton, and inverses the fringe routines in batches. At s~n/h this suggests O(h*log h) depth and O(n) work. This is only a construction sketch: precise boundary memory, active-set disjointness, round-space union, clean-root reversal, rounding and work constants remain to be checked. No theorem or novelty claim is made for this bound.
A useful new lower bound would improve the existing h*L^2 obstruction or match a construction in this restricted linear-work problem. To use the Lean bridge one must supply an explicit phi (preferably recursively composed on subtrees) and PROVE its Legal-step inequality. No such graph-specific potential has been supplied in this unit. Supported linear inequalities alone may miss nonconvex Pareto points; a full frontier could need richer/vector certificates.

## Prior literature screening
Lee et al. above is the principal joint bound baseline. Komarath-Sarma-Sawlani, Reversible Pebble Game on Trees (2015), https://www.cse.iitm.ac.in/~jayalal/research/papers/KSS15a.pdf, already gives O(n) sequential work at O(n^epsilon) space for bounded-degree trees. Thus linear work at sublinear space is not new; parallel depth under fixed linear-work budget would need separate comparison. This pass does NOT establish that this question is globally open. No S novelty assertion.
