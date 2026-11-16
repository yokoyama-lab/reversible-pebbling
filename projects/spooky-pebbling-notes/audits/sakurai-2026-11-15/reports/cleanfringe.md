# Clean-fringe construction: precise mathematical accounting and finite checks

ID SPOOKY-CLEANFRINGE-20261115, sole owner /root/spooky_dp. This is an elementary candidate baseline for the fixed-linear-work problem, NOT an S-grade novelty claim. No claim that this schedule is Pareto-optimal. All new jobs STOP.

## Construction and exact costs (mathematical proof)
Take complete tree height H=t+r with t>=1,r>=1, k=2^t, m=2^r-1, n=k*m+k-1. Cut at depth t into k disjoint bottom/fringe trees, each m vertices, beneath a top skeleton with k-1 internal vertices. Choose integer1<=b<=k. Partition the fringe roots into consecutive batches, with maximum size b and last batch possibly smaller.
A clean-fringe routine computes every level bottom-up (r rounds), then uncomputes all levels except its root top-down (r-1 rounds). Its costs are work2m-1, depth2r-1, peak m. Every nonroot input required for uncomputation is still present. Each round contains vertices from one level; their active sets (vertex and children) are pairwise disjoint. Across different fringe trees active sets are disjoint too. A batch executes the identical level routine on each of its trees in parallel.
First run clean routines on all batches and retain the k roots. Compute the k-1 internal top nodes levelwise bottom-up (t rounds), then uncompute every top internal node except global root levelwise top-down (t-1 rounds). The boundary roots stay untouched and serve as available inputs. Finally invert each batch's clean routine (reverse round order and exchange pebble/unpebble). All inversions are legal: same-level targets are not one another's dependencies, and all such dependencies are unchanged by that round. The global root and other boundary roots remain idle. No ghost operation occurs anywhere. Result is exactly the global root.
Costs of this actual schedule:
W=2*k*(2*m-1)+(2*k-3)=4*k*m-3 < 4*n.
D=2*ceil(k/b)*(2*r-1)+(2*t-1).
S=max(2*k-1,k+1+b*(m-1)).
The top skeleton peaks at all its2k-1 nodes present. In preparation the completed roots add at most k-b' to b'*m vertices of a batch; in cleanup the global output adds1, yielding k+1+b'*(m-1). The first cleanup batch has exactly b trees and all k roots initially present, so that bound is attained. Space is the union before/after-first-phase, not just endpoints: every round here is all additions or all removals, hence union equals the larger endpoint. This establishes the exact peak rather than an illicit endpoint approximation.

## Explicit regime bound, mathematical argument (not yet general Lean)
Suppose 8<=s<=n and s^2>=32*(n+1). Let k be the largest power of2 at most s/4; thus s/8<k<=s/4 and k>=2. Then m+1=(n+1)/k<8*(n+1)/s<=s/4, so m<s/4, with m>=1. Choose b=min(k,floor((s-k-1)/(m-1))) for m>1; if m=1 choose b=k. These choices satisfy both peak constraints.
For m>1, s-k-1>=s/2 and x=(s-k-1)/(m-1)>2. Thus floor(x)>=x/2>=s/(4*m). If this is not capped at k, ceil(k/b)<=1+4*k*m/s<=1+4*n/s. If capped, the number of batches is1 and the same bound holds. Since r=log2(m+1)<3+log2((n+1)/s), the exact depth formula gives D<=2H+4*(1+4n/s)*r, hence D=O(H+(n/s)*(1+log((n+1)/s))). Constants independent of H,s in this range. At s=Theta(n/H) for sufficiently large H, this gives W<4n and D=O(H log H).
This establishes a concrete elementary mathematical upper construction, but its arbitrary-size generator-to-PaperRuns proof is unfinished. It does not improve the known optimal-depth construction; it sacrifices depth to bound work by4n.

## What Lean actually proves
Lean4.35.0, -j1 -M1024.
Arithmetic.lean: work_exact, work_linear, peak_fits for arbitrary natural parameters subject to k>=2,m>=1. These are algebraic formulas, not a formal proof that the generator realizes those formulas on every tree.
Certificates.lean: generic check_sound converts checks using original SpookyRound.Legal into PaperRuns. Three15-vertex actual schedules (H4,t2,b1/2/4) have (work,depth,peak)=(45,27,7),(45,15,9),(45,9,13). Each has actual PaperRuns, exact costs and root-only/no-ghost goal. Pure decide/kernel checking, no native_decide/sorry/admit. Dependencies propext,Quot.sound.
31-vertex certificate attempt exceeded Lean's1GiB memory limit; this is NOT a counterexample. AttemptWith31.lean and failed logs retained, theorem run3 is NOT a valid completed result. Completed Certificates.lean omits that failed case and is compiled successfully to .olean. Successful15 witnesses were consolidated in that final module after the combined-file failure; old exact7 shards were never rerun.

## Finite Python audit (not proof)
494 cases: every H2..8, t1..H-1 and b1..2^t. At most255vertices. Independently checks all action preconditions, pairwise-disjoint active sets, phase union peak, clean goal, exact W,D,S formula. All pass. No state-space exhaustive search and no optimality claim. CPU0.129248s, measured peak13139968bytes; Python memory not hard-capped, bounded instances.

## Execution receipts
AUDIT START15:04:34.098946Z STOP15:04:34.230621Z rc0 CPU0.129248.
ALG1 failed algebra normalization, ALG2 START15:05:57.590073Z STOP15:05:57.841634Z rc0 CPU0.2485.
CERT1 START15:06:45.984078Z STOP15:06:50.659310Z rc1 CPU4.664591;31vertex kernel memory limit, not false theorem.
CERT15 START15:07:23.765333Z STOP15:07:26.164402Z rc0 CPU2.389698, peak884736000bytes.
Each subprocess CPU30s/wall60s, whole reservation600wall. No limit expansion. Failed algebra log's sorryAx is not part of successful ALG2 proofs.

## Prior work and novelty limit
Lee et al. https://arxiv.org/html/2610.09434v1 §§3.2–3.4 already uses retained boundaries, top-block compute/uncompute and batched independent subtrees. Our difference is a fully clean reversible fringe routine instead of ghost-producing preparation followed by recursive ghost cleanup. Therefore the decomposition/batching idea is NOT new. Their §5.3 eq38 gives, at s=Theta(n/H), W=O(n) implies D=Omega(H*lambda(n)^2) as lambda grows. This is a prior-bound corollary, not our lower bound. Their optimal-depth endpoint has higher work. We have not established that O(H log H) linear-work schedules are absent from other literature.
Komarath-Sarma-Sawlani2015 https://www.cse.iitm.ac.in/~jayalal/research/papers/KSS15a.pdf already establishes linear sequential work with O(n^epsilon) space in bounded-degree trees; its sequential step convention is different from this disjoint-active-set parallel depth. Hence neither linear work nor clean reversible partitioning is inherently new.
The targeted gap remains between prior Omega(H lambda(n)^2) and this O(H log H) baseline at W<4n, s~n/H. Improving or matching this gap, with a graph-specific lower-bound potential or a better phased construction, would be substantive. The current unit alone is not sufficient to call a new research result S.
