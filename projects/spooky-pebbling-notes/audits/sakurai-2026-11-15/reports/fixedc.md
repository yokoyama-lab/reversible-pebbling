# Fixed work coefficient calibration and a rejected lower-bound conjecture

ID SPOOKY-FIXEDC-20261115, sole owner /root/spooky_dp. New finite unit, previous R4 STOP. CPU30/wall60 per call; total600wall; Lean-j1-M1024. No prior successful instance repeated.

## Exact scale-by-scale accounting
Use Lee's parallel boundary preparation, which computes each vertex once and leaves nonroot ghosts; retain the output in the first top block. Let M=n+1 be twice the leaf count, invariant through equal-depth cuts. After the first cut there are A1 boundary-root trees with no pebbles. After j more forest-contraction stages there are A_(j+1) trees. Before stage i, forest has N_i=M-A_i vertices.
For one tree of x vertices cut into B boundary subtrees, preparation computes x-(B-1) vertices exactly once. Top skeleton then has B-1 computations and B-1 uncomputations (one fewer uncomputation when retaining the global output). Ghosting boundary roots costs zero. Thus a non-output block costs x+B-1; output block x+B-2.
Initial output work is M+A1-3. Each subsequent forest stage costs M+A_(i+1)-2A_i. Terminal full-storage cleanup computes and uncomputes every remaining vertex, costing2(M-A_(j+1)). Consequently:
 W=(j+3)M-3-sum_{i=1}^{j+1} A_i <= (j+3)n-1,
because each A_i>=1. This gives an EXPLICIT work coefficient, unlike a hidden O_j constant. Work counts compute/uncompute only. Ghosting boundaries even when leaves is legal in our model; for the asymptotic Lee Resolve stages, boundaries remain internal until bounded height anyway. Do not conflate this with a sequential convention that charges ghost moves.

## Consequence from PRIOR construction, not new lower bound
Use the schedules/conditions in the preceding report spooky-reverse-20261115: at s=Theta(n/H), sufficiently large H, initial boundary height r0=log2(n/s)+O(1)=O(log H); apply j Resolve stages r->ceil(log2 r)+2, then terminal full-storage cleanup. Timing remains D=O(H*(1+j+r_j)). For every fixed integer j>=0:
 W<=(j+3)n-1,  D=O(H * iterated_log_{j+1}(H)).
This relies on the same feasible local budgets p(r) and absolute per-stage depth bound as Lee Lemmas3.6/3.7. Preparation retains the output only in the first call; reserve one register throughout later calls. For sufficiently large H, the terminal fringe fits the remaining budget. Fixed j keeps r_j large enough for the claimed asymptotic form; stop early at bounded height otherwise. If j grows with H, W's coefficient j+3 grows: it is NOT W<=C*n for fixed C.
In particular j=1 gives W<=4n-1 with depthO(H loglogH). Therefore the tempting conjecture 'W<=4n and s~n/H force D=Omega(H logH)' is false, assuming the cited construction's stated guarantees. This is an asymptotic counterexample assembled from existing techniques, NOT a new S-grade upper theorem. It improves on our clean-fringe baseline only because that baseline was elementary, not because Lee's frontier is surpassed.
A meaningful remaining target is the true D_C for explicit C, potentially a hierarchy of scales indexed by floor(C)-3. Such a lower bound is UNPROVEN. The known eq38 still only yields Omega(H lambda(n)^2) for fixed C. No matching hierarchy or new scale invariant is established in this unit.

## Finite evidence vs Lean proof
Python audit.py constructs legal ghosting-block schedules for every nonempty descending cut chain with H2..8:247 cases, n<=255. It independently checks preconditions, active-set disjointness, no illegal ghosting, P/G disjointness, final root-only and exact work identity. All pass. It schedules fringe preparations sequentially and does NOT certify the fast asymptotic depth, which uses the cited ParallelPebble batching. Examples H4 cuts[2]:W41;cuts[2,1]:W49. These do not prove asymptotics.
FixedWork.lean proves tail_balance/exact_work/fixed_work_coefficient over abstract integer cost recurrences for arbitrary stage lists. No native_decide/sorry/admit; dependencies propext,Quot.sound,Classical.choice. It does NOT yet prove those recurrences for arbitrary-size PaperRuns. Existing reverse_step and finite certificates remain separate verified components.
Lean4.35.0 ALG1 START2026-11-15T15:19:36.330334Z STOP15:19:36.618113Z rc0 CPU0.282042sec peak665403392bytes.
Python AUDIT START2026-11-15T15:18:54.570798Z STOP15:18:54.818670Z rc0 CPU0.245268sec peak14024704bytes. Python memory measured, not hard-limited; finite input bound enforced by generator.

## Source and novelty boundary
https://arxiv.org/html/2610.09434v1 §§3.4,5.3 (ParallelPebble computes every vertex once; Lemma3.6 block; Lemma3.7 Resolve stages). Algebraic coefficient extraction and a mechanically audited small implementation are contributions of this unit, but underlying algorithmic mechanisms are prior art. No claim of globally new fixed-C tradeoff and no claim of improved lower bound. General model-to-construction Lean connection is outstanding.
