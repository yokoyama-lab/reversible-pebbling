# PaperRuns exception bound without cut assumptions, S2
Lean4.35.0, no sorry/admit/native_decide. paper_exception_bound depends only propext,Classical.choice,Quot.sound.

Theorem: for n>0 and heap dependency pred, any PaperRuns d q r with every initial vertex nonpebbled, root finally pebbled, every other vertex finally empty, actual work<=3n+e and actual space<=s admits a final-root-compute cut with root pebbled, cut pebble count<=s, and removed accounts B<=e+2s+1. Prefix and suffix are actual action witnesses of that SAME run. No precomputed-account, cutroot, cutspace, Path, mandatory compute/cleanup or abstract work-equality assumptions remain.

occurrence bounds the selected original roundSpace by actual whole-run max-space. after_space compares configuration-after-round pebble indicator sum to ORIGINAL union-space |P_before union P_after_firstphase|; ghost second phase only decreases pebbles. root_stays uses final pebble and no later root computes. Previous verified exact work/mandatory events/finite accounts are composed directly.

Initial nonpebbled allows ghosts (empty initial is a special case). Output assumptions do require all nonroot empty including ghosts. n arbitrary positive covers complete tree n=2^H-1; model is original formal PaperRuns, prose equivalence remains separate.

Remaining for proposed asymptotic C3 depth lower bound: identify good forest and its components; extract unique compute/uncompute round times and continuous occupancy; interval nesting; finite depth count and occupancy area<=sD. B theorem is a substantive structural lemma, not the complete asymptotic theorem or confirmed new S result. Independent novelty audit still required.

S1 projection simplification failure saved. S2 START2026-11-15T16:09:57.182903Z STOP16:09:57.458857Z rc0 CPU0.270582s peak670040064B. All STOP. Budget600wall CPU30/call wall60 memory1GiB. Prior E5 STOP observed, same owner/no competing implementation. One harmless unused-simp warning.
