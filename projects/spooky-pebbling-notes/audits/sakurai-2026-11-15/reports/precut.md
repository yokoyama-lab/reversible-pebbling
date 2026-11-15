# Precut computation and exact splits, C3
Lean4.35.0 no sorry/admit/native_decide. precut_all propext,Quot.sound; counts_split propext; selected_exceptions additionally Classical.choice.

precut_all: on actual heap ActionRuns pre++a::post, if every vertex initially nonpebbled and a computes root, EVERY vertex has a compute in pre++[a]. Proof propagates prerequisites backwards, then strong induction on heap indices. No path/reachability assumption remains.
counts_split: exact scalar event counts for every event on arbitrary action concatenation. selected_exceptions: actual suffix nonpebbled vertices with cleanup witnesses, mapped to real count pairs, obey summed exceptional indicator <= summed (compute+uncompute-2). List may have duplicates: use finRange.filter for genuine distinct cardinality; that final instantiation and bounding against global W remain TODO.
Remaining: package all cut accounts, root omission and cut-pebble cardinality; derive B<=e+2s+1 using total work and space; good forest timestamps/area. C3 lower bound whole theorem remains incomplete. No newS/novelty claim.
C1 failed implicit dimension inference saved; C2,C3 successful. C3 START2026-11-15T16:00:46.567786Z STOP16:00:46.860592Z CPU0.288016s peak667123712B rc0. Budget600wall CPU30/call wall60 mem1GiB. All STOP, same owner no overlapping assigned implementation, old successful units not recompiled.
