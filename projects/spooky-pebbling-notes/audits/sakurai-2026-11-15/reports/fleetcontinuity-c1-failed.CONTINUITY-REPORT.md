# FLEETCONTINUITY C1: FAILED, not a proved theorem
Same sf2 reservation, final fourth attempt, completed within22:12:47+600seconds. START22:22:38 STOP22:22:43 UTC, rc1, runtime5.338s CPU5.238s. cgroupMemoryMax1GiB/swap0/CPUQuota100%/Tasks16/Runtime20s/LimitCPU18s unchanged. MemoryPeak256KiB remains unreliable and not claimed as actual RSS.

Attempted scalar statement: a trace ending pebble with zero computes begins pebble and every event is idle. Proposed consequence: two equal prefix epoch IDs at an occupied endpoint imply no ghost/uncompute within the intervening ActionRuns; conversely a removal followed by occupancy requires a strictly larger ID.

Compilation failed in no_compute_occupied, simp_all/omega left a non-arithmetic goal. Lean failure diagnostics inserted sorryAx into all three attempted new theorem dependencies. These are NOT verified lemmas; no new accepted theorem is claimed. Failure is a proof-script gap, not evidence of a mathematical counterexample. Successful earlier EpochPrefix theorems retain their previously checked standard-only dependencies.

P2 produced no olean, so its fixed source was concatenated with the new source in ContinuityCombined.lean; fixed underlying3dependency oleans were reused, not rebuilt. The first source no_compute proof used coarse cases+automation. Next attempt should inspect each Step constructor explicitly and specialize the induction hypothesis with tail zero-count and endpoint, rather than treating the remaining logical goal as arithmetic. No correction was compiled in this unit. Unique-start extraction and chronological reference-set theorem remain missing.

Reservation's four attempts F1/P1/P2/C1 exhausted and wall window completed; no automatic retry, job remains stopped. Source, failed output, actual STOP, return code, and SHA manifest recovered sf2-><host>->m3 and verified. Existing successful artifacts untouched. No C4 result asserted.
