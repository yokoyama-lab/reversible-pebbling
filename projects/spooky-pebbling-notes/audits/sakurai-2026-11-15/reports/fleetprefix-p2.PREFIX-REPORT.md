# FLEETPREFIX P2
Continuation in F1 sf2 reservation; same memory1GiB/swap0/1CPU/Tasks16/Runtime20s/LimitCPU18s/Nice10. No prior successful compilation rerun: P1 built fixed three original dependencies once, failed only new theorem implicit type inference; P2 reused generated Linux oleans and explicitly typed n/pred/q/xs/r/a. Failed source and logs retained.
P1 START22:17:09 STOP22:17:13 UTC rc1 CPU3.491s/runtime3.493s. P2 START22:18:27 STOP22:18:28 UTC rc0 CPU.523s/runtime.519s. Memory display256KiB remains unreliable, exact RSS not claimed. All requested cgroup limits match previously enforcement-tested mechanism.
Lean4.35.0 source-only three dependencies ConcreteRound/CutBound/TraceBridge. New theorem types:
* occupied_has_epoch: scalar Trace s es t ending pebble implies 1<=initiallyOccupied(s)+count(compute,es).
* before_append: initial occupied contribution plus actual prefix compute counts is additive under suffix extension.
* before_mono: prefix epoch counter nondecreasing.
* old_pebble_positive: actual ActionRuns ending with vertex pebbled yields positive prefix epoch ID.
* reference_positive: Legal parent C/U depending on child u gives positive epoch ID at OLD prefix, via actual Legal dependency premise.
All five #print axioms propext/Quot.sound only (before_append propext only); no sorry/native_decide. Source and original dependencies fixed in PREFIX-MANIFEST.sha256. This does connect OLD-reference positivity and counter monotonicity to original ActionRuns, unlike abstract F1 alone.
Still missing: unique live epoch start/no-removal interval, assignment of C/U to parent epochs, ordered times between distinct parent epochs, finite reference-set extraction and actual union-cardinality telescoping. Positive counter does not itself certify the last occupied interval; initial ghosts have zero initialOccupied and are distinguished. C4 area/depth lower bound remains unproved. No S novelty asserted.
Both attempts STOP confirmed and all files copied sf2-><host> new directory->m3, SHA readback matched. No ongoing research process and no job restart. This package preserves F1 unchanged and adds P1/P2 records.
