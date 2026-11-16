# LASTLIVE T2: actual last-compute live suffix
Owner /root/spooky_dp, stopped L4 continuation, no duplicate job. 600wall unit; 30CPU/60wall/-M1024/-j1 per compile; no <host> transmission.

last_compute_suffix: for an actual run on xs ++ b :: ys, where b references u and xs contains a compute of u, extract xs=pre++c::suffix. c is a compute of u and suffix contains no compute of u. The theorem includes a real prefix ActionRuns reaching before, and actual suffix ActionRuns starting afterRound before c. It proves c does not ghost u in its second phase; after c u is pebbled; its occupied old-boundary time along suffix equals suffix.length; this length is <= actual union-volume of that suffix. All next-reference actions b are universally quantified (type readback saved).

prior_compute_required removes the compute-exists condition when initial kind q u is nonpebble: a subsequent legal reference forces a prior compute in xs. If initial u is already pebbled and xs has no compute, the earlier no_compute_live/reference_suffix_live supplies continuity for the whole prefix. Last occurrence selection is existential Classical.choice, not an executable selector; it is tied to the actual chronological decomposition.

Boundary conventions: suffix excludes the selected compute round and the next reference round. It may be empty (compute immediately before reference), so no positive duration is implied. The selected compute round itself cannot ghost u; ghosting elsewhere is not globally forbidden. Length lower bounds, bounded-overlap selection for many references, branching geometry, second-scale area and C4 lower bound remain unproved. Arbitrarily long discarded prefixes from L4 are not charged as live area.

T2 accepted 2026-11-15T20:24:48.455411Z–20:24:48.717964Z rc0 CPU .25218s peak666763264 bytes. Lean4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. last_compute_suffix axioms propext,Classical.choice,Quot.sound; prior_compute_required propext,Quot.sound. No sorry/native_decide. T1 success retained; T2 strengthens explicit prefix linkage. No failure or running job.

No S-level novelty claimed. Existing artifacts unchanged, new showa save only.
