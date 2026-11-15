# FLEETEPOCH F1
New user fleet-computation instruction; sole owner /root/spooky_dp. Fleet inventory confirmed sf2 low load and no Condor queue entries; save_overnight used a separate directory. sf2 chosen, busy <host> and reboot-window s3 not used for research execution. No existing process stopped/restarted; no global settings changed.

Read-only preparation and exclusive new directory preceded execution. Preflight transient unit readback: memory.max134217728, memory.swap.max0, cpu.max100000 100000, pids.max16, RLIMIT_CPU6/6. Separate tiny32MiB memory probe allocated48MiB and was OOM-killed at33554432 bytes, CPU34001000ns; separate1sec CPU loop killed at996744000ns. These were bounded diagnostic processes, not the old failed research job.

Research unit spooky-fleetepoch-f1-20261115 used MemoryMax1G, MemorySwapMax0, CPUQuota100%, TasksMax16, RuntimeMaxSec20, LimitCPU18, Nice10; therefore process-tree memory/PID/quota restrictions, not mere per-child RSS polling. START22:13:31Z STOP22:13:32Z, rc0, runtime484ms/CPU483ms as reported by systemd. Kernel memory controller enforcement was tested beforehand. Exact research peak RSS is NOT established: systemd display256KiB is suspiciously low and later property is not set. Do not use this as a trustworthy Lean peak memory measurement. No hard-limit exceedance reported.

Lean4.35.0 x86_64 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Standalone Std-only source SHA818efde82dbd15e0615fa777808ac14e08c1fc7cc6e0d5b49eac1ce5ddc4682b. Four theorems accepted by Lean: shared_unique, overlap_card_le_one, sum_reuse_le_count, noninitial_reuse_le. Printed axioms standard propext/Quot.sound plus Classical.choice for cardinality lemma; no sorry/native_decide.

Ordered old fresh means every old child-epoch ID <= every fresh ID. Shared_unique proves any two shared IDs equal. A duplicate-free list contained in both has length<=1. Lists of per-noninitial-epoch costs each<=1 sum to at most q-1 when length+1<=q. Empty epoch families are not asserted to satisfy length+1<=0; they require a separate zero branch.

Remaining: extract epochs/reference sets from actual ActionRuns, prove chronological ordering/initial-P correction, define actual set-union increments and their double-counting identity, then instantiate tree parent uniqueness. The arithmetic costs are still abstract assumptions, not actual event counts. No C4 depth/area theorem or S-grade novelty claimed. This is a verified proof component, not a solution of the research target.

Files preserved sf2:<home>/spooky-fleetepoch-20261115 and <host>:<local>/paper-audits/spooky-fleetepoch-20261115 with manifest, copied back to m3. Existing files untouched. F1 finished, no running research job; no repeated compilation.
