# Last-root cut and scalar exception charging
R4 Lean 4.35.0 verified, no sorry/admit/native_decide. Axioms propext, Classical.choice, Quot.sound. R1 type-hole and R3 tactic failure are retained, not successful proofs.

last_root_cut extracts the last root compute occurrence directly from PaperRuns, given initially nonpebbled/finally pebbled root. root_child_cut extracts the configuration after this occurrence and actual suffix traces: each immediate dependency child (distinct from root, finally empty) is nonempty at the cut, has an uncompute afterwards, and if not pebbled at cut must compute afterwards.
actual_suffix_charge turns an arbitrary actual ActionRuns suffix and a mandatory uncompute witness into c>=1,u>=1 and a unit charge for the exceptional c,u != (1,1) case. bad_count_bound sums these charges for any list of such accounts.

Outstanding: descend this property through ALL descendants (not only immediate children), prove their earlier compute witnesses, relate the sum of counts to the actual whole-run work and cut pebbles, form the full good forest, extract unique timestamps and prove occupancy-area connection. Thus B<=e+2s+1 and the proposed C3 logarithmic depth bound are NOT yet end-to-end Lean theorems. No novelty or S-grade claim.

Budget wall600 seconds CPU30/call memory1GiB; final compile R4 CPU0.269596s, START15:45:26.101129Z STOP15:45:26.375852Z on 2026-11-15. All subprocesses stopped. No previous successful unit rerun. Same existing owner spooky_dp; lower_audit was independent prose audit, no overlapping implementation reservation.
