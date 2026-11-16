# REFSELECT K3: zero-recompute selection
Owner /root/spooky_dp; A2 stopped before this unit. No duplicate job. Finite limits: 600 wall unit, 30 CPU/60 wall per compile, -j1 -M1024. Mikawa no transfer.

CORRECTION TO A2 SCOPE: RefArea.reference_area was declared after counterexample constant RefArea.b and its implicit b resolved to that fixed action, not an arbitrary Action. Its proof was sound but its area corollary was narrower than intended/reported. Earlier RefArea.reference_suffix_live and live_le_volume were genuinely general. A2 originals unchanged. K3 RefSelect.kept_gap_live combines those general lemmas and #print explicitly confirms {b : Action} universally quantified. It establishes live=length and length<=volume for any subsequent legal reference with no compute in the gap.

Selection: good filters chunks with compute count 0, bad filters positive compute count; split_lengths gives an exact partition of chunk occurrences. removed_count bounds the number of removed INTERIOR reference chunks by the original per-child compute count. many_kept gives total interior chunk count <= kept chunk count + original compute count. Terminal chunks remain excluded.

kept_has_no_loss: for an actual extracted interior reference chunk, zero compute implies zero ghost and zero uncompute by actual endpoint balance. Thus ghost losses occur only in removed chunks, not in the selected continuously occupied ones. No duration bound is asserted for removed chunks. One ghost can precede arbitrarily many idle rounds, so bounding counts does not bound lost duration. This is the central obstruction to obtaining an area lower bound from these lemmas alone.

Actual-model connection: selection predicates and removed_count use the extracted reference chunk list of actual actions; kept_has_no_loss uses actual ActionRuns/extracted_gap. kept_gap_live handles the corresponding segment at its actual starting configuration; automatic aggregation of all selected segment configurations and non-overlapping volume contributions remains unfinished. C4 lower bound and second-scale structure remain unproved.

K3 accepted: 2026-11-15T20:17:07.436680Z–20:17:07.722587Z, rc0 CPU .281226s peak672989184 bytes. Lean4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc. kept_gap_live/removed_count axioms propext,Quot.sound. split_lengths/many_kept/kept_has_no_loss also Classical.choice. No sorry/native_decide in accepted proofs. Harmless unused h warning in a purely combinatorial count inequality. K1/K2 failures retained, diagnostic sorryAx not accepted.

No novelty/S claim, no change to earlier manuscript/theorems or prior Drive files.
