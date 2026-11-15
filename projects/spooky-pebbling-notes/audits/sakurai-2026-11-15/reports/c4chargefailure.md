# C4CHARGEFAILURE F2: exact logical failure of the C3 good-forest argument
Owner /root/spooky_dp, stopped B1 continuation. No duplicate job, no repeated simulation. Limits 600wall unit, 30CPU/60wall/-j1/-M1024 each Lean call; fixed saved witness for count audit. No <host> transfer.

## What remains valid at C4
Actual last-root cut, pre-compute propagation, mandatory cleanup, account validity, charge inequality and interval nesting for GOOD vertices remain true. Nothing in their proofs breaks. The critical implication is instead the mass estimate:
  3n+B <= W+2p+1.
At W<=3n this gives B<=2p+1, leaving almost all vertices good at p=O(n/H). At W<=4n it only gives B<=n+2p+1, allowing all vertices to be removed. No large good forest, and therefore no entropy/depth mass, follows. Treating this as a failure of interval nesting would misidentify the obstruction.

## General Lean-certified countermodel to the ACCOUNT assumptions
For n=k+1 accounts, one root account (preC,postC,postU,cutP,root)=(1,0,0,1,1) and k accounts (1,2,1,0,0) satisfy all Valid conditions. Totals:
 length=n, work=4k+1=4n-3, cutP=1, roots=1, removed=n.
ChargeFailure.no_good_mass proves these jointly for every k. Thus even with cut-space1 the account assumptions plus W<=4n cannot imply any positive retained-good mass. This is a logical account countermodel, NOT an actual tree execution; it cannot refute a geometric theorem using additional causality/branching hypotheses. It strengthens the earlier single-vertex four-cost example to the complete root-count/aggregate assumptions.

## Actual witness corroboration (not the abstract model)
Read the previously verified H16/cuts[8,4] witness, input SHA56869a44457b242934ed85eae37c0a6c3af1a3138a32a4392be521ce1fa8201e. No generator or legality run repeated. At final root compute index2055: p511, exceptional61440, retained good3584, removed61951, n65535. All61440 exceptions have exactly tuple(1,2,1,0,0). Thus roughly94% of the actual vertices have the very four-cost pattern excluded by the C3 forest. Histogram saved. This does not prove the all-removed scalar model is realizable.

## Promising replacement, NOT PROVED
Do not delete all vertices with a second post-cut compute. Refine each such vertex into its two compute-to-loss occupancy epochs and retain their dependency references. A viable structural lemma must show that the resulting event graph either supplies a low-overlap occupied-cell charge across a second branching scale or forces a third post-cut compute/additional uncompute beyond the4n budget. It must control reuse: one epoch can serve multiple parent references, so the selected object need not be a forest; claiming tree entropy without proving bounded merges would be invalid. This bounded-merge/extra-work alternative is the missing geometric hypothesis not present in the scalar account countermodel. No formal lower bound or proof of this replacement is claimed.

## Verification
F2 2026-11-15T20:44:11.151964Z–20:44:11.416220Z rc0 CPU.258193s peak669908992 bytes. Lean4.35.0 eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Axioms propext,Classical.choice,Quot.sound; no native/sorry. F1 failed Std syntax/decidability retained, diagnostic sorryAx not accepted.
ACCOUNT finite Python read/aggregate20:44:57.808443Z–20:44:57.952014Z rc0 CPU.140168s peak65748992B. This histogram is not Lean proof. C4-Area conjecture remains unproved; no S-grade claim.
