# REFSUM S4 — actual reference interval aggregation
Owner: /root/spooky_dp. Prior R6 stopped rc0; continuation only, no duplicate research worker.

For an actual ActionRuns and a fixed child u, parts(references pred u) actions decomposes the original action list into an unmarked prefix and chronological marked chunks. interior excludes exactly the final chunk (and is empty for zero or one chunks).

Proved RefSum.aggregate: sum interior compute = sum interior ghost + sum interior uncompute.
Proved RefSum.no_duplicate_charge: sum interior ghost + sum interior uncompute <= total compute events of u in the original action list.
The proof uses R6 actual-gap endpoint pebbling, exact list reconstruction, flatten/count distributivity, and omission of nonnegative prefix and terminal costs. It does not charge arbitrary overlapping pairs of references. Each action position in the interior flatten occurs once. Equal-valued actions/chunks at distinct positions are allowed and correctly counted by occurrence.

Boundary treatment: no references or a single reference yields an empty interior sum. The last chunk has no later reference endpoint and is intentionally excluded. Its compute cost contributes only to the ambient upper budget, never an assumed pebble-to-pebble equality.

Accepted S4 rc0: 2026-11-15T20:05:32.236152Z–20:05:32.510125Z, CPU .26803s, peak 673628160 bytes. Lean4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, -j1 -M1024, 30 CPU /60 wall seconds. Axioms propext, Quot.sound; no native_decide or sorry in accepted results. S1–S3 failed type/rewrite attempts preserved; their sorryAx diagnostics are not accepted proofs.

Limitations: this is a per-child exact action/scalar count statement, not yet a sum over all children or a round-area lower bound. Same action may reference two children, but each child's scalar compute budget is distinct; a global summed theorem is not asserted here. Original-round occupancy, second-scale forest extraction, and C=4 lower bound remain unproved. This is a verification building block, not an S-grade novelty claim. Lee repeated constructions and exact space constants still constrain next claims.

No <host> transmission attempted; prior rejected operation remains awaiting approval. Existing showa files unchanged.

Source SHA256: 4a73963205cb8eb131f1a818134cf4d0d560dc9c40bd4790f86851ddc0777b5c
