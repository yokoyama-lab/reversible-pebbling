# C4SAMPLES B1: true-premise finite checks, still not evidence for the asymptotic strengthening
Owner /root/spooky_dp, stopped Q1 continuation, no duplicate job. Old H2..8 and SPACEPATH cases not rerun. New cases H10 cuts[5,2], H12[6,3], H16[8,4]. All actual actions saved in three witnesses.

The candidate: clean complete binary tree n=2^H-1, W<=4n, peak<=s, 8*s*2^(2^ell)<=n implies 8*A>=n*(ell+1). Here s is chosen as the measured peak, not the larger designated s_H.

H10 n1023: W3805, S63, A15256, D1930. ell0 premise true (1008<=1023); 8A122048>=1023.
H12 n4095: W15805, S127, A61705, D5452. ell0,1 premise true; at ell1 4064<=4095 and 8A493640>=8190.
H16 n65535: W257789, S511, A1155339, D53520. ell0,1,2 premise true; at ell2 65408<=65535 and 8A9242712>=196605.
All W<=4n. Independent execution checker verifies old dependencies, active-neighborhood disjointness, ghost-phase legality, P/G disjointness, full clean endpoint, work and union-area. This is Python finite verification, not Lean proof of the witness.

Important limitations: these are six TRUE-premise cases (not the earlier vacuous tests), but every ell<=2 conclusion is weaker than the elementary A>=n baseline. Thus they test implementation/model arithmetic and establish actual feasible samples, not the novel strengthening. The designated larger s_H also contains these schedules, but its scale premise does NOT thereby become true. No claim of validating the fixed-budget asymptotic C4 theorem. At ell>=8 the candidate first exceeds A>=n, requiring n/s>=8*2^256; explicit full-tree enumeration at that scale is outside the finite budget. Additional elementary lower bounds such as A>=work make informative tests harder still.

These slow schedules are not minimizers of area or depth. Passing them does not calibrate coefficient8 tightly. No counterexample found in these cases; validity remains OPEN. Next evidence must be an analytic structural lemma, symbolic recurrence with proved implementation connection, or a rigorous upper-construction inequality that could refute the candidate. Do not increase brute-force tree size expecting useful asymptotic evidence.

B1 actual 2026-11-15T20:40:20.106197Z–20:40:30.769207Z rc0 CPU10.652329s peak121651200 bytes. Python3.9.6. Finite inputs capped65535 vertices/two cuts, CPU30/wall60 and per-round RSS stop1GiB. No OS hard memory cap; unchanged from prior Darwin limitation. No new Lean theorem, no S claim, no <host> transfer. Existing artifacts unchanged.
