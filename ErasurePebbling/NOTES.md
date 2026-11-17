# ErasurePebbling — notes, the open upper bound, and RESUME

Formalisation (Lean 4, mathlib-free, on top of `RevPebbling.PebblingFoundations`
and `RevPebbling.LiftAbove`) of the erasure-budgeted clean reversible pebbling
of a chain from the seminar note RC-02 (`rc02_erasure_pebbling.tex`,
tetsuo-jp/rc-lecture-notes).  Exhaustive tables from the accompanying search
live in `data/erasure/` (see `data/erasure/SUMMARY.md`).

## 1. What is proved (general theorems; sorry 0; axioms propext / Classical.choice / Quot.sound)

| statement | Lean | file |
|---|---|---|
| Model: erasure move, budgeted plays, clean plan `IsPlay n p e s`, `Reachable`, `ReachIs` (= reach), `MstarLe` / `MstarIs` (= M*), `estar n p = ⌈(n−1)/(p−1)⌉−1` | `okE`, `isErase`, `legalE`, `erasures`, `IsPlay`, … | `Basic.lean` |
| Floor: every clean plan has ≥ 2n−1 moves (Knill Obs. 2.2(i)) | `floor_length` | `Saturation.lean` |
| **Theorem A** (saturation), p ≥ 2, n ≥ 1: `M*(n,p,e) = 2n−1 ↔ e ≥ e*(n,p)` | `theoremA`, halves `theoremA_upper` (construction, `Sweep.lean`) and `theoremA_lower` | `Saturation.lean` |
| Corollary: `e < e*(n,p)` ⇒ every plan is strictly longer than 2n−1 | `floor_not_attained` | `Saturation.lean` |
| **Theorem B1**: `reach(p,e) ≥ (e+2)·2^(p−2)` for p ≥ 2 | `theoremB1` | `Reach.lean` |
| Conjecture B2 at e = 0 (Knill): `reach(p,0) = 2^(p−1)` | `reachIs_zero` | `Conjectures.lean` |
| **Conjecture B2 (now a theorem)**, p ≥ 2, every e: `reach(p,e) = (e+2)·2^(p−2)`; upper bound `n ≤ (e+2)·2^(p−2)` for every clean plan | `Compression.conjB2`, `Compression.reach_le` | `Compression.lean` |
| Drop threshold: the first n where one more erasure helps is `(p−1)(e+1)+2` | `drop_threshold`, `estar_threshold` | `Conjectures.lean` |
| Additive upper bound at the maximal reach (2026-11-11): `M*((e+2)·2^(p−2),p,e) ≤ M*(2^(p−1),p,0) + e·(M*(2^(p−2),p−1,0)+1)` for p ≥ 2 (any sub-plans, not only Bennett's; anchor `M*(6,3,1) ≤ 13`) | `Additive.mstar_reach_le`, `anchor_6_3_1` | `Additive.lean` |
| **First drop is exactly two** (2026-11-17), p ≥ 3, every e, at n = (p−1)(e+1)+2: `M*(n,p,e) = 2n+1` and `M*(n,p,e+1) = 2n−1`; every clean plan has odd length; hence the complete tables for p = 2 and p = 3 | `first_drop`, `drop_construction`, `length_odd`, `mstar_p2`, `mstar_p3_floor`, `mstar_p3_drop`, `unreachable_p3` | `FirstDrop.lean` |
| **Contraction lower bound** (2026-11-17), p ≥ 2, every n ≥ 1, e: every clean plan has `|s| ≥ 2n − 1 + 2·max(0, n − A)` with `A = (p−1)(e+1)+1` (contract the lowest re-placed cell: delete cell 0, or OR-merge it with the cell below; at least 4 moves shorter, peak and erasures not larger). Corollaries: `n = A + j` ⇒ `≥ 2n − 1 + 2j`; `p = 4`, `n ≥ 3e+4` ⇒ `≥ 4n − 6e − 9`. Lower bounds only; the matching constructions are in `Triangular.lean` (next row) | `contraction_bound`, `length_ge`, `near_band_lower`, `p4_lower`, `contract_drop`, `contract_merge` | `Contraction.lean` |
| **Exact up to the triangular frontier** (2026-11-17), p ≥ 3, every e, `1 ≤ n ≤ T(p) + e·T(p−1)` with `T(p) = p(p−1)/2 + 1`: `M*(n,p,e) = 2n − 1 + 2·max(0, n − A)`. Construction: for `p ≤ n ≤ T(p)` split `n = a + b` and run the (p−1)-plan on `b` cells above a held stone (no erasure, `4n − 2p − 1` moves); then `e` blocks of length in `[p−1, T(p−1)]`, each on a held stone that is erased. Corollaries: `n = A + j`, `j ≤ p−2` is exact; `M*(n,4,e) = 4n − 6e − 9` for `3e+4 ≤ n ≤ 4e+7`; `M*(n,5,e) = 4n − 8e − 11` for `4e+5 ≤ n ≤ 7e+11`. Open: `n > T(p) + e·T(p−1)` (p = 4 endpoint `4e+8`) | `mstar_exact`, `near_band_exact`, `mstar_p4_interior`, `mstar_p5_interior`, `tri_spec`, `blocks_spec`, `window_seg` | `Triangular.lean` |

Bounded (oracle-level, `native_decide`, `Bounded.lean`): RC-02 anchors
(`M*(4,3,·)=9,7,7,7`, `M*(6,4,·)=15,11,11,11`, `M*(16,5,·)=71,45,37,31`,
`M*(16,6,0)=51`, `M*(16,7,0)=49`, `M*(16,6,1)=41`, `M*(17,6,0)=57`);
Conjecture B2 for p = 3 (e ≤ 6), p = 4 (e ≤ 4), p = 5 (e ≤ 2); the inequality
`M*(n,p,e+1) ≤ M*(n,p+1,e)` for n ≤ 2^(p−1), p ≤ 4, e ≤ 3; its counterexample
`M*(10,3,3) = 21 > 19 = M*(10,4,2)`; non-monotonicity `M*(16,5,0)=71 > M*(17,6,0)=57`.
The oracle (`mstarE`, `reachableE`) implements the same rules as `IsPlay` on
bit-mask boards but is *not* linked to `IsPlay` by proof.  **Since 2026-11-12 the counterexample is
also a statement about `IsPlay`**: `Checker.counterexample_verified` proves
`MstarIs 10 3 3 21 ∧ MstarIs 10 4 2 19` with a second search (`Checker.layer`,
on the boards of `IsPlay`) whose soundness `Checker.mem_layer_of_play` is
proved; only the two layer evaluations use `native_decide`.

Outside Lean (`data/erasure/`, exhaustive C/Python search, all plans re-verified
by an independent checker): Conjecture B2 `reach(p,e) = (e+2)·2^(p−2)` holds
exhaustively for p ≤ 6, e ≤ 6 and for p = 7, e ≤ 4 (40 cells, 0 mismatches);
p = 7, e ∈ {5,6} and p = 8 are lower bounds only.  The drop point
`(p−1)(e+1)+2` is verified for p ≤ 8, e ≤ 5.  The identity
`M*(reach(p,e),p,e) = M*(2^(p−1),p,0) + e·(M*(2^(p−2),p−1,0)+1)` holds for
p ≤ 6, e ≤ 6 (36 cells with data, 0 mismatches).  Its `≤` half is proved in
general (`Additive.mstar_reach_le`); the `≥` half is open.

## 2. How the lower bound of Theorem A is proved (no permutations)

RC-02 counts ascents of the removal-time permutation τ.  In Lean the
argument is a **state potential** (`Potential.lean`).  For a board `b` of
length n:

* `dCount n b` = number of pebbles whose removal would be irreversible
  (pebbled cell with empty lower neighbour; cell 0 never counts);
* `fb n b` = the largest rising edge = the bottom of the run of pebbles
  containing the highest pebble (0 if the board is empty);
* `pot n p b = ⌈(n − 1 − fb n b)/(p − 1)⌉ + dCount n b − 1`.

`pot(∅) = e*(n,p)`, `pot({n}) = 0`.  Along a *tight* play (every cell toggled
exactly the forced number of times: pebbled cells once, cells above every
pebble twice, the last cell once / zero times; `Tight` in `Saturation.lean`,
derived from `|s| = 2n−1` through the parity law `nth_execB_parity`, coverage
`frozen_above`, and `Σ_j count j s = |s|`), a placement leaves `pot`
unchanged (`pot_place`) and a removal lowers it by at most the erasure
indicator (`pot_remove`).  The only use of the peak: the frontier run
`[fb, top]` is contiguous and has ≤ p pebbles, so splitting it at i loses at
most p−1 from `n−1−fb` and the ceiling drops by at most one.  Hence
`erasures ≥ pot(∅) − pot({n}) = e*(n,p)`.  The correspondence with the
paper proof: `dCount` counts the descending runs of τ that have already
started (their bottoms), the ceiling counts the runs still needed above the
frontier.

## 3. The upper bound of Conjecture B2 — where the rigidity argument breaks

Goal: `reach(p,e) ≤ (e+2)·2^(p−2)`.  "One erasure buys one 2^(p−2) block."

**What works (e = 1, sketch).**  Before the first erasure the play is
reversible with peak p, so (Knill, `complete_bound`) every pebble ever placed
lies in `[1, 2^(p−1)]`.  Let the erasure remove x and let y be the lowest
pebble above x afterwards (if none, nothing above x can ever change again and
n ≤ 2^(p−1)).  If x is never re-pebbled, the segment above y is a
reversible play with y as a *permanent* stone: peak p−1 relative to y, starting
from a board inside `(y, 2^(p−1)]`.  A generalised Knill bound — *from a board
whose pebbles lie in [1, L], a reversible play with peak q never pebbles a cell
above L + 2^(q−1)* — gives n ≤ y + (2^(p−1) − y) + 2^(p−2) = 3·2^(p−2).  The
tables (`data/erasure/SUMMARY.md`, normal-form theory) confirm the ingredient:
in the reversible game with peak p a pebble is removable iff its gap to the
pebble below is ≤ 2^(p−k) (k = current pebble count), so a stone with a dead
gap below it is frozen for as long as it stays.

**Where it breaks for e ≥ 2 (the recursion is not self-similar).**  Repeating
the argument treats the segment above the stone y as a game with peak p−1 and
e−1 erasures.  But the next erasure in the witnesses (`witness_p*_e*.txt`:
erasures at 2^(p−1), 2^(p−1)+2^(p−2), …) is the erasure of y *itself*; at that
moment all p pebbles are above y, so the sub-game's peak jumps back to p.  The
naive recursion `R(L,q,e) ≤ L + 2^(q−1) + (e+1)·2^(q−3)` is therefore
*wrong* (it would give reach(p,2) ≤ 7·2^(p−3) < 4·2^(p−2) = the B1 value).  The
correct bookkeeping must charge each erasure of a stone with "peak p−1 while
the stone stands, one free pebble once it is gone", i.e. a potential over the
*stack of frozen stones*, not an induction on the sub-game.  This is the
missing lemma:

> **Lemma (needed).**  Let a play with peak p have frozen stones
> `s_1 < … < s_k` (each with an empty cell below it that can never be
> re-pebbled without an erasure), and let the highest pebble be h.  Then
> `h ≤ s_k + 2^(p−k−1)`-type bounds do **not** hold in general (the stones may
> be arbitrarily far apart and the free pebbles may rebuild from the entrance);
> what is true and would suffice is a bound on the *total advance*:
> `h ≤ 2^(p−1) + (number of erasures so far)·2^(p−2)`.

The two failure shapes to watch, both visible in small witnesses:
1. **Rebuilding from the entrance.**  After erasing x, cells 1 … x−1 can be
   re-pebbled reversibly from the free entrance; with enough free pebbles x
   itself can be re-placed and later removed reversibly, so "an erasure kills
   the block below x for good" is false as stated.  What is true: re-pebbling
   x needs a reversible reach of x−1 from the entrance with the pebbles not
   used as stones, i.e. x ≤ 2^(q−1) for the q free pebbles.
2. **Peak reset.**  Erasing a stone frees the pebble it occupied; the segment
   above the next stone then has peak p again (see above).

A proof of the upper bound must therefore be an induction on e with a
statement about arbitrary starting boards (not the empty board), of the shape
"from a board B whose pebbles lie in [1, L] with k stones …, a play with peak
p and e erasures reaches at most L + (e + c(B))·2^(p−2)".  We did not find the
right correction term c(B) in this session; `reachIs_zero` is the e = 0 case
(c(∅) = 2 with L = 0).

**Reduction to one lemma (2026-11-06, `UpperBound.lean`).**  Define on a board
`b` with `k = ones b` pebbles the threshold `T_k = 2^(p−k)`, the gap of a
pebble as its distance to the previous pebbled node (or the entrance), and
the potential `phi p b = min over pebbled z of (max(0, gap z − T_k) +
phi p (toggle b z))`, `phi ∅ = 0` (least total excess over all removal
orders; equivalently the least total excess over all insertion orders, each
insertion measured against the threshold at the count it creates).  Proved
in Lean (sorry 0, standard axioms): a legal placement never increases
`phi`; removing *any* pebble raises `phi` by at most `2^(p−2)`
(two-level induction through the recursion; the only delicate case is the
removal of the predecessor of the pebble an optimal order removes first);
`phi ∅ = 0` and `phi {n} ≥ n − 2^(p−1)`.  Hence `n ≤ (e+2)·2^(p−2)` follows
(`reach_le_of_removalLemma`, `conjB2_of_removalLemma`) **from the single
open lemma `RemovalLemma p`: a reversible removal (predecessor pebbled)
never increases `phi`.**  That lemma was checked exhaustively on all boards
for `(p, n) = (2, 8), (3, 9), (4, 10)` (`#guard`s in the file) and, for all
cheap removals (gap ≤ `T_k`, more than the game needs) on all configurations
with ≤ p pebbles among 16/24/22 nodes for p = 3/4/5
(`data/erasure/potential_check.py`).  The potential equals the exact charged
value `max_e (reach_e(b) − e·2^(p−2))` on every configuration for p ≤ 4
(verified against the BFS tables).  Attempted proofs of the lemma (exchange
arguments on insertion orders; induction through the recursion with a
“shift-down” lemma `phi((Y − x) ∪ v) ≤ phi(Y) + max(0, (v − u) − T)`) all
close every case except the one where the optimal order first removes a long
descending chain of predecessors of `x`; see the report
`/work/tmp/work-runs/G-erasure-b2/t1/REPORT.md` of that session.

**Second attempt (2026-11-06, `RemovalCases.lean`, report
`/work/tmp/work-runs/G-erasure-b2/t2/REPORT.md`).**  Still open; what changed:

*Gap-merge form.*  Write a board as its gap sequence `B_1, …, B_m` (gap =
distance to the previous pebbled node).  Removing the pebble of `B_i` at
count `m` pays `max(0, B_i − T_m)` and merges `B_i` into `B_{i+1}` (deletes it
if `i = m`).  `phi` is the least total payment to empty the sequence.  A
removal order is a forest (parent = nearest earlier-inserted pebble below);
each pebble pays `max(0, (its gap to its parent) − T_level)`.

*Reversible components = reduced boards.*  A pebble with gap ≤ `T_m` is
*free*: its removal is reversible (reach the predecessor with the `p − m`
free pebbles, remove, undo; peak stays ≤ p).  Every reversible move is a free
removal or its inverse, and free removals are confluent (after removing a
free `z`, a free `x` keeps gap ≤ `2·T_m = T_{m−1}`).  So each reversible
component has a unique reduced board, and `RemovalLemma` is equivalent to
(R′) `phi(b − x) ≤ phi(b)` for every free `x`, i.e. “`phi` is constant on
components”.  (The easy direction `phi(b) ≤ phi(b − x)` is `x` last.)

*Stronger forms, all verified by computer and all still open* (`FreeRemoval`,
`SlackRemoval` in `RemovalCases.lean`; `data/erasure/rcheck.c`,
`data/erasure/potential_structure.py`):
(S) removing *any* pebble raises `phi` by at most its excess
`max(0, gap − T_m)`; together with the proved `2^(p−2)` bound this gives
`min(excess, 2^(p−2))`, which is exactly the measured maximum.
(DEL) for *every* optimal removal order `O` and every free `x`, deleting
`x`'s step from `O` gives an order of `b − x` of cost ≤ `phi(b)` — so “`x`
first” is always optimal; the surgery is canonical, only its cost bound is
missing.  Checked: p ≤ 5, gaps ≤ 14.  (R′) and (S): p = 5 gaps ≤ 20,
p = 6 gaps ≤ 22, p = 7 gaps ≤ 11 (`rcheck.c`, 7.1·10^8 removals, 0 failures).

*Where the recursion closes and where not.*  Let `z` be the pebble an optimal
order removes first.  If `z = x`, or `z` is not adjacent to `x`, or `z` is
the pebble just *above* `x`, or `z` is the predecessor of `x` with
`gap z ≤ T_m`: the induction closes (the doubled threshold absorbs the merged
gap ≤ `T_m`).  Proved in Lean as the two cases where no other case can
occur: the highest pebble (`phi_toggle_le_of_top`, any gap) and the lowest
pebble when free (`phi_toggle_le_of_lowest_free`).  The open case: `z` is
the predecessor of `x` and `gap z + gap x > 2·T_m`.  Then `x` has gap
`> T_{m−1}` after `z` is gone and the hypothesis is lost.  Recursing further,
the optimal order removes a descending chain `w_1 > w_2 > …` of predecessors
of `x`, each paying `e_i = gap w_i − 2^{i−1}T_m > 0`; the naive accounting
closes iff every `e_i ≤ 2^{i−1}T_m` (every chain element doubly excessive is
the problem).

*The e = 0 case of (R′) is proved on paper* (zero-cost orders): delete `x`
from a zero-cost insertion order; a child `u` of `x` whose new parent is
lower gets gap ≤ `(u − x) + T_m + (gap of the predecessor chain of `x`
inserted after `x`)` ≤ `T_u + T_u` = its doubled threshold, because the
chain's thresholds are distinct powers of two below `T_u`.  With positive
excess on that chain the same bound gives “new excess ≤ old excess + chain
excess”, and the chain's own saving from the doubled threshold is only
`min(excess, T)` per element — the gap in the argument is exactly the doubly
excessive chain elements again.

*Surgeries that do and do not work* (numerically, on optimal orders).  For
free `x`: deleting `x` always works ((DEL) above).  For (S) with `x` not
free, deletion fails (e.g. gaps `(6,1,3)`, p = 4, remove the lowest: the
optimal order of the result turns the *star* of `x`'s children into a
*chain*, lowest child first), and “replace `x` by its predecessor” fails
when `x` has ≥ 2 children; so a proof of (S) needs the star-to-chain
rewrite, while (R′)/(DEL) needs only deletion plus an optimality argument.
Optimality of `O` only yields *lower* bounds on alternative orders, so the
missing step is an upper bound on the extra cost of the c-steps (removals of
the block just above `x` before `x` is removed): each such step costs at most
`max(0, X_s − T_s)` extra, `X_s` = content of `x`'s block at that time; the
savings are the doubled thresholds of the other steps and `x`'s own payment.

**Third attempt (2026-11-10, `Sliding.lean`, report
`/work/tmp/work-runs/G-erasure-b2-del/t1/REPORT.md`).**  Still open; the open
case is now a single boundary configuration.

*Sliding the predecessor (proved, `freeRemoval_of_boundaryStep`).*  Let `x`
be free with `gap x < T` (strictly), let its predecessor `v` have
`gap v > T`, and let an optimal order remove `v` first.  Move `v` down by one
cell to get `b'`.  Then `b' − v' = b − v`, so `phi b' ≤ phi b − 1`; `x` is
still free in `b'`; and `b − x` is `b' − x` with `v'` moved up by one cell,
which raises `phi` by at most one (`phi_moveUp_le`: follow an optimal order,
only the block of the moved pebble grows).  With an inner induction on the
position of the predecessor, `phi (b − x) ≤ phi (b' − x) + 1 ≤ phi b' + 1 ≤
phi b`.  So the whole of (R′) follows from the **boundary step**
(`BoundaryStep p`): `gap x = T` exactly, `gap v > T`, `v` first is the
*unique* optimal first step; (R′) may be used on boards with fewer pebbles
and on boards of the same count with a lower predecessor.  Lean:
`conjB2_of_boundaryStep`.  Numerically the premises of the boundary step
never hold together (`data/erasure/slide_check.py`: whenever `v` first is
optimal at the boundary, `x` first is optimal too, and then
`T < gap v ≤ 2T`).

*Other tools found (paper only, checked numerically).*
(1) *Two free pebbles.*  If `b` has two free pebbles `x ≠ y`, the first
pebble of an optimal order is not the predecessor of both, so the induction
closes for one of them; `phi (b − x) = phi (b − y) = phi (b − x − y)` by
confluence, so it closes for both.
(2) *Promotion.*  For two non-adjacent pebbles removed consecutively the
order "smaller `min((gap − T)^+, T)` first" is never worse.  In particular a
doubly excessive pebble (`gap ≥ 2T`) can be delayed past any non-adjacent
step, so an optimal order that starts with a doubly excessive `v` and then
removes `y ∉ {x, pred v}` can be replaced by one that starts with `y`.
A doubly excessive pebble is never followed immediately by its successor.
(3) *Move-down inequality (MD), the statement that is really missing.*
For `Y = (L, G, r, R)` at threshold `S` and `0 < d < G`,
`phi_S(L, G − d, r + d, R) ≤ phi_S(Y) + W3(G, d, S)`,
`W3 = Σ_{n ≥ 0} min(d, (G − 2^n S)^+)` — one unit of `d` for every future
threshold below the gap of `x`.  It holds on all enumerated boards
(`data/erasure/move_down_check.py`) and gives the boundary step
(`Y = b − v`, `S = 2T`, `d = T`: `W3 ≤ gap v − T`) and (S) for gaps `≤ 2T`.
Given (R′) and (S) for gaps `≤ 2T` at the same count (they cover the case
`G − d ≤ S`), its first-step induction closes when the first optimal pebble
is `x`, is not adjacent to `x`, is the successor of `x` (one unit of `d` is spent), or is
the predecessor `u` of `x` with `gap u ≤ 2S`; with a sliding step it also
closes for `gap u > 2S` unless a threshold `2^n S` lies in `(G − d, G]`.
What remains is: `u` first is the unique optimum, `gap u > 2S`, the next
optimal step is the predecessor of `u`, and `G` is within `d` above a
threshold.  Under the same two assumptions a weaker static bound *is* provable by the
plain induction:
`d · #{n ≥ 0 : 2^n S < max_l (G + C_l)/2^l}`, `C_l` = the sum of the `l` gaps
just below `x` — it does not use optimality and is too weak when a deep
pebble below `x` is very excessive.
(4) *Why optimality must enter.*  With `u` very excessive the budget of MD
cannot be kept by any bound that only looks at gaps: the true reason is that
"`x` first, `u` survives" becomes cheaper than "`u` first" (the successors of
`x` are then removed top-down instead of bottom-up).  A proof of the last
case has to compare with that order.

**Fourth attempt (2026-11-10, `Compression.lean`, report
`/work/tmp/work-runs/G-erasure-b2-del/t2/REPORT.md`): the upper bound is
proved, without the removal lemma.**  `RemovalLemma` / (R′) / (DEL) for `phi`
are still open, but Conjecture B2 no longer needs them: use a *smaller*
potential for which the reversible step is easy.

*The potential.*  Give each cell a width `w i` (`w ≡ 1` on the real chain)
and let `wphi p w b` be `phi` computed with weighted gaps.  Call `b` *flat*
for `w` if `wphi p w b = 0`.  The squeezing number `psi(b)` is the least
number of cells whose width must be set to 0 to make `b` flat (never defined
in Lean; the proof carries the widths along the play instead).

*The four steps* (all in Lean, sorry 0, standard axioms):
(a) a legal placement keeps a flat board flat for the same widths
(`wphi_toggle_le_of_place`; the new pebble has weighted gap `w x ≤ 1`);
(b) a reversible removal keeps a flat board flat for the same widths
(`wphi_zero_of_free`).  This is (R′) **restricted to boards of potential 0**,
and there the first-step induction closes: the pebble `z` removed first by a
zero-cost order has gap `≤ T`, so the merged gap of `x` is `≤ 2T`, the next
threshold.  The blocking case of the earlier attempts (the predecessor is
removed first *with positive excess*) cannot occur at cost 0;
(c) an erasure raises `wphi` from 0 to at most `2^(p−2)`
(`wphi_toggle_le_of_remove`, weighted copy of the old proof), and a board of
potential `k` is flat after squeezing at most `k` cells (`compress`: if the
pebble removed first by an optimal order has positive excess, shrink one
cell of its gap; otherwise recurse; shrinking never raises `wphi`,
`wphi_mono`);
(d) the target `{n}` is flat only if the total width is `≤ 2^(p−1)`
(`wphi_target`).
So after `e` erasures at most `e·2^(p−2)` cells are squeezed and
`n ≤ 2^(p−1) + e·2^(p−2)` (`flat_execB`, `reach_le`, `conjB2`).

*Why this was missed.*  `psi ≤ phi` (`compress`) and the inequality can be
strict: nodes `{2, 5, 7}` with `p = 3` have `phi = 2`, `psi = 1` (squeeze the
entrance cell; `#guard`s at the end of `Compression.lean`;
`data/erasure/compression_check.py` finds 10 such boards for `p = 3`,
`n = 10` and 5 for `p = 4`, `n = 11`).  One squeezed cell can repair several
*nested* excessive gaps at once, whereas `phi` pays for each of them.  So
`phi` is **not** the least potential of the game, and its invariance under
reversible moves — which the three earlier attempts tried to prove — is a
harder statement than the conjecture needs.  (If (R′) holds, `phi` is a
second, larger valid potential.)

*Checked numerically* (`data/erasure/compression_check.py`, all boards with
at most `p` pebbles among `n` cells, `(p, n) = (2, 8), (3, 10), (4, 11)`):
`psi` never rises under a placement or a reversible removal, rises by at most
`2^(p−2)` under an erasure, and `psi({m}) = max(0, m − 2^(p−1))`; 0 failures.

## 4. The inequality `M*(n,p,e+1) ≤ M*(n,p+1,e)`

False in general: `M*(10,3,3) = 21 > 19 = M*(10,4,2)` (`ineq_counterexample`;
all 213 violations in `data/erasure/inequality.md`, e.g. (12,3,3), (14,3,4),
(17,4,3)).  It holds for every checked (n,p,e) with n ≤ 2^(p−1) (482 comparisons:
474 from the dense table `mstar.csv` plus 8 from `mstar_ext.csv`; 0 violations); stated as `IneqM_conj` in `Conjectures.lean`.

Proof idea for n ≤ 2^(p−1) (draft, not formalised).  Take an optimal plan with
peak p+1 and e erasures.  Since n ≤ 2^(p−1), the plan never needs the (p+1)-st
pebble for *reach*; the extra pebble is only ever used as a temporary stone to
shorten uncomputation.  Replace the first moment the (p+1)-st pebble is on the
board: the lowest pebble at that moment sits on a cell whose lower neighbour is
either empty (then erase it now, saving its later reversible removal and the
re-pebbling that supports it) or pebbled (then the run below it is a Bennett
tail that can be uncomputed later at no more cost).  Each such replacement
trades one erasure for one pebble without lengthening the plan; the difficulty
is showing one replacement suffices (the counterexamples with n > 2^(p−1) are
exactly the instances where the (p+1)-st pebble is needed for reach and the
trade costs 2 extra moves).

## 5. Manifest / audit

`ErasurePebbling` is registered as a second default target in
`lakefile.toml`; `scripts/build_proof_manifest.py` hashes its sources and
audits the stages `erasure_pebbling_*` (general theorems: standard axioms
only; `Bounded.lean`: native_decide, BOUNDED).  The manifest values in this
branch were computed locally with Lean 4.32.2 (the CI toolchain is 4.31.0);
a manifest diff on CI, if any, is expected only in these stages.

## RESUME (for the next session)

Proved: Theorem A (both directions, `theoremA`), Theorem B1 (`theoremB1`),
floor, drop threshold, Knill's reach at e = 0 (`reachIs_zero`), and
**Conjecture B2 for every p ≥ 2 and every e** (`Compression.conjB2`,
2026-11-10); all sorry-free with standard axioms.  Bounded: B2 for p ≤ 5 (Lean oracle), p ≤ 6 and p = 7,
e ≤ 4 (C search in `data/erasure/`).

Open:
0. The `≥` half of the additive identity at the maximal reach (§1): every
   clean plan for `(e+2)·2^(p−2)` with peak p and e erasures has at least
   `M*(2^(p−1),p,0) + e·(M*(2^(p−2),p−1,0)+1)` moves.  The `≤` half is
   `Additive.mstar_reach_le`.
1. (No longer needed for B2, which is proved in `Compression.lean`.)  The
   invariance of `phi` itself: `RemovalLemma p` (§3, `UpperBound.lean`),
   reduced to `BoundaryStep p`
   (`Sliding.lean`, §3 third attempt): the free pebble sits exactly at the
   threshold and its non-free predecessor is the unique optimal first step.
   Next step: prove the move-down inequality (MD) of §3 in its last case
   (very excessive predecessor, gap of `x` just above a threshold) by
   comparing with the order "`x` first, predecessor survives"; or show
   directly that the premises of `BoundaryStep` are contradictory.  Two special cases are proved (`phi_toggle_le_of_top`,
   `phi_toggle_le_of_lowest_free`).  The Knill-style route (generalised
   complete-computation bound) breaks because the reversed suffix of a play
   with erasures has free placements and no longer covers the chain.
2. Partly done (2026-11-12, `Checker.lean`): a separate search proved sound
   against `IsPlay`, which turns any lower bound on `M*` into a statement about
   `MstarIs` and has re-derived the counterexample.  Still open: the bit-mask
   oracle `mstarE` itself, and moving the other `Bounded.lean` anchors to
   `Checker` (cheap: one play plus one empty layer each).
3. `IneqM_conj` (inequality for n ≤ 2^(p−1)).
4. Optional: `reach` monotone in n (`Reachable (n+1) → Reachable n`, by the
   projection lemma of `data/erasure/SUMMARY.md`), which turns `ReachIs` into a
   statement about a maximum.

Build locally without mathlib: put `RevPebbling/PebblingFoundations.lean`,
`RevPebbling/LiftAbove.lean`, `RevPebbling/PebblingGame.lean` and
`ErasurePebbling/` into a scratch Lake workspace with two `lean_lib`s and no
`require`; `lake build` takes ~45 s (Bounded.lean dominates).
