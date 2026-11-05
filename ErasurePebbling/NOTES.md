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
| Drop threshold: the first n where one more erasure helps is `(p−1)(e+1)+2` | `drop_threshold`, `estar_threshold` | `Conjectures.lean` |

Bounded (oracle-level, `native_decide`, `Bounded.lean`): RC-02 anchors
(`M*(4,3,·)=9,7,7,7`, `M*(6,4,·)=15,11,11,11`, `M*(16,5,·)=71,45,37,31`,
`M*(16,6,0)=51`, `M*(16,7,0)=49`, `M*(16,6,1)=41`, `M*(17,6,0)=57`);
Conjecture B2 for p = 3 (e ≤ 6), p = 4 (e ≤ 4), p = 5 (e ≤ 2); the inequality
`M*(n,p,e+1) ≤ M*(n,p+1,e)` for n ≤ 2^(p−1), p ≤ 4, e ≤ 3; its counterexample
`M*(10,3,3) = 21 > 19 = M*(10,4,2)`; non-monotonicity `M*(16,5,0)=71 > M*(17,6,0)=57`.
The oracle (`mstarE`, `reachableE`) implements the same rules as `IsPlay` on
bit-mask boards but is *not* linked to `IsPlay` by proof.

Outside Lean (`data/erasure/`, exhaustive C/Python search, all plans re-verified
by an independent checker): Conjecture B2 `reach(p,e) = (e+2)·2^(p−2)` holds
exhaustively for p ≤ 6, e ≤ 6 and for p = 7, e ≤ 4 (40 cells, 0 mismatches);
p = 7, e ∈ {5,6} and p = 8 are lower bounds only.  The drop point
`(p−1)(e+1)+2` is verified for p ≤ 8, e ≤ 5.  The identity
`M*(reach(p,e),p,e) = M*(2^(p−1),p,0) + e·(M*(2^(p−2),p−1,0)+1)` holds for
p ≤ 6, e ≤ 6.

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

## 4. The inequality `M*(n,p,e+1) ≤ M*(n,p+1,e)`

False in general: `M*(10,3,3) = 21 > 19 = M*(10,4,2)` (`ineq_counterexample`;
all 213 violations in `data/erasure/inequality.md`, e.g. (12,3,3), (14,3,4),
(17,4,3)).  It holds for every checked (n,p,e) with n ≤ 2^(p−1) (474 comparisons,
0 violations); stated as `IneqM_conj` in `Conjectures.lean`.

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
floor, drop threshold, Knill's reach at e = 0 (`reachIs_zero`); all sorry-free
with standard axioms.  Bounded: B2 for p ≤ 5 (Lean oracle), p ≤ 6 and p = 7,
e ≤ 4 (C search in `data/erasure/`).

Open:
1. Conjecture B2 upper bound `reach(p,e) ≤ (e+2)·2^(p−2)`.  Next step: prove the
   *generalised Knill bound* (reversible play from a board inside [1, L] with
   peak q stays below L + 2^(q−1)) with the `shiftAbove`/`complete_bound`
   machinery of `PebblingFoundations`, then the e = 1 case exactly as in §3;
   then look for the potential over the stack of frozen stones for e ≥ 2.
2. Link the oracle to `IsPlay` (soundness/completeness of `mstarE`), so the
   bounded certificates become statements about `MstarIs`/`ReachIs`.
3. `IneqM_conj` (inequality for n ≤ 2^(p−1)).
4. Optional: `reach` monotone in n (`Reachable (n+1) → Reachable n`, by the
   projection lemma of `data/erasure/SUMMARY.md`), which turns `ReachIs` into a
   statement about a maximum.

Build locally without mathlib: put `RevPebbling/PebblingFoundations.lean`,
`RevPebbling/LiftAbove.lean`, `RevPebbling/PebblingGame.lean` and
`ErasurePebbling/` into a scratch Lake workspace with two `lean_lib`s and no
`require`; `lake build` takes ~45 s (Bounded.lean dominates).
