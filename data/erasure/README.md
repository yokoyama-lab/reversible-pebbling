# tables/ — computed data for erasure-budgeted clean reversible pebbling of a chain

Model (rc02_erasure_pebbling.tex, Def. 1–2): chain 0→1→…→n, node 0 a free entrance; a move flips the pebble of an
*available* node (i = 1 or i−1 pebbled); an *erasure* removes the pebble of a non-available node; a clean plan goes
∅ → {n} with ≤ p pebbles and ≤ e erasures.  M*(n,p,e) = min moves, reach(p,e) = max n.  Everything here is exact
(exhaustive), see SUMMARY.md for the proofs of the reductions used.

| file | content |
|---|---|
| `SUMMARY.md` | all results, methods, checks, timings (start here) |
| `reach.csv`, `reach.md` | reach(p,e) for p = 2..7, e = 0..6; column `proved` = yes iff the chain of length reach+1 was exhausted; `Mstar_at_reach` |
| `mstar.csv`, `mstar.md` | M*(n,p,e) for n ≤ 24, p ≤ 8, e ≤ 6 (empty = impossible) |
| `mstar_ext.csv` | M*(n,p,e) for n ≤ 129 (p ≤ 6, e ≤ 6) and n ≤ 64 (p = 7, e = 0), from the C runs |
| `inequality.md` | check of M*(n,p,e+1) ≤ M*(n,p+1,e): holds iff n ≤ 2^(p−1); all counterexamples listed |
| `drops.md` | first n where an extra erasure helps (= (p−1)(e+1)+2), p_min(n) sequence and its non-monotone steps |
| `witness_p{p}_e{e}.txt` | one verified clean plan for n = reach(p,e), p = 2..8, e = 0..6: `step | move | config | #pebbles | erasures`; moves are `place i` / `remove i` / `ERASE i`; header lists erasure positions and τ-ascents |
| `witness_index.md` | plan lengths vs M*, which witnesses are BFS-optimal, erasure positions |
| `raw/` | raw outputs of the C searches (`reach_N*_p*_E*.txt`: first-hit depth per (n, erasures) and witnesses; `nfsearch_*.txt`: normal-form search logs) |

Code (Python 3 stdlib + gcc): `pebble.py` (dense BFS, `check_plan` verifier, `--all` pipeline), `reachbfs.c` (exhaustive
BFS over ≤p-pebble configurations, `./reachbfs N p E [-w]`), `normalform.py` (component theory, Python reference of the
normal-form search), `nfsearch.c` / `nfsearch_omp.c` (`./nfsearch_omp p E nmax`, OpenMP), `aggregate.py` (builds every
table from `raw/`), `summary.py` (writes SUMMARY.md), `variant_check.py` (touch variant), `run_p7_chain.sh`.

Reproduce: `python3 pebble.py --all --small` (~5 min: everything except p = 7) or `python3 pebble.py --all` (+ ~15 min,
needs ~6 GB).  Re-verify any witness: `python3 -c "import pebble; print(pebble.check_plan(pebble.parse_witness_file('witness_p5_e3.txt'), 40, 5, 3))"`.
