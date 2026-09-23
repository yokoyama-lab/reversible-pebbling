# SUMMARY – erasure-budgeted clean reversible pebbling of a chain

All files in this directory (`tables/`).  Reproduce everything with `python3 pebble.py --all` (≈ 5 min without the
p=7/8 normal-form searches, `--small`; the p=7 search takes longer, see timings).  Scripts: `pebble.py` (dense BFS,
plan checker, pipeline), `reachbfs.c` (exhaustive C BFS over ≤p-pebble configurations, rank-indexed bitsets, optional
optimal-witness extraction), `normalform.py` (component theory + exact normal-form search, Python reference),
`nfsearch.c` / `nfsearch_omp.c` (the same search in C, serial / OpenMP), `aggregate.py` (tables and checks),
`variant_check.py`, `summary.py`.

## 1. Definitions used (the model of `rc02_erasure_pebbling.tex`, Def. 1–2)

Chain 0 → 1 → ⋯ → n; node 0 is a free entrance (always available, never counted).  A configuration is the set of
pebbled nodes among 1..n.  Node i is *available* iff i = 1 or i−1 is pebbled.  A move flips the pebble of an
available node (place or remove; these are mutually inverse).  An *erasure* (irreversible removal) removes the pebble
of a node that is **not** available (predecessor empty; node 1 therefore never erases).  A **clean** plan with peak
p and budget e starts from ∅, ends at exactly {n}, never has more than p pebbles and uses ≤ e erasures.
M*(n,p,e) = its minimum number of moves (∞ if none); reach(p,e) = the largest n with a plan.

*Variant that matches the note's numbers:* the clean end is essential.  The clean model reproduces every anchor of
the note exactly: M*(4,3,e)=9,7,7,7; M*(6,4,e)=15,11,11,11; **M*(16,5,e)=71,45,37,31**; **M*(16,6,0)=51**;
M*(16,7,0)=49; M*(17,6,0)=57; reach(5,0)=16.  (So (n,p) = (16,5) is the 71/45/51 example.)  The "touch" variant
(goal merely pebbled at some moment, no clean end) gives 29/27/27 for n=16, p=5 and reach_touch(p,0) = 2^p−1 – it
does not fit (`variant_check.py`).

*Projection lemma* (used for every table): deleting from a plan all moves on nodes > n leaves a legal clean plan for
n with the same or fewer moves/pebbles/erasures.  Hence one BFS on a chain of length N gives M*(n,p,e) for every
n ≤ N, and exhausting the state space of a chain of length reach+1 proves the reach.

## 2. reach(p,e)   (`reach.csv`, `reach.md`)

| p \ e | 0 | 1 | 2 | 3 | 4 | 5 | 6 | method |
|---|---|---|---|---|---|---|---|---|
| 2 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | exhaustive BFS N=9 |
| 3 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | exhaustive BFS N=17 |
| 4 | 8 | 12 | 16 | 20 | 24 | 28 | 32 | exhaustive BFS N=33 |
| 5 | 16 | 24 | 32 | 40 | 48 | 56 | 64 | exhaustive BFS N=65 |
| 6 | 32 | 48 | 64 | 80 | 96 | 112 | 128 | exhaustive BFS N=129 |
| 7 | 64 | 96 | 128 | 160 | 192 | – | – | normal-form search nmax=161; normal-form search nmax=193 |

(* = lower bound only.)  **Every proved value equals (e+2)·2^(p−2)** (Conjecture B2 of the note) – fits all 40 proved cells.
Proved range: p ≤ 7 with e ≤ 6 for p ≤ 6, p=7 for e ≤ 4.
Alternatives tested and rejected: 2^p−1+e·2^(p−2) and (e+1)·2^(p−2) (Li–Tromp–Vitányi lemma 1) fail on every cell with
p ≥ 2 resp. every cell; 2^(p−1)+e·2^(p−2) is the same formula as (e+2)2^(p−2).

Methods.  p ≤ 6: exhaustive layered BFS over all (config with ≤ p pebbles, erasures used) states of the chain of
length reach(p,6)+1 (`reachbfs.c`), which also yields M*(n,p,e) for all n ≤ 129, p ≤ 6, e ≤ 6 (`mstar_ext.csv`):
- N=129 p=6 E=6 states=291860250 depth=734 seconds=79
- N=17 p=3 E=6 states=1152 depth=37 seconds=0
- N=33 p=4 E=6 states=30354 depth=98 seconds=0
- N=64 p=6 E=2 states=18711284 depth=446 seconds=6
- N=64 p=7 E=0 states=172923709 depth=665 seconds=50
- N=65 p=5 E=6 states=1920811 depth=265 seconds=0
- N=80 p=6 E=3 states=45055758 depth=518 seconds=14
- N=97 p=6 E=4 states=92270279 depth=590 seconds=22
- N=9 p=2 E=6 states=98 depth=18 seconds=0

p ≥ 7: exact **normal-form search** (`normalform.py` docstring has the proof).  In the reversible game with peak p a
pebble x is *removable* iff its gap to the pebble below (or to node 0) is ≤ 2^(p−k), k = current number of pebbles
(touch x−1 with the free pebbles, remove x, undo).  Removability is preserved when another removable pebble is
removed, so greedy elimination has a unique normal form nf(C) (Newman's lemma), placing a pebble creates a
removable pebble, hence nf is invariant under reversible moves and **two configurations are reversibly connected iff
they have the same normal form**; in particular {n} is reachable from ∅ iff n ≤ 2^(p−1).  The search keeps only
normal forms: N₀ = {∅}, N_(e+1) = N_e ∪ {nf(C∖x) : nf(C) ∈ N_e, x erasable in C}, enumerating each component
without a visited set by canonical reverse elimination (each configuration generated exactly once).  It was validated
configuration-by-configuration against the brute force for p ≤ 5 and by all reach values and state counts for p = 6.
Memory (the table of normal forms) is the limit: the p=7 run storing all levels was OOM-killed (15 GB) while storing the
level-3 normal forms; the reruns process the last level without storing its successors (N_(e+1) is complete once level e
is processed).  p = 8 was not attempted: comp(∅) alone has ~10^11 configurations (~2.5 h on 4 cores), and the level-1
normal forms would not fit in memory; reach(8,e) ≥ (e+2)·64 holds by the verified witnesses.
nfsearch_p7_E3_n161.txt:
```
# nfsearch_omp p=7 E=3 nmax=161 threads=4
e=0 reach=64 conj=64 PROVED new_normal_forms=1 configs_this_level=427562462 configs_total=427562462 seconds=30
complete e=1 reach=96 conj=96 PROVED normal_forms_at_level=14816920 seconds=30
e=1 reach=96 conj=96 PROVED new_normal_forms=14816920 configs_this_level=1201662872 configs_total=1629225334 seconds=132
complete e=2 reach=128 conj=128 PROVED normal_forms_at_level=50823269 seconds=132
e=2 reach=128 conj=128 PROVED new_normal_forms=50823269 configs_this_level=2460896842 configs_total=4090122176 seconds=277
complete e=3 reach=160 conj=160 PROVED normal_forms_at_level=not_stored seconds=277
# total normal forms 65640190
```
nfsearch_p7_E4_n193.txt:
```
# nfsearch_omp p=7 E=4 nmax=193 threads=4
e=0 reach=64 conj=64 PROVED new_normal_forms=1 configs_this_level=427562462 configs_total=427562462 seconds=30
complete e=1 reach=96 conj=96 PROVED normal_forms_at_level=14816920 seconds=30
e=1 reach=96 conj=96 PROVED new_normal_forms=14816920 configs_this_level=1201662872 configs_total=1629225334 seconds=123
complete e=2 reach=128 conj=128 PROVED normal_forms_at_level=50823269 seconds=123
e=2 reach=128 conj=128 PROVED new_normal_forms=50823269 configs_this_level=2478077676 configs_total=4107303010 seconds=375
complete e=3 reach=160 conj=160 PROVED normal_forms_at_level=119539000 seconds=375
e=3 reach=160 conj=160 PROVED new_normal_forms=119539000 configs_this_level=4476886814 configs_total=8584189824 seconds=645
complete e=4 reach=192 conj=192 PROVED normal_forms_at_level=not_stored seconds=645
# total normal forms 185179190
```
nfsearch_p7_E6_n257.txt:
```
# nfsearch_omp p=7 E=6 nmax=257 threads=4
e=0 reach=64 conj=64 PROVED new_normal_forms=1 configs_this_level=427562462 configs_total=427562462 seconds=37
e=1 reach=96 conj=96 PROVED new_normal_forms=14816920 configs_this_level=1201662872 configs_total=1629225334 seconds=138
e=2 reach=128 conj=128 PROVED new_normal_forms=50823269 configs_this_level=2478077676 configs_total=4107303010 seconds=391
```

Bonus identity at the reach (all p ≤ 6, e ≤ 6; and p=7, e=0): **M*(reach(p,e),p,e) = M*(2^(p−1),p,0) + e·(M*(2^(p−2),p−1,0)+1)**,
i.e. the block construction of Theorem B1 with optimal sub-plans is move-optimal at the reach.  Base values
M*(2^(p−1),p,0) for p = 1..7: 1, 3, 9, 25, 71, 193, 531.  Increment per erasure block (p=3..7): 4, 10, 26, 72, 194.

## 3. M*(n,p,e)   (`mstar.csv`, `mstar.md`: n ≤ 24, p ≤ 8, e ≤ 6; `mstar_ext.csv`: n ≤ 129, p ≤ 6)

Theorem A of the note, M*(n,p,e) = 2n−1 ⇔ e ≥ e*(n,p) = ⌈(n−1)/(p−1)⌉−1, holds on every finite entry (0 violations).
Extract at the minimal peak p_min(n) (least p with 2^(p−1) ≥ n):

| n | p_min | e=0 | e=1 | e=2 | e=3 | e=4 | 2n−1 |
|---|---|---|---|---|---|---|---|
| 2 | 2 | 3 | 3 | 3 | 3 | 3 | 3 |
| 3 | 3 | 5 | 5 | 5 | 5 | 5 | 5 |
| 4 | 3 | 9 | 7 | 7 | 7 | 7 | 7 |
| 5 | 4 | 11 | 9 | 9 | 9 | 9 | 9 |
| 6 | 4 | 15 | 11 | 11 | 11 | 11 | 11 |
| 7 | 4 | 19 | 13 | 13 | 13 | 13 | 13 |
| 8 | 4 | 25 | 17 | 15 | 15 | 15 | 15 |
| 9 | 5 | 25 | 17 | 17 | 17 | 17 | 17 |
| 10 | 5 | 29 | 21 | 19 | 19 | 19 | 19 |
| 11 | 5 | 33 | 25 | 21 | 21 | 21 | 21 |
| 12 | 5 | 39 | 29 | 23 | 23 | 23 | 23 |
| 13 | 5 | 45 | 33 | 25 | 25 | 25 | 25 |
| 14 | 5 | 53 | 37 | 29 | 27 | 27 | 27 |
| 15 | 5 | 61 | 41 | 33 | 29 | 29 | 29 |
| 16 | 5 | 71 | 45 | 37 | 31 | 31 | 31 |
| 17 | 6 | 57 | 45 | 35 | 33 | 33 | 33 |
| 18 | 6 | 63 | 49 | 39 | 35 | 35 | 35 |
| 19 | 6 | 69 | 53 | 43 | 37 | 37 | 37 |
| 20 | 6 | 77 | 57 | 47 | 39 | 39 | 39 |
| 21 | 6 | 85 | 61 | 51 | 41 | 41 | 41 |
| 22 | 6 | 93 | 65 | 55 | 45 | 43 | 43 |
| 23 | 6 | 101 | 69 | 59 | 49 | 45 | 45 |
| 24 | 6 | 109 | 73 | 63 | 53 | 47 | 47 |
| 25 | 6 | 117 | 77 | 67 | 57 | 49 | 49 |
| 26 | 6 | 125 | 81 | 71 | 61 | 51 | 51 |
| 27 | 6 | 135 | 85 | 75 | 65 | 55 | 53 |
| 28 | 6 | 145 | 91 | 79 | 69 | 59 | 55 |
| 29 | 6 | 155 | 97 | 83 | 73 | 63 | 57 |
| 30 | 6 | 167 | 103 | 87 | 77 | 67 | 59 |
| 31 | 6 | 179 | 109 | 91 | 81 | 71 | 61 |
| 32 | 6 | 193 | 115 | 95 | 85 | 75 | 63 |
| 33 | 7 | 153 | ? | ? | ? | ? | 65 |

## 4. Inequality M*(n,p,e+1) ≤ M*(n,p+1,e)   (`inequality.md`)

- For n ≤ 2^(p−1) = reach(p,0) the inequality HOLDS in all 482 comparisons (0 violations). 86 are strict; the 396 ties are all at the floor 2n−1 (396 of 396), so for n ≤ 2^(p−1): M*(n,p,e+1) < M*(n,p+1,e) ⇔ M*(n,p+1,e) > 2n−1 ⇔ e < ⌈(n−1)/p⌉−1.
- For n > 2^(p−1) (n not reversibly reachable with p pebbles) it FAILS: 213 violations, of which 117 have both sides finite (smallest: [(10, 3, 2, 21, 19), (12, 3, 3, 25, 23), (14, 3, 4, 29, 27)]) and 96 have M*(n,p,e+1) = ∞ (one pebble reaches n, one erasure does not: reach(p,e+1) = (e+3)2^(p−2) < (2e+4)2^(p−2) = reach(p+1,e)).

## Violations

| n | p | e | M*(n,p,e+1) | M*(n,p+1,e) |
|---|---|---|---|---|
| 2 | 1 | 0 | inf | 3 |
| 2 | 1 | 1 | inf | 3 |
| 2 | 1 | 2 | inf | 3 |
| 2 | 1 | 3 | inf | 3 |
| 2 | 1 | 4 | inf | 3 |
| 2 | 1 | 5 | inf | 3 |
| 3 | 1 | 1 | inf | 5 |
| 3 | 1 | 2 | inf | 5 |
| 3 | 1 | 3 | inf | 5 |
| 3 | 1 | 4 | inf | 5 |
| 3 | 1 | 5 | inf | 5 |
| 4 | 1 | 2 | inf | 7 |
| 4 | 1 | 3 | inf | 7 |
| 4 | 1 | 4 | inf | 7 |
| 4 | 1 | 5 | inf | 7 |
| 4 | 2 | 0 | inf | 9 |
| 5 | 1 | 3 | inf | 9 |
| 5 | 1 | 4 | inf | 9 |
| 5 | 1 | 5 | inf | 9 |
| 5 | 2 | 1 | inf | 9 |
| 6 | 1 | 4 | inf | 11 |
| 6 | 1 | 5 | inf | 11 |
| 6 | 2 | 1 | inf | 13 |
| 6 | 2 | 2 | inf | 11 |
| 7 | 1 | 5 | inf | 13 |
| 7 | 2 | 2 | inf | 13 |
| 7 | 2 | 3 | inf | 13 |
| 7 | 3 | 0 | inf | 19 |
| 8 | 2 | 2 | inf | 17 |
| 8 | 2 | 3 | inf | 15 |
| 8 | 2 | 4 | inf | 15 |
| 8 | 3 | 0 | inf | 25 |
| 9 | 2 | 3 | inf | 17 |
| 9 | 2 | 4 | inf | 17 |
| 9 | 2 | 5 | inf | 17 |
| 9 | 3 | 1 | inf | 21 |
| 10 | 2 | 3 | inf | 21 |
| 10 | 2 | 4 | inf | 19 |
| 10 | 2 | 5 | inf | 19 |
| 10 | 3 | 1 | inf | 25 |
| 10 | 3 | 2 | 21 | 19 |
| 11 | 2 | 4 | inf | 21 |
| 11 | 2 | 5 | inf | 21 |
| 11 | 3 | 1 | inf | 29 |
| 11 | 3 | 2 | inf | 23 |
| 12 | 2 | 4 | inf | 25 |
| 12 | 2 | 5 | inf | 23 |
| 12 | 3 | 1 | inf | 35 |
| 12 | 3 | 2 | inf | 27 |
| 12 | 3 | 3 | 25 | 23 |
| 13 | 2 | 5 | inf | 25 |
| 13 | 3 | 2 | inf | 31 |
| 13 | 3 | 3 | inf | 25 |
| 13 | 4 | 0 | inf | 45 |
| 14 | 2 | 5 | inf | 29 |
| 14 | 3 | 2 | inf | 35 |
| 14 | 3 | 3 | inf | 29 |
| 14 | 3 | 4 | 29 | 27 |
| 14 | 4 | 0 | inf | 53 |
| 15 | 3 | 2 | inf | 39 |
| 15 | 3 | 3 | inf | 33 |
| 15 | 3 | 4 | inf | 29 |
| 15 | 4 | 0 | inf | 61 |
| 16 | 3 | 2 | inf | 45 |
| 16 | 3 | 3 | inf | 37 |
| 16 | 3 | 4 | inf | 31 |
| 16 | 3 | 5 | 33 | 31 |
| 16 | 4 | 0 | inf | 71 |
| 17 | 3 | 3 | inf | 41 |
| 17 | 3 | 4 | inf | 35 |
| 17 | 3 | 5 | inf | 33 |
| 17 | 4 | 1 | inf | 49 |
| 17 | 4 | 3 | 35 | 33 |
| 18 | 3 | 3 | inf | 45 |
| 18 | 3 | 4 | inf | 39 |
| 18 | 3 | 5 | inf | 35 |
| 18 | 4 | 1 | inf | 53 |
| 18 | 4 | 3 | 39 | 37 |
| 19 | 3 | 3 | inf | 49 |
| 19 | 3 | 4 | inf | 43 |
| 19 | 3 | 5 | inf | 37 |
| 19 | 4 | 1 | inf | 59 |
| 19 | 4 | 3 | 43 | 41 |
| 20 | 3 | 3 | inf | 55 |
| 20 | 3 | 4 | inf | 47 |
| 20 | 3 | 5 | inf | 41 |
| 20 | 4 | 1 | inf | 65 |
| 20 | 4 | 2 | 55 | 53 |
| 20 | 4 | 3 | 47 | 45 |
| 20 | 4 | 4 | 41 | 39 |
| 21 | 3 | 4 | inf | 51 |
| 21 | 3 | 5 | inf | 45 |
| 21 | 4 | 1 | inf | 71 |
| 21 | 4 | 2 | inf | 57 |
| 21 | 4 | 3 | 51 | 49 |
| 21 | 4 | 4 | 45 | 41 |
| 22 | 3 | 4 | inf | 55 |
| 22 | 3 | 5 | inf | 49 |
| 22 | 4 | 1 | inf | 79 |
| 22 | 4 | 2 | inf | 61 |
| 22 | 4 | 3 | 55 | 53 |
| 22 | 4 | 4 | 49 | 45 |
| 23 | 3 | 4 | inf | 59 |
| 23 | 3 | 5 | inf | 53 |
| 23 | 4 | 1 | inf | 87 |
| 23 | 4 | 2 | inf | 65 |
| 23 | 4 | 3 | 59 | 57 |
| 23 | 4 | 4 | 53 | 49 |
| 23 | 4 | 5 | 47 | 45 |
| 24 | 3 | 4 | inf | 65 |
| 24 | 3 | 5 | inf | 57 |
| 24 | 4 | 1 | inf | 97 |
| 24 | 4 | 2 | inf | 69 |
| 24 | 4 | 3 | 65 | 61 |
| 24 | 4 | 4 | 57 | 53 |
| 24 | 4 | 5 | 51 | 47 |
| 25 | 4 | 4 | 61 | 57 |
| 25 | 4 | 5 | 55 | 49 |
| 26 | 4 | 4 | 65 | 61 |
| 26 | 4 | 5 | 59 | 53 |
| 26 | 5 | 4 | 53 | 51 |
| 27 | 4 | 4 | 69 | 65 |
| 27 | 4 | 5 | 63 | 57 |
| 27 | 5 | 4 | 57 | 55 |
| 28 | 4 | 4 | 75 | 69 |
| 28 | 4 | 5 | 67 | 61 |
| 28 | 5 | 4 | 61 | 59 |
| 29 | 4 | 5 | 71 | 65 |
| 29 | 5 | 4 | 65 | 63 |
| 30 | 4 | 5 | 75 | 69 |
| 30 | 5 | 1 | 105 | 103 |
| 30 | 5 | 4 | 69 | 67 |
| 30 | 5 | 5 | 61 | 59 |
| 31 | 4 | 5 | 79 | 73 |
| 31 | 5 | 1 | 113 | 109 |
| 31 | 5 | 4 | 73 | 71 |
| 31 | 5 | 5 | 65 | 61 |
| 32 | 4 | 5 | 85 | 77 |
| 32 | 5 | 1 | 123 | 115 |
| 32 | 5 | 4 | 77 | 75 |
| 32 | 5 | 5 | 69 | 65 |
| 33 | 5 | 4 | 81 | 79 |
| 33 | 5 | 5 | 73 | 69 |
| 34 | 5 | 2 | 105 | 103 |
| 34 | 5 | 4 | 85 | 83 |
| 34 | 5 | 5 | 77 | 73 |
| 35 | 5 | 2 | 111 | 107 |
| 35 | 5 | 4 | 89 | 87 |
| 35 | 5 | 5 | 81 | 77 |
| 36 | 5 | 2 | 117 | 111 |
| 36 | 5 | 4 | 93 | 91 |
| 36 | 5 | 5 | 85 | 81 |
| 37 | 5 | 2 | 123 | 115 |
| 37 | 5 | 4 | 97 | 95 |
| 37 | 5 | 5 | 89 | 85 |
| 38 | 5 | 2 | 131 | 119 |
| 38 | 5 | 4 | 101 | 99 |
| 38 | 5 | 5 | 93 | 89 |
| 39 | 5 | 2 | 139 | 125 |
| 39 | 5 | 4 | 105 | 103 |
| 39 | 5 | 5 | 97 | 93 |
| 40 | 5 | 2 | 149 | 131 |
| 40 | 5 | 3 | 119 | 117 |
| 40 | 5 | 4 | 109 | 107 |
| 40 | 5 | 5 | 101 | 97 |
| 41 | 5 | 3 | 125 | 121 |
| 41 | 5 | 4 | 113 | 111 |
| 41 | 5 | 5 | 105 | 101 |
| 42 | 5 | 3 | 131 | 125 |
| 42 | 5 | 4 | 117 | 115 |
| 42 | 5 | 5 | 109 | 105 |
| 43 | 5 | 3 | 137 | 129 |
| 43 | 5 | 4 | 121 | 119 |
| 43 | 5 | 5 | 113 | 109 |
| 44 | 5 | 3 | 143 | 133 |
| 44 | 5 | 4 | 125 | 123 |
| 44 | 5 | 5 | 117 | 113 |
| 45 | 5 | 3 | 149 | 137 |
| 45 | 5 | 4 | 129 | 127 |
| 45 | 5 | 5 | 121 | 117 |
| 46 | 5 | 3 | 157 | 141 |
| 46 | 5 | 4 | 133 | 131 |
| 46 | 5 | 5 | 125 | 121 |
| 47 | 5 | 3 | 165 | 145 |
| 47 | 5 | 4 | 139 | 135 |
| 47 | 5 | 5 | 129 | 125 |
| 48 | 5 | 3 | 175 | 149 |
| 48 | 5 | 4 | 145 | 139 |
| 48 | 5 | 5 | 133 | 129 |
| 49 | 5 | 4 | 151 | 143 |
| 49 | 5 | 5 | 137 | 133 |
| 50 | 5 | 4 | 157 | 147 |
| 50 | 5 | 5 | 141 | 137 |
| 51 | 5 | 4 | 163 | 151 |
| 51 | 5 | 5 | 145 | 141 |
| 52 | 5 | 4 | 169 | 155 |
| 52 | 5 | 5 | 149 | 145 |
| 53 | 5 | 4 | 175 | 159 |
| 53 | 5 | 5 | 153 | 149 |
| 54 | 5 | 4 | 183 | 163 |
| 54 | 5 | 5 | 159 | 153 |
| 55 | 5 | 4 | 191 | 167 |
| 55 | 5 | 5 | 165 | 157 |
| 56 | 5 | 4 | 201 | 171 |
| 56 | 5 | 5 | 171 | 161 |
| 57 | 5 | 5 | 177 | 165 |
| 58 | 5 | 5 | 183 | 169 |
| 59 | 5 | 5 | 189 | 173 |
| 60 | 5 | 5 | 195 | 177 |
| 61 | 5 | 5 | 201 | 181 |
| 62 | 5 | 5 | 209 | 185 |
| 63 | 5 | 5 | 217 | 189 |
| 64 | 5 | 5 | 227 | 193 |

So "one erasure is worth at least one pebble" is true exactly in the regime where p pebbles suffice reversibly
(n ≤ 2^(p−1)); it is strict there whenever the pebble side is above the floor; it is false beyond the reach of p pebbles.

## 5. Where an erasure starts to help; non-monotonicity   (`drops.md`)

The first n with M*(n,p,e+1) < M*(n,p,e) is **n = (p−1)(e+1)+2** for every p ≤ 8, e ≤ 5 in range – the first n
whose saturation threshold e*(n,p) exceeds e – and not 2^(p−1)+1 (which is the first n that p pebbles cannot reach
reversibly).  Non-monotonicity of n ↦ M*(n,p_min(n),0): 16 → 17 drops 71 → 57 (p_min 5 → 6), 32 → 33 drops
193 → 153 (6 → 7), 8 → 9: 25 → 25, 4 → 5: 9 → 11; the same jump happens for every e at n = 2^k+1 (drops.md table).

## 6. Witnesses   (`witness_p{p}_e{e}.txt`, index `witness_index.md`)

One plan per (p,e), p = 2..8, e = 0..6, at n = reach(p,e), one move per line (`place i` / `remove i` / `ERASE i`) with
the configuration after each move; all re-verified by the independent checker `pebble.check_plan`.  BFS-optimal for
p ≤ 5 (all e), p = 6 (e ≤ 3), p = 7 (e = 0); for p = 6, e = 4..6 the block construction has length = M* (so optimal);
for p = 7, e ≥ 1 length = 531 + 194e (conjecturally optimal by the identity above); for p = 8 the base plan is the
Bennett 3× composition (1593 moves, not optimal).  τ-structure: in every BFS-optimal witness the erasures sit at
2^(p−1) + i·2^(p−2) (i = 0..e−1) in increasing order, which are exactly the τ-ascents (i with τ(i) > τ(i−1)) of the
plan; the plan climbs by one 2^(p−2)-block after each erasure and never retreats below the stepping stone.

## 7. Timing

Dense BFS (n ≤ 24, p ≤ 8, e ≤ 6): 35 s.  Exhaustive BFS p=5 (N=65): < 1 s, 1.9M states; p=6 (N=129): 79 s, 292M
states (7 × 875 MB bitsets); optimal-witness runs p=6 (N=64/80): 6 s / 14 s; p=7 e=0 (N=64): 50 s, 173M states.
Normal-form search (4 threads): p=6 (nmax 129): 13 s, 120M configurations, 8.6M normal forms; p=7: e ≤ 2 from the
nmax-257 run (391 s, 4.1·10^9 configurations, OOM-killed while storing the level-3 normal forms), e=3 from the nmax-161
run (277 s), e=4 from the nmax-193 run (645 s, 8.6·10^9 configurations, 185M normal forms, 6 GB).  p=7 e=5,6 and all
of p=8 were not attempted (memory / time); those cells hold only the constructive lower bound (e+2)·2^(p−2).
Machine: 4 cores, 15 GB.

## 8. Surprises / remarks

- The inequality "erasure ≥ pebble" fails as soon as n > 2^(p−1); the note's example n=16, p=5 sits exactly at the
  boundary n = 2^(p−1).
- The reachable state space is tiny compared with all ≤p-pebble configurations (p=6, N=129: 2.9·10^8 of 7·10^9·7),
  and the reversible components are classified by a simple greedy normal form – this is what makes p=7 exact.
- The optimal plans at the reach are exactly the Theorem B1 construction with optimal sub-plans; M*(2^(p−1),p,0) =
  3, 9, 25, 71, 193, 531 (p = 2..7).
- reach(p,e+1)−reach(p,e) = 2^(p−2) = half of reach(p,0): an erasure buys half of what the last pebble bought.
