#!/usr/bin/env python3
"""Writes SUMMARY.md from the generated tables (run after aggregate.py)."""
import csv, os, re, glob
HERE = os.path.dirname(os.path.abspath(__file__))
INF = float('inf')
def rd(name): return open(os.path.join(HERE, name)).read()
reach = {}
for r in csv.DictReader(open(os.path.join(HERE, 'reach.csv'))):
    reach[(int(r['p']), int(r['e']))] = (int(r['reach']), r['proved'] == 'yes', r['method'], r['states_or_configs'], r['seconds'], r['Mstar_at_reach'])
M = {}
for f in ('mstar.csv', 'mstar_ext.csv'):
    for r in csv.DictReader(open(os.path.join(HERE, f))):
        M.setdefault((int(r['n']), int(r['p']), int(r['e'])), int(r['Mstar']) if r['Mstar'] else INF)
pmax = max(p for p, e in reach); emax = max(e for p, e in reach)
def reach_table():
    out = ["| p \\ e | " + " | ".join(str(e) for e in range(emax + 1)) + " | method |", "|---|" + "---|" * (emax + 2)]
    for p in range(2, pmax + 1):
        cells = []
        for e in range(emax + 1):
            if (p, e) in reach:
                v, pr, *_ = reach[(p, e)]; cells.append(f"{v}{'' if pr else '*'}")
            else: cells.append('–')
        meths = sorted(set(reach[(p, e)][2] for e in range(emax + 1) if (p, e) in reach))
        out.append(f"| {p} | " + " | ".join(cells) + " | " + "; ".join(meths) + " |")
    return "\n".join(out)
def mstar_block(ns, ps, es):
    out = ["| n | p_min | " + " | ".join(f"e={e}" for e in es) + " | 2n−1 |", "|---|---|" + "---|" * (len(es) + 1)]
    for n in ns:
        p = 1
        while 2 ** (p - 1) < n: p += 1
        vals = [M.get((n, p, e), None) for e in es]
        if all(v is None for v in vals): continue
        out.append(f"| {n} | {p} | " + " | ".join('∞' if v == INF else ('?' if v is None else str(v)) for v in vals) + f" | {2*n-1} |")
    return "\n".join(out)
nf_runs = []
for f in sorted(glob.glob(os.path.join(HERE, 'raw', 'nfsearch_p*_E*_n*.txt'))):
    nf_runs.append(os.path.basename(f) + ":\n```\n" + open(f).read().strip() + "\n```")
bf_runs = []
for f in sorted(glob.glob(os.path.join(HERE, 'raw', 'reach_N*_p*_E*.txt'))):
    bf_runs.append("- " + open(f).readline().strip().lstrip('# '))
proved = sorted((p, e) for (p, e), v in reach.items() if v[1])
lower = sorted((p, e) for (p, e), v in reach.items() if not v[1])
fits_all = all((e + 2) * 2 ** (p - 2) == reach[(p, e)][0] for (p, e) in proved)
txt = f"""# SUMMARY – erasure-budgeted clean reversible pebbling of a chain

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
p and budget e starts from ∅, ends at exactly {{n}}, never has more than p pebbles and uses ≤ e erasures.
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

{reach_table()}

(* = lower bound only.)  **Every proved value equals (e+2)·2^(p−2)** (Conjecture B2 of the note){' – fits all ' + str(len(proved)) + ' proved cells' if fits_all else ' – MISMATCH, see reach.md'}.
Proved range: p ≤ {max(p for p, e in proved)} with e ≤ {emax} for p ≤ 6{', p=7 for e ≤ ' + str(max(e for p, e in proved if p == 7)) if any(p == 7 for p, e in proved) else ''}{', p=8 for e ≤ ' + str(max(e for p, e in proved if p == 8)) if any(p == 8 for p, e in proved) else ''}.
Alternatives tested and rejected: 2^p−1+e·2^(p−2) and (e+1)·2^(p−2) (Li–Tromp–Vitányi lemma 1) fail on every cell with
p ≥ 2 resp. every cell; 2^(p−1)+e·2^(p−2) is the same formula as (e+2)2^(p−2).

Methods.  p ≤ 6: exhaustive layered BFS over all (config with ≤ p pebbles, erasures used) states of the chain of
length reach(p,6)+1 (`reachbfs.c`), which also yields M*(n,p,e) for all n ≤ 129, p ≤ 6, e ≤ 6 (`mstar_ext.csv`):
{chr(10).join(bf_runs)}

p ≥ 7: exact **normal-form search** (`normalform.py` docstring has the proof).  In the reversible game with peak p a
pebble x is *removable* iff its gap to the pebble below (or to node 0) is ≤ 2^(p−k), k = current number of pebbles
(touch x−1 with the free pebbles, remove x, undo).  Removability is preserved when another removable pebble is
removed, so greedy elimination has a unique normal form nf(C) (Newman's lemma), placing a pebble creates a
removable pebble, hence nf is invariant under reversible moves and **two configurations are reversibly connected iff
they have the same normal form**; in particular {{n}} is reachable from ∅ iff n ≤ 2^(p−1).  The search keeps only
normal forms: N₀ = {{∅}}, N_(e+1) = N_e ∪ {{nf(C∖x) : nf(C) ∈ N_e, x erasable in C}}, enumerating each component
without a visited set by canonical reverse elimination (each configuration generated exactly once).  It was validated
configuration-by-configuration against the brute force for p ≤ 5 and by all reach values and state counts for p = 6.
Memory (the table of normal forms) is the limit: the p=7 run storing all levels was OOM-killed (15 GB) while storing the
level-3 normal forms; the reruns process the last level without storing its successors (N_(e+1) is complete once level e
is processed).  p = 8 was not attempted: comp(∅) alone has ~10^11 configurations (~2.5 h on 4 cores), and the level-1
normal forms would not fit in memory; reach(8,e) ≥ (e+2)·64 holds by the verified witnesses.
{chr(10).join(nf_runs)}

Bonus identity at the reach (all p ≤ 6, e ≤ 6; and p=7, e=0): **M*(reach(p,e),p,e) = M*(2^(p−1),p,0) + e·(M*(2^(p−2),p−1,0)+1)**,
i.e. the block construction of Theorem B1 with optimal sub-plans is move-optimal at the reach.  Base values
M*(2^(p−1),p,0) for p = 1..7: {', '.join(str(M.get((2**(p-1), p, 0), '?')) for p in range(1, 8))}.  Increment per erasure block (p=3..7): {', '.join(str(M.get((2**(p-2), p-1, 0), 0) + 1) for p in range(3, 8))}.

## 3. M*(n,p,e)   (`mstar.csv`, `mstar.md`: n ≤ 24, p ≤ 8, e ≤ 6; `mstar_ext.csv`: n ≤ 129, p ≤ 6)

Theorem A of the note, M*(n,p,e) = 2n−1 ⇔ e ≥ e*(n,p) = ⌈(n−1)/(p−1)⌉−1, holds on every finite entry (0 violations).
Extract at the minimal peak p_min(n) (least p with 2^(p−1) ≥ n):

{mstar_block(range(2, 34), None, range(0, 5))}

## 4. Inequality M*(n,p,e+1) ≤ M*(n,p+1,e)   (`inequality.md`)

{rd('inequality.md').split('## Characterisation')[1].split('## Equalities')[0].strip()}

So "one erasure is worth at least one pebble" is true exactly in the regime where p pebbles suffice reversibly
(n ≤ 2^(p−1)); it is strict there whenever the pebble side is above the floor; it is false beyond the reach of p pebbles.

## 5. Where an erasure starts to help; non-monotonicity   (`drops.md`)

The first n with M*(n,p,e+1) < M*(n,p,e) is **n = (p−1)(e+1)+2** for every p ≤ 8, e ≤ 5 in range – the first n
whose saturation threshold e*(n,p) exceeds e – and not 2^(p−1)+1 (which is the first n that p pebbles cannot reach
reversibly).  Non-monotonicity of n ↦ M*(n,p_min(n),0): 16 → 17 drops 71 → 57 (p_min 5 → 6), 32 → 33 drops
{M.get((32,6,0),'?')} → {M.get((33,7,0),'?')} (6 → 7), 8 → 9: {M.get((8,4,0),'?')} → {M.get((9,5,0),'?')}, 4 → 5: {M.get((4,3,0),'?')} → {M.get((5,4,0),'?')}; the same jump happens for every e at n = 2^k+1 (drops.md table).

## 6. Witnesses   (`witness_p{{p}}_e{{e}}.txt`, index `witness_index.md`)

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
"""
open(os.path.join(HERE, 'SUMMARY.md'), 'w').write(txt)
print("SUMMARY.md written", len(txt))
