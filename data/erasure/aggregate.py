#!/usr/bin/env python3
"""Aggregate raw BFS outputs into the tables: reach.csv/md, mstar_ext.csv, witnesses, checks."""
import os, re, csv, glob, math, sys
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pebble

HERE = os.path.dirname(os.path.abspath(__file__))
RAW = os.path.join(HERE, 'raw')
INF = float('inf')

def parse_bitset_run(path):
    txt = open(path).read().split('\n')
    m = re.match(r'# N=(\d+) p=(\d+) E=(\d+) states=(\d+) depth=(\d+) seconds=(\d+)', txt[0])
    N, p, E, states, depth, secs = map(int, m.groups())
    first = {}
    witnesses = {}
    i = 0
    while i < len(txt):
        l = txt[i]
        if re.match(r'^\d+,\d+,\d+$', l):
            n, eu, d = map(int, l.split(',')); first[(n, eu)] = d
        elif l.startswith('witness '):
            mm = re.match(r'witness e=(\d+) n=(\d+) eu=(\d+) moves=(\d+)', l)
            e, n, eu, mv = map(int, mm.groups())
            moves = []
            i += 1
            while txt[i] != 'end':
                kind, x = txt[i].split(); moves.append((kind, int(x))); i += 1
            witnesses[e] = (n, eu, mv, moves)
        i += 1
    return dict(N=N, p=p, E=E, states=states, depth=depth, secs=secs, first=first, witnesses=witnesses, path=path)

def mstar_from_first(first, N, E):
    M = {}
    for n in range(1, N + 1):
        best = INF
        for e in range(E + 1):
            best = min(best, first.get((n, e), INF)); M[(n, e)] = best
    return M

def load_runs():
    runs = []
    for f in sorted(glob.glob(os.path.join(RAW, 'reach_N*_p*_E*.txt'))):
        try:
            runs.append(parse_bitset_run(f))
        except Exception as ex:
            print('skip', f, ex)
    return runs

def parse_nfsearch(path):
    res = {}
    meta = None
    for l in open(path):
        m = re.match(r'# nfsearch(?:_omp)? p=(\d+) E=(\d+) nmax=(\d+)', l)
        if m: meta = tuple(map(int, m.groups()))
        m = re.match(r'e=(\d+) reach=(\d+) conj=(\d+) (\S+) new_normal_forms=(\d+) configs_this_level=(\d+) configs_total=(\d+) seconds=(\d+)', l)
        if m:
            e, r, conj, status, nnf, cl, ct, sec = m.groups()
            res[int(e)] = dict(reach=int(r), conj=int(conj), proved=status.startswith('PROVED'), nnf=int(nnf), cfg=int(ct), secs=int(sec))
        m = re.match(r'complete e=(\d+) reach=(\d+) conj=(\d+) (\S+) normal_forms_at_level=(\w+) seconds=(\d+)', l)
        if m:  # N_e complete after processing level e-1
            e, r, conj, status, nnf, sec = m.groups()
            if int(e) not in res:
                res[int(e)] = dict(reach=int(r), conj=int(conj), proved=status.startswith('PROVED'), nnf=(int(nnf) if nnf.isdigit() else -1), cfg=res.get(int(e) - 1, {}).get('cfg', 0), secs=int(sec))
    return meta, res

def main():
    runs = load_runs()
    # ---------------- reach table ----------------
    reach = {}   # (p,e) -> (value, proved, method, states/configs, secs, Mstar_at_reach)
    for r in runs:
        N, p, E = r['N'], r['p'], r['E']
        M = mstar_from_first(r['first'], N, E)
        for e in range(E + 1):
            ns = [n for n in range(1, N + 1) if M[(n, e)] < INF]
            v = max(ns)
            proved = v < N
            key = (p, e)
            cand = (v, proved, f"exhaustive BFS N={N}", r['states'], r['secs'], M[(v, e)])
            if key not in reach or (proved and not reach[key][1]) or (proved == reach[key][1] and N > int(reach[key][2].split('=')[1])):
                reach[key] = cand
    nfres = {}
    for f in sorted(glob.glob(os.path.join(RAW, 'nfsearch_p*_E*_n*.txt'))):
        meta, res = parse_nfsearch(f)
        if not meta: continue
        p, E, nmax = meta
        for e, d in res.items():
            key = (p, e)
            if key not in reach or not reach[key][1]:
                reach[key] = (d['reach'], d['proved'], f"normal-form search nmax={nmax}", d['cfg'], d['secs'], None)
            nfres[key] = d
    pmax = max(p for p, e in reach)
    emax = max(e for p, e in reach)
    with open(os.path.join(HERE, 'reach.csv'), 'w', newline='') as f:
        w = csv.writer(f); w.writerow(['p', 'e', 'reach', 'conjecture_(e+2)2^(p-2)', 'proved', 'method', 'states_or_configs', 'seconds', 'Mstar_at_reach'])
        for p in range(2, pmax + 1):
            for e in range(emax + 1):
                if (p, e) in reach:
                    v, pr, meth, st, sec, ms = reach[(p, e)]
                    w.writerow([p, e, v, (e + 2) * 2 ** (p - 2), 'yes' if pr else 'lower bound only', meth, st, sec, '' if ms is None else ms])
    # formula fit
    cands = {
        '(e+2)*2^(p-2)': lambda p, e: (e + 2) * 2 ** (p - 2),
        '2^p-1+e*2^(p-2)': lambda p, e: 2 ** p - 1 + e * 2 ** (p - 2),
        '2^(p-1)+e*2^(p-2)': lambda p, e: 2 ** (p - 1) + e * 2 ** (p - 2),
        '(e+1)*2^(p-2) (LTV lemma 1)': lambda p, e: (e + 1) * 2 ** (p - 2),
        '2^(p-1)*(1+e/2)': lambda p, e: 2 ** (p - 1) * (1 + e / 2),
    }
    fit = {}
    for name, fn in cands.items():
        bad = [(p, e, v) for (p, e), (v, pr, *_) in reach.items() if pr and fn(p, e) != v]
        fit[name] = bad
    with open(os.path.join(HERE, 'reach.md'), 'w') as f:
        f.write("# reach(p,e): largest n admitting a clean plan with peak p and at most e erasures\n\n")
        f.write("Conjecture B2 of the note: reach(p,e) = (e+2)·2^(p−2).  'proved' = the chain of length reach+1 was exhausted "
                "(exhaustive BFS over all configs with ≤ p pebbles, or the exact normal-form search).  Entries marked * are only lower bounds (search space truncated).\n\n")
        f.write("| p \\ e | " + " | ".join(str(e) for e in range(emax + 1)) + " |\n|---|" + "---|" * (emax + 1) + "\n")
        for p in range(2, pmax + 1):
            row = []
            for e in range(emax + 1):
                if (p, e) in reach:
                    v, pr, *_ = reach[(p, e)]
                    row.append(f"{v}{'' if pr else '*'}")
                else:
                    row.append('')
            f.write(f"| {p} | " + " | ".join(row) + " |\n")
        f.write("\n## Method per row\n\n")
        for p in range(2, pmax + 1):
            meths = sorted(set((reach[(p, e)][2], reach[(p, e)][1]) for e in range(emax + 1) if (p, e) in reach))
            f.write(f"- p={p}: " + "; ".join(f"{m} ({'proved' if pr else 'lower bound'})" for m, pr in meths) + "\n")
        f.write("\n## Candidate closed forms vs all proved values\n\n")
        for name, bad in fit.items():
            f.write(f"- `{name}`: {'FITS ALL' if not bad else f'{len(bad)} mismatches, e.g. {bad[:3]}'}\n")
        f.write("\n## M*(reach(p,e), p, e) (optimal move count at the reach)\n\n")
        f.write("| p \\ e | " + " | ".join(str(e) for e in range(emax + 1)) + " |\n|---|" + "---|" * (emax + 1) + "\n")
        for p in range(2, pmax + 1):
            row = []
            for e in range(emax + 1):
                ms = reach.get((p, e), (None,) * 6)[5]
                row.append('' if ms is None else str(ms))
            f.write(f"| {p} | " + " | ".join(row) + " |\n")
    print("reach table:")
    for p in range(2, pmax + 1):
        print(f"  p={p}:", [reach.get((p, e), ('-',))[0] for e in range(emax + 1)], "proved:", [reach.get((p, e), (None, None))[1] for e in range(emax + 1)])
    print("fits:", {k: len(v) for k, v in fit.items()})

    # ---------------- extended mstar from bitset runs ----------------
    ext = {}
    for r in runs:
        N, p, E = r['N'], r['p'], r['E']
        M = mstar_from_first(r['first'], N, E)
        for (n, e), v in M.items():
            if v < INF:
                ext[(n, p, e)] = v
    # dense table
    dense = {}
    with open(os.path.join(HERE, 'mstar.csv')) as f:
        for row in csv.DictReader(f):
            dense[(int(row['n']), int(row['p']), int(row['e']))] = int(row['Mstar']) if row['Mstar'] else INF
    # consistency between dense and bitset runs
    incons = [(k, dense[k], ext[k]) for k in ext if k in dense and dense[k] != ext[k]]
    print("dense/bitset inconsistencies:", len(incons), incons[:5])
    allM = dict(dense)
    for k, v in ext.items():
        allM.setdefault(k, v)
    with open(os.path.join(HERE, 'mstar_ext.csv'), 'w', newline='') as f:
        w = csv.writer(f); w.writerow(['n', 'p', 'e', 'Mstar'])
        for (n, p, e) in sorted(ext):
            w.writerow([n, p, e, ext[(n, p, e)]])

    # ---------------- inequality M*(n,p,e+1) <= M*(n,p+1,e) ----------------
    viol, eq, gaps = [], [], []
    for (n, p, e), v in allM.items():
        k2 = (n, p + 1, e - 1)
        if e >= 1 and k2 in allM:
            a, b = v, allM[k2]  # a = M*(n,p,e) (one more erasure), b = M*(n,p+1,e-1) (one more pebble)
            if a == INF and b == INF: continue
            if a > b: viol.append((n, p, e - 1, a, b))
            elif a == b: eq.append((n, p, e - 1, a))
            else: gaps.append((n, p, e - 1, a, b))
    print(f"inequality M*(n,p,e+1) <= M*(n,p+1,e): {len(viol)} violations, {len(eq)} equalities, {len(gaps)} strict")
    with open(os.path.join(HERE, 'inequality.md'), 'w') as f:
        f.write("# Check of M*(n,p,e+1) ≤ M*(n,p+1,e)\n\n")
        f.write(f"Checked over every (n,p,e) where both sides are defined (dense table n ≤ 24, p ≤ 8, e ≤ 6, plus the exhaustive runs up to n = 129 for p ≤ 6).\n\n")
        f.write(f"- comparisons: {len(viol)+len(eq)+len(gaps)}\n- violations (erasure worse than a pebble): **{len(viol)}**\n- equalities: {len(eq)}\n- strict (erasure strictly better): {len(gaps)}\n\n")
        small = [(n, p, e, a, b) for (n, p, e, a, b) in viol if n <= 2 ** (p - 1)]
        holds_small = [t for t in eq + [(n, p, e, a) for (n, p, e, a, b) in gaps] if t[0] <= 2 ** (t[1] - 1)]
        eq_small_floor = [t for t in eq if t[0] <= 2 ** (t[1] - 1) and t[3] == 2 * t[0] - 1]
        eq_small = [t for t in eq if t[0] <= 2 ** (t[1] - 1)]
        strict_small = [t for t in gaps if t[0] <= 2 ** (t[1] - 1)]
        f.write("## Characterisation\n\n")
        f.write(f"- For n ≤ 2^(p−1) = reach(p,0) the inequality HOLDS in all {len(holds_small)} comparisons ({len(small)} violations). "
                f"{len(strict_small)} are strict; the {len(eq_small)} ties are all at the floor 2n−1 ({len(eq_small_floor)} of {len(eq_small)}), "
                "so for n ≤ 2^(p−1): M*(n,p,e+1) < M*(n,p+1,e) ⇔ M*(n,p+1,e) > 2n−1 ⇔ e < ⌈(n−1)/p⌉−1.\n")
        f.write(f"- For n > 2^(p−1) (n not reversibly reachable with p pebbles) it FAILS: {len(viol)} violations, of which {len([v for v in viol if v[3] != INF])} have both sides finite "
                f"(smallest: {sorted([v for v in viol if v[3] != INF])[:3]}) and {len([v for v in viol if v[3] == INF])} have M*(n,p,e+1) = ∞ (one pebble reaches n, one erasure does not: "
                "reach(p,e+1) = (e+3)2^(p−2) < (2e+4)2^(p−2) = reach(p+1,e)).\n\n")
        if viol:
            f.write("## Violations\n\n| n | p | e | M*(n,p,e+1) | M*(n,p+1,e) |\n|---|---|---|---|---|\n")
            for t in sorted(viol): f.write("| " + " | ".join(map(str, t)) + " |\n")
        f.write("\n## Equalities (n, p, e, value)\n\n")
        eqs = sorted(eq)
        # characterise: floor cases vs others
        floor_eq = [t for t in eqs if t[3] == 2 * t[0] - 1]
        inf_eq = [t for t in eqs if t[3] == INF]
        other = [t for t in eqs if t[3] != 2 * t[0] - 1 and t[3] != INF]
        f.write(f"- both sides at the floor 2n−1: {len(floor_eq)}\n- both sides infinite (n beyond both reaches): {len(inf_eq)}\n- other equalities: {len(other)}\n\n")
        if other:
            f.write("| n | p | e | value |\n|---|---|---|---|\n")
            for t in other: f.write("| " + " | ".join(map(str, t)) + " |\n")
        f.write("\n## Gap M*(n,p+1,e) − M*(n,p,e+1) for strict cases (finite both sides)\n\n")
        fin = [(n, p, e, b - a) for (n, p, e, a, b) in gaps if a != INF and b != INF]
        infb = [(n, p, e, a) for (n, p, e, a, b) in gaps if b == INF]
        f.write(f"- erasure reachable but extra pebble not (M*(n,p+1,e)=∞ while M*(n,p,e+1) finite): {len(infb)} cases (e.g. {sorted(infb)[:5]})\n")
        f.write(f"- finite gaps: {len(fin)}; max gap {max((g for *_, g in fin), default=0)}, mean {sum(g for *_, g in fin)/max(1,len(fin)):.1f}\n\n")
        f.write("| n | p | e | M*(n,p,e+1) | M*(n,p+1,e) | gap |\n|---|---|---|---|---|---|\n")
        for (n, p, e, a, b) in sorted(gaps):
            if a != INF and b != INF and n <= 24:
                f.write(f"| {n} | {p} | {e} | {a} | {b} | {b-a} |\n")
    # ---------------- Theorem A check ----------------
    badA = []
    for (n, p, e), v in allM.items():
        if p < 2 or v == INF: continue
        estar = math.ceil((n - 1) / (p - 1)) - 1
        if (v == 2 * n - 1) != (e >= estar):
            badA.append((n, p, e, v, estar))
    print("Theorem A violations:", len(badA), badA[:5])
    # ---------------- drop points and non-monotonicity ----------------
    lines = ["# Where does an erasure start to help?  Non-monotonicity in n\n"]
    lines.append("## First n at which M*(n,p,e+1) < M*(n,p,e)\n")
    lines.append("| p | e | first n with M*(n,p,e+1) < M*(n,p,e) | 2^(p−1)+1 (first n unreachable with e=0) | (p−1)(e+1)+2 (first n with e*(n,p) > e) |")
    lines.append("|---|---|---|---|---|")
    drops = {}
    for p in range(2, 9):
        for e in range(0, 6):
            ns = [n for n in range(1, 130) if (n, p, e) in allM and (n, p, e + 1) in allM and allM[(n, p, e + 1)] < allM[(n, p, e)]]
            first_n = min(ns) if ns else None
            drops[(p, e)] = first_n
            lines.append(f"| {p} | {e} | {first_n} | {2**(p-1)+1} | {(p-1)*(e+1)+2} |")
    lines.append("\nObserved: the first strict drop is at n = (p−1)(e+1)+2, exactly the smallest n whose saturation threshold e*(n,p)=⌈(n−1)/(p−1)⌉−1 exceeds e "
                 "(for n ≤ (p−1)(e+1)+1 both budgets already sit at the floor 2n−1).  The value 2^(p−1)+1 is instead the first n that is *unreachable* with e=0.\n")
    lines.append("\n## p_min(n) = least p with reach(p,0) = 2^(p−1) ≥ n, and M*(n, p_min(n), e)\n")
    lines.append("| n | p_min | e=0 | e=1 | e=2 | e=3 | e=4 | floor 2n−1 |")
    lines.append("|---|---|---|---|---|---|---|---|")
    seq = {}
    for n in range(1, 65):
        pm = 1
        while 2 ** (pm - 1) < n: pm += 1
        vals = [allM.get((n, pm, e), None) for e in range(5)]
        seq[n] = (pm, vals)
        if all(v is not None for v in vals):
            lines.append(f"| {n} | {pm} | " + " | ".join(str(v) for v in vals) + f" | {2*n-1} |")
    lines.append("\nNon-monotone steps of n ↦ M*(n,p_min(n),0) (value decreases although n increases):\n")
    prev = None
    for n in range(1, 65):
        pm, vals = seq[n]
        if vals[0] is None: continue
        if prev is not None and vals[0] < prev[1]:
            lines.append(f"- n={prev[0]} (p_min={seq[prev[0]][0]}): {prev[1]}  →  n={n} (p_min={pm}): {vals[0]}")
        prev = (n, vals[0])
    lines.append("\nWith erasures the same jumps occur at n = 2^k+1 (e=1,2,...): see the table.\n")
    with open(os.path.join(HERE, 'drops.md'), 'w') as f:
        f.write("\n".join(lines) + "\n")
    print("drop points (p,e)->n:", {k: v for k, v in drops.items() if v})

    # ---------------- witnesses from -w runs ----------------
    wit_written = {}
    for r in runs:
        for e, (n, eu, mv, moves) in r['witnesses'].items():
            p = r['p']
            if reach.get((p, e), (None,))[0] != n:
                continue  # witness for a truncated n, skip
            ok, msg = pebble.check_plan(moves, n, p, e)
            assert ok, (p, e, msg)
            # prefer optimal: mv == M*
            if (p, e) in wit_written and wit_written[(p, e)] <= mv: continue
            write_witness(p, e, n, moves, f"optimal (BFS depth = M*({n},{p},{e}) = {mv}); source {os.path.basename(r.get('path',''))}")
            wit_written[(p, e)] = mv
    print("witnesses written from BFS:", sorted(wit_written))
    compose_witnesses(runs, reach, allM, wit_written)
    return reach, allM, wit_written

def shift(moves, b):
    return [(k, i + b) for k, i in moves]

def reverse_plan(moves):
    out = []
    for k, i in reversed(moves):
        assert k != 'ERASE'
        out.append(('remove' if k == 'place' else 'place', i))
    return out

def compose_witnesses(runs, reach, allM, wit_written):
    """Block construction of Theorem B1 with optimal sub-plans: base = optimal clean plan for 2^(p-1) with p pebbles,
    then e times: from stepping stone b run the optimal clean plan for 2^(p-2) with p-1 pebbles shifted by b, ERASE b."""
    base = {}  # p -> optimal e=0 plan for n = 2^(p-1)
    for r in runs:
        if 0 in r['witnesses']:
            n, eu, mv, moves = r['witnesses'][0]
            if n == 2 ** (r['p'] - 1):
                base[r['p']] = moves
    # p=8 base: Bennett composition of the optimal 7-pebble plan (not optimal)
    if 7 in base and 8 not in base:
        b7 = base[7]
        base[8] = b7 + shift(b7, 64) + reverse_plan(b7)
        ok, msg = pebble.check_plan(base[8], 128, 8, 0); assert ok, msg
    rows = []
    for p in sorted(base):
        blk = base.get(p - 1)
        if blk is None: continue
        for e in range(0, 7):
            n = (e + 2) * 2 ** (p - 2)
            moves = list(base[p])
            for i in range(e):
                b = 2 ** (p - 1) + i * 2 ** (p - 2)
                moves += shift(blk, b) + [('ERASE', b)]
            ok, msg = pebble.check_plan(moves, n, p, e); assert ok, (p, e, msg)
            ms = allM.get((n, p, e), None)
            if ms is None and (p, e) in reach: ms = reach[(p, e)][5]
            status = ('optimal (= M*)' if ms == len(moves) else f'NOT optimal (M* = {ms})') if ms is not None else \
                     ('optimal (base plan is the BFS-optimal 7-pebble plan)' if e == 0 and p == 7 else
                      ('length = M*(2^(p-1),p,0) + e*(M*(2^(p-2),p-1,0)+1), the pattern that is optimal for every p <= 6; M* unknown here' if p == 7 else
                       'valid but NOT optimal (8-pebble base plan is the Bennett 3x composition, 3*M*(64,7,0) moves)'))
            rows.append((p, e, n, len(moves), ms, status))
            if (p, e) not in wit_written or wit_written[(p, e)] > len(moves):
                write_witness(p, e, n, moves, f"block construction (Thm B1) with optimal sub-plans; {status}")
                wit_written[(p, e)] = len(moves)
    with open(os.path.join(HERE, 'witness_index.md'), 'w') as f:
        f.write("# Witness plans for n = reach(p,e) = (e+2)·2^(p−2)\n\n")
        f.write("Files `witness_p{p}_e{e}.txt`: one move per line (`place i`, `remove i`, `ERASE i`), with the configuration after each move.  "
                "All plans were re-verified by `pebble.check_plan` (flip rule, peak, erasure count, clean end).\n\n")
        f.write("For p ≤ 5 (all e ≤ 6) and p = 6 (e ≤ 3) the file holds a BFS-optimal plan.  For the remaining cases the file holds the block construction "
                "(base: optimal clean plan to 2^(p−1) with p pebbles; then e blocks: optimal clean plan for 2^(p−2) with p−1 pebbles from the stepping stone b, followed by `ERASE b`).\n\n")
        f.write("| p | e | n | plan length | M*(n,p,e) | status |\n|---|---|---|---|---|---|\n")
        for row in rows:
            f.write("| " + " | ".join('' if x is None else str(x) for x in row) + " |\n")
        f.write("\nObserved identity (all p ≤ 6, e ≤ 6): M*(reach(p,e), p, e) = M*(2^(p−1), p, 0) + e·(M*(2^(p−2), p−1, 0) + 1), "
                "i.e. the block construction with optimal sub-plans is optimal at the reach.  Base values M*(2^(p−1),p,0): "
                + ", ".join(f"p={p}: {allM.get((2**(p-1),p,0))}" for p in range(1, 7)) + f", p=7: {len(base[7]) if 7 in base else '?'}.\n")
        f.write("\nErasure positions in the BFS-optimal witnesses (p ≤ 5) versus the block construction 2^(p−1)+i·2^(p−2):\n\n")
        for r in runs:
            for e, (n, eu, mv, moves) in sorted(r['witnesses'].items()):
                if n != reach.get((r['p'], e), (None,))[0] or r['p'] > 6: continue
                er = [i for k, i in moves if k == 'ERASE']
                f.write(f"- p={r['p']} e={e} n={n}: erasures (in time order) at {er}; construction would use {[2**(r['p']-1)+i*2**(r['p']-2) for i in range(e)]}\n")
    print("composed witnesses:", [(p, e, L, ms) for p, e, n, L, ms, st in rows])

def ascents(moves, n):
    """tau(i) = last removal time of node i (if never removed, None). Ascents: i in [2,n-1] with tau(i) > tau(i-1)."""
    tau = {}
    for t, (kind, i) in enumerate(moves, 1):
        if kind in ('remove', 'ERASE'):
            tau[i] = t
    asc = [i for i in range(2, n) if i in tau and (i - 1) in tau and tau[i] > tau[i - 1]]
    return tau, asc

def write_witness(p, e, n, moves, note):
    er = [i for k, i in moves if k == 'ERASE']
    tau, asc = ascents(moves, n)
    lines = [f"# witness for reach(p={p},e={e}) = {n}: {len(moves)} moves, {len(er)} erasures at nodes {er}; {note}",
             f"# chain 0->1->...->{n} (0 = free entrance), clean plan: empty -> {{{n}}}, peak <= {p}",
             f"# erasure positions (ascending): {sorted(er)}; differences from 2^(p-1): {[x - 2**(p-1) for x in sorted(er)]}",
             f"# tau-ascents (i in [2,n-1] with last removal of i after last removal of i-1): {asc}",
             "# columns: step | move | config after move | #pebbles | erasures used"]
    C = set(); eu = 0; peak = 0
    for t, (kind, i) in enumerate(moves, 1):
        if kind == 'place': C.add(i)
        else:
            C.remove(i)
            if kind == 'ERASE': eu += 1
        peak = max(peak, len(C))
        lines.append(f"{t:5d} | {kind + ' ' + str(i):11s} | {{{','.join(map(str, sorted(C)))}}} | {len(C)} | {eu}")
    lines.append(f"# peak = {peak}, final = {{{n}}}, erasures = {eu}")
    with open(os.path.join(HERE, f"witness_p{p}_e{e}.txt"), 'w') as f:
        f.write("\n".join(lines) + "\n")

if __name__ == '__main__':
    main()
