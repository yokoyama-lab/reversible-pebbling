#!/usr/bin/env python3
"""Erasure-budgeted clean reversible pebbling of a chain (model of rc02_erasure_pebbling.tex).

Chain 0 -> 1 -> ... -> n, node 0 a free entrance (never counted, never pebbled).
Config = bitmask over nodes 1..n (bit i-1 <-> node i).  Node i is *available* iff i == 1
or node i-1 is pebbled.  A reversible move flips the pebble of an available node.  An
*erasure* (irreversible removal) removes the pebble of a NON-available pebbled node
(node 1 is always available, so it never erases).  A clean plan starts at the empty
config and ends at exactly {n}, never having more than p pebbles.

  M*(n,p,e) = min #moves of a clean plan with <= e erasures (inf if none)
  reach(p,e) = max n admitting such a plan.

Projection lemma (used throughout): deleting from a plan all moves on nodes > n keeps it a
legal clean plan for target n with the same or fewer pebbles/erasures/moves.  Hence one BFS
on a chain of length N yields M*(n,p,e) for every n <= N, and {n} unreachable on a chain of
length N >= n proves n > reach(p,e).

Usage: python3 pebble.py --all   (writes every table into this directory)
"""
import sys, os, time, csv, argparse
from array import array

HERE = os.path.dirname(os.path.abspath(__file__))
INF = float('inf')

def popcount(x):
    return bin(x).count('1')

# ----------------------------------------------------------------------------
# Dense BFS (N <= ~26): visited/dist arrays indexed by config*(E+1)+eu.
# Returns dist dict {(n, eu): moves} for goals {n} reached with exactly eu erasures used,
# and optionally the full dist array (for witness extraction).
# ----------------------------------------------------------------------------
def bfs_dense(N, p, E, want_dist_array=False, max_moves=None):
    E1 = E + 1
    size = (1 << N) * E1
    dist = array('H', bytes(2 * size))  # 0 = unvisited; store d+1
    dist[0] = 1
    frontier = [0]  # state index = config*E1 + eu
    mask = (1 << N) - 1
    d = 0
    goals = {}
    pc = popcount
    while frontier:
        d += 1
        if max_moves is not None and d > max_moves:
            break
        nxt = []
        app = nxt.append
        for s in frontier:
            c, eu = divmod(s, E1)
            avail = ((c << 1) | 1) & mask
            k = pc(c)
            # reversible flips
            x = avail
            while x:
                b = x & -x
                x ^= b
                if c & b:
                    nc = c ^ b
                else:
                    if k >= p:
                        continue
                    nc = c | b
                ns = nc * E1 + eu
                if not dist[ns]:
                    dist[ns] = d + 1
                    app(ns)
                    if nc and (nc & (nc - 1)) == 0:
                        goals.setdefault((nc.bit_length(), eu), d)
            # erasures
            if eu < E:
                x = c & ~avail
                while x:
                    b = x & -x
                    x ^= b
                    nc = c ^ b
                    ns = nc * E1 + eu + 1
                    if not dist[ns]:
                        dist[ns] = d + 1
                        app(ns)
                        if nc and (nc & (nc - 1)) == 0:
                            goals.setdefault((nc.bit_length(), eu + 1), d)
        frontier = nxt
    if want_dist_array:
        return goals, dist
    return goals

# ----------------------------------------------------------------------------
# Sparse BFS (large N, small p): dict/set based, states = (config, eu) packed as
# config*(E+1)+eu.  Optionally records layers for witness reconstruction.
# ----------------------------------------------------------------------------
def bfs_sparse(N, p, E, keep_layers=False, verbose=False):
    E1 = E + 1
    mask = (1 << N) - 1
    seen = {0}
    frontier = [0]
    layers = [frontier] if keep_layers else None
    d = 0
    goals = {}
    pc = popcount
    t0 = time.time()
    while frontier:
        d += 1
        nxt = []
        app = nxt.append
        add = seen.add
        for s in frontier:
            c, eu = divmod(s, E1)
            avail = ((c << 1) | 1) & mask
            k = pc(c)
            x = avail
            while x:
                b = x & -x
                x ^= b
                if c & b:
                    nc = c ^ b
                else:
                    if k >= p:
                        continue
                    nc = c | b
                ns = nc * E1 + eu
                if ns not in seen:
                    add(ns); app(ns)
                    if nc and (nc & (nc - 1)) == 0:
                        goals.setdefault((nc.bit_length(), eu), d)
            if eu < E:
                x = c & ~avail
                while x:
                    b = x & -x
                    x ^= b
                    nc = c ^ b
                    ns = nc * E1 + eu + 1
                    if ns not in seen:
                        add(ns); app(ns)
                        if nc and (nc & (nc - 1)) == 0:
                            goals.setdefault((nc.bit_length(), eu + 1), d)
        frontier = nxt
        if keep_layers:
            layers.append(frontier)
        if verbose and d % 20 == 0:
            print(f"  N={N} p={p} E={E} layer {d}: frontier {len(frontier)} seen {len(seen)} t={time.time()-t0:.0f}s", file=sys.stderr, flush=True)
    return goals, seen, layers

def mstar_from_goals(goals, N, E):
    """M*(n,p,e) = min over eu<=e of goals[(n,eu)]."""
    M = {}
    for n in range(1, N + 1):
        best = INF
        for e in range(E + 1):
            v = goals.get((n, e), INF)
            if v < best:
                best = v
            M[(n, e)] = best
    return M

# ----------------------------------------------------------------------------
# Witness extraction: walk back from goal through layers (sparse) or dist array (dense).
# ----------------------------------------------------------------------------
def predecessors(s, N, p, E):
    """All states s' with a legal move s' -> s (reverse of the move generator)."""
    E1 = E + 1
    mask = (1 << N) - 1
    c, eu = divmod(s, E1)
    preds = []
    # reverse of a reversible flip at bit b: predecessor c^b, where b was available in c^b
    # availability of node i in config c' depends on bit i-1 of c'. For place (bit b not in c'):
    # need avail in c' = c^b; for remove (bit b in c'): same.  Availability is decided by
    # the bit below b, which is unchanged by flipping b, so check it in c.
    for i in range(N):
        b = 1 << i
        avail = (i == 0) or (c & (b >> 1))
        if avail:
            pc_ = c ^ b
            if popcount(pc_) <= p:
                preds.append((pc_ * E1 + eu, ('flip', i + 1)))
    # reverse of an erasure: predecessor had bit b set, b not available, eu-1
    if eu > 0:
        for i in range(1, N):
            b = 1 << i
            if not (c & b) and not (c & (b >> 1)):
                pc_ = c | b
                if popcount(pc_) <= p:
                    preds.append((pc_ * E1 + eu - 1, ('erase', i + 1)))
    return preds

def witness_sparse(layers, goal_state, N, p, E):
    d = None
    for idx, L in enumerate(layers):
        if goal_state in L:  # lists; convert lazily
            d = idx; break
    if d is None:
        return None
    layer_sets = [set(L) for L in layers[:d + 1]]
    E1 = E + 1
    path = []
    s = goal_state
    for k in range(d, 0, -1):
        for ps, mv in predecessors(s, N, p, E):
            if ps in layer_sets[k - 1]:
                path.append((mv, s)); s = ps; break
        else:
            raise RuntimeError("witness reconstruction failed")
    path.reverse()
    return path  # list of (move, resulting_state)

def witness_dense(dist, goal_state, N, p, E):
    dgoal = dist[goal_state] - 1
    path = []
    s = goal_state
    for k in range(dgoal, 0, -1):
        for ps, mv in predecessors(s, N, p, E):
            if dist[ps] == k:  # dist stores d+1, so state at depth k-1 has value k
                path.append((mv, s)); s = ps; break
        else:
            raise RuntimeError("witness reconstruction failed (dense)")
    path.reverse()
    return path

def format_witness(path, N, p, E, n, e, header=''):
    E1 = E + 1
    lines = [header] if header else []
    lines.append(f"# chain 0->1->...->{n}, peak p={p}, erasure budget e={e}; {len(path)} moves")
    lines.append("# columns: step | move | config after move (nodes pebbled) | #pebbles | erasures used")
    lines.append("# move 'place i' / 'remove i' are reversible; 'ERASE i' is an irreversible removal (i-1 empty)")
    c = 0
    peak = 0
    for step, (mv, s) in enumerate(path, 1):
        nc, eu = divmod(s, E1)
        kind, i = mv
        if kind == 'flip':
            name = f"place {i}" if (nc >> (i - 1)) & 1 else f"remove {i}"
        else:
            name = f"ERASE {i}"
        nodes = [j + 1 for j in range(N) if (nc >> j) & 1]
        peak = max(peak, len(nodes))
        lines.append(f"{step:4d} | {name:10s} | {{{','.join(map(str,nodes))}}} | {len(nodes)} | {eu}")
        c = nc
    lines.append(f"# peak observed = {peak}; final config = {{{n}}}")
    return "\n".join(lines) + "\n"

def check_plan(moves, n, p, e):
    """Independent verifier: moves = list of ('place'|'remove'|'ERASE', i). Returns (ok, msg)."""
    C = set(); eu = 0; peak = 0
    for t, (kind, i) in enumerate(moves, 1):
        if not (1 <= i <= n):
            return False, f"step {t}: node {i} out of range"
        avail = (i == 1) or ((i - 1) in C)
        if kind == 'place':
            if i in C or not avail:
                return False, f"step {t}: illegal place {i}"
            C.add(i)
        elif kind == 'remove':
            if i not in C or not avail:
                return False, f"step {t}: illegal remove {i}"
            C.remove(i)
        elif kind == 'ERASE':
            if i not in C or avail:
                return False, f"step {t}: ERASE {i} but node available (would be reversible)"
            C.remove(i); eu += 1
        peak = max(peak, len(C))
        if peak > p:
            return False, f"step {t}: peak {peak} > {p}"
    if eu > e:
        return False, f"{eu} erasures > {e}"
    if C != {n}:
        return False, f"final config {sorted(C)} != {{{n}}}"
    return True, f"ok: {len(moves)} moves, peak {peak}, erasures {eu}"

def parse_witness_file(path):
    moves = []
    with open(path) as f:
        for line in f:
            if line.startswith('#') or '|' not in line:
                continue
            parts = [x.strip() for x in line.split('|')]
            kind, i = parts[1].split()
            moves.append((kind, int(i)))
    return moves

# ----------------------------------------------------------------------------
# Tasks
# ----------------------------------------------------------------------------
def task_mstar(N=24, PMAX=8, EMAX=4, out_csv='mstar.csv', out_md='mstar.md', log=print):
    t0 = time.time()
    table = {}  # (n,p,e) -> M*
    for p in range(1, PMAX + 1):
        t1 = time.time()
        goals = bfs_dense(N, p, EMAX)
        M = mstar_from_goals(goals, N, EMAX)
        for (n, e), v in M.items():
            table[(n, p, e)] = v
        log(f"  mstar: p={p} done in {time.time()-t1:.1f}s")
    with open(os.path.join(HERE, out_csv), 'w', newline='') as f:
        w = csv.writer(f); w.writerow(['n', 'p', 'e', 'Mstar'])
        for n in range(1, N + 1):
            for p in range(1, PMAX + 1):
                for e in range(EMAX + 1):
                    v = table[(n, p, e)]
                    w.writerow([n, p, e, '' if v == INF else v])
    with open(os.path.join(HERE, out_md), 'w') as f:
        f.write(f"# M*(n,p,e): minimum moves of a clean plan (chain 0->...->n, peak <= p, <= e erasures)\n\n")
        f.write(f"Computed by exhaustive BFS on a chain of length {N} (projection lemma gives all n <= {N}).  "
                f"'-' = impossible (n > reach(p,e)).  Floor is 2n-1 (Knill).\n\n")
        for e in range(EMAX + 1):
            f.write(f"## e = {e}\n\n| n | 2n-1 | " + " | ".join(f"p={p}" for p in range(1, PMAX + 1)) + " |\n")
            f.write("|---|---|" + "---|" * PMAX + "\n")
            for n in range(1, N + 1):
                row = [str(n), str(2 * n - 1)]
                for p in range(1, PMAX + 1):
                    v = table[(n, p, e)]
                    row.append('-' if v == INF else str(v))
                f.write("| " + " | ".join(row) + " |\n")
            f.write("\n")
    log(f"  mstar table written ({time.time()-t0:.1f}s)")
    return table

def task_reach_bruteforce(cases, out_prefix='reach_bf', log=print, witness=True):
    """cases: list of (p, E, N). BFS sparse on chain N; report for each e the max n with {n} reached.
    A value is *proved* iff it is < N (then N itself was not reached with that budget)."""
    results = {}
    for (p, E, N) in cases:
        t1 = time.time()
        goals, seen, layers = bfs_sparse(N, p, E, keep_layers=witness, verbose=True)
        M = mstar_from_goals(goals, N, E)
        for e in range(E + 1):
            r = max([n for n in range(1, N + 1) if M[(n, e)] < INF], default=0)
            results[(p, e)] = (r, N, M[(r, e)] if r else None, r < N)
            log(f"  reach: p={p} e={e} N={N}: reach={r} ({'PROVED' if r < N else 'not proved, N too small'}) M*={M[(r,e)]}  states={len(seen)} t={time.time()-t1:.0f}s")
            if witness and r:
                # witness at n=r with exactly some eu<=e erasures: pick eu achieving the min
                E1 = E + 1
                best = None
                for eu in range(e + 1):
                    v = goals.get((r, eu), INF)
                    if best is None or v < best[0]:
                        best = (v, eu)
                gs = (1 << (r - 1)) * E1 + best[1]
                path = witness_sparse(layers, gs, N, p, E)
                txt = format_witness(path, N, p, E, r, e,
                                     header=f"# optimal witness for reach(p={p},e={e}) = {r}, M*({r},{p},{e}) = {len(path)}")
                with open(os.path.join(HERE, f"witness_p{p}_e{e}.txt"), 'w') as f:
                    f.write(txt)
    return results

# ----------------------------------------------------------------------------
# Full pipeline (python3 pebble.py --all): compiles the C searches, runs every computation, aggregates.
# ----------------------------------------------------------------------------
def run_all(threads=4, big=True):
    import subprocess, shutil
    os.makedirs(os.path.join(HERE, 'raw'), exist_ok=True)
    def sh(cmd, out=None, err=None, env=None):
        print('  $', cmd, flush=True)
        with open(out, 'w') if out else open(os.devnull, 'w') as fo, open(err, 'w') if err else open(os.devnull, 'w') as fe:
            subprocess.run(cmd, shell=True, cwd=HERE, stdout=fo, stderr=fe, check=True, env=env)
    t0 = time.time()
    print("[1] dense BFS: M*(n,p,e) for n<=24, p<=8, e<=6")
    task_mstar(24, 8, 6)
    print("[2] compile C searches")
    sh("gcc -O2 -o reachbfs reachbfs.c"); sh("gcc -O2 -o nfsearch nfsearch.c"); sh("gcc -O2 -fopenmp -o nfsearch_omp nfsearch_omp.c")
    print("[3] exhaustive reach BFS with optimal witnesses (p<=5, e<=6) and p=6")
    for (N, p, E, w) in [(9, 2, 6, 1), (17, 3, 6, 1), (33, 4, 6, 1), (65, 5, 6, 1), (129, 6, 6, 0), (64, 6, 2, 1), (80, 6, 3, 1), (64, 7, 0, 1)]:
        tag = f"reach_N{N}_p{p}_E{E}" + ("_w" if w else "")
        sh(f"./reachbfs {N} {p} {E}" + (" -w" if w else ""), out=f"raw/{tag}.txt", err=f"raw/{tag}.log")
    if big:
        print("[4] exact normal-form search p=7: e<=2 (nmax 257, ~7 min, ~6 GB), e=3 (nmax 161), e=4 (nmax 193)  -- long")
        env = dict(os.environ, OMP_NUM_THREADS=str(threads))
        sh("./nfsearch_omp 7 3 257", out="raw/nfsearch_p7_E6_n257.txt", env=env)   # proves e<=3 at nmax 257 (level 2 not stored)
        sh("./nfsearch_omp 7 3 161", out="raw/nfsearch_p7_E3_n161.txt", env=env)
        sh("./nfsearch_omp 7 4 193", out="raw/nfsearch_p7_E4_n193.txt", env=env)
    print("[5] aggregate")
    import aggregate; aggregate.main()
    print(f"all done in {time.time()-t0:.0f}s")

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--all', action='store_true')
    ap.add_argument('--mstar', action='store_true')
    ap.add_argument('--N', type=int, default=24)
    ap.add_argument('--pmax', type=int, default=8)
    ap.add_argument('--emax', type=int, default=4)
    ap.add_argument('--small', action='store_true', help='with --all: skip the long p=7/p=8 normal-form searches')
    a = ap.parse_args()
    if a.all:
        run_all(big=not a.small)
    elif a.mstar:
        task_mstar(a.N, a.pmax, a.emax)

