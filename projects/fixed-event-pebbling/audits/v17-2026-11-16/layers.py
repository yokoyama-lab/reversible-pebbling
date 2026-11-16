"""Exact cost layers of the local factors I and M (finite check, Python only).

Setting of Definition 8.1 (manuscript v16/v17): IDs = event indices of
LocalCertificate.lean, weight +1 placement / -1 removal, initial height 4,
guard = every post-event height in [0,5], cost A(w) = sum of post-event heights,
Q = common precedence of all capacity-legal local words (Q_X^cap).

Checks, per factor:
  (a) LE(Q) ∩ guard == capacity-legal words  (hypothesis of Thm 8.2 / l.377)
  (b) LE(Q) ⊆ capacity-free legal words      (non-capacity conditions held by Q)
  (c) per cost value a: #words, #signatures
  (d) per signature class: LE(closure(Q ∪ σ)) == class (direct upper-bound certificate)
Usage: python3 -I layers.py LocalCertificate.lean OUT.json
"""
import ast, hashlib, json, re, sys
from collections import defaultdict

src_path, out_path = sys.argv[1], sys.argv[2]
src = open(src_path, 'rb').read()
SHA = hashlib.sha256(src).hexdigest()
assert SHA == 'ab087e2a09ad672be9248e409381581905e98fa0635cae3b111a65a1c06fa9cf'
text = src.decode()

def load(name):
    s = text.split('namespace ' + name + '\n')[1]
    ev = [(b == 'true', int(v)) for b, v in
          re.findall(r'⟨(false|true), (\d+)⟩', re.search(r'def events .*? := (.*)', s)[1])]
    arr = lambda k: ast.literal_eval(re.search(r'def ' + k + r' .*? := (.*)', s)[1])
    return ev, arr('initial'), arr('final'), arr('erasures')

def legal_words(ev, init, fin, eras, cap):
    n = len(ev); out = []
    def rec(pre, board, used):
        if len(pre) == n:
            if sorted(board) == sorted(fin): out.append(tuple(pre))
            return
        for i, (pl, v) in enumerate(ev):
            if used >> i & 1: continue
            has_pred = (v == 1) or (v - 1 in board)
            if pl:
                if v in board or not has_pred: continue
                nb = board | {v}
            else:
                if v not in board: continue
                if (not has_pred) != (v in eras): continue   # actual erasure iff designated
                nb = board - {v}
            if cap and len(nb) > 5: continue
            rec(pre + [i], nb, used | 1 << i)
    rec([], frozenset(init), 0)
    return set(out)

def lin_ext(n, before):  # before[b] = bitmask of required predecessors
    out = []
    def rec(pre, used):
        if len(pre) == n: out.append(tuple(pre)); return
        for i in range(n):
            if not used >> i & 1 and before[i] & ~used == 0:
                rec(pre + [i], used | 1 << i)
    rec([], 0)
    return out

def closure(n, rel):
    r = [[False] * n for _ in range(n)]
    for a, b in rel: r[a][b] = True
    for k in range(n):
        for i in range(n):
            if r[i][k]:
                for j in range(n):
                    if r[k][j]: r[i][j] = True
    assert not any(r[i][i] for i in range(n))
    return r

res = {'source_sha256': SHA}
for name in ['I', 'M']:
    ev, init, fin, eras = load(name); n = len(ev)
    w8 = [1 if pl else -1 for pl, _ in ev]
    legal = legal_words(ev, init, fin, eras, True)
    free = legal_words(ev, init, fin, eras, False)
    Q = {(a, b) for a in range(n) for b in range(n)
         if a != b and all(w.index(a) < w.index(b) for w in legal)}
    before = [sum(1 << a for a, b in Q if b == x) for x in range(n)]
    ext = lin_ext(n, before)
    h0 = len(init)
    def heights(w):
        h = h0; hs = []
        for i in w: h += w8[i]; hs.append(h)
        return hs
    guarded = {w for w in ext if all(0 <= h <= 5 for h in heights(w))}
    assert h0 == 4
    pairs = [(x, y) for x in range(n) for y in range(x + 1, n) if w8[x] != w8[y]]
    def sig(w):
        pos = {e: k for k, e in enumerate(w)}
        return tuple(pos[x] < pos[y] for x, y in pairs)
    layers = defaultdict(lambda: defaultdict(list))
    for w in guarded:
        layers[sum(heights(w))][sig(w)].append(w)
    rows = []; all_ok = True
    for a in sorted(layers):
        cls = layers[a]; ok = True
        for s, ws in cls.items():
            rel = set(Q) | {((x, y) if o else (y, x)) for (x, y), o in zip(pairs, s)}
            r = closure(n, rel)
            bef = [sum(1 << i for i in range(n) if r[i][j]) for j in range(n)]
            if set(lin_ext(n, bef)) != set(ws): ok = False
        all_ok &= ok
        rows.append({'cost': a, 'words': sum(len(v) for v in cls.values()),
                     'signatures': len(cls), 'class_sizes': sorted(len(v) for v in cls.values()),
                     'P_sigma_exact': ok})
    # Q edges that fail in some capacity-free legal word (= order coming from capacity)
    cap_edges = sorted((x, y) for x, y in Q if not all(w.index(x) < w.index(y) for w in free))
    # lower-bound certificate: for every pair of signature representatives u,v in a layer,
    # a word z in LE(common order of u and v) with z outside the layer
    def common_ext_outside(u, v, layer):
        pu = {e: k for k, e in enumerate(u)}; pv = {e: k for k, e in enumerate(v)}
        bef2 = [sum(1 << x for x in range(n) if pu[x] < pu[y] and pv[x] < pv[y]) for y in range(n)]
        hit = []
        def rec(pre, used):
            if hit: return
            if len(pre) == n:
                if tuple(pre) not in layer: hit.append(tuple(pre))
                return
            for i in range(n):
                if not used >> i & 1 and bef2[i] & ~used == 0:
                    rec(pre + [i], used | 1 << i)
        rec([], 0)
        return hit[0] if hit else None
    def verify_witness(u, v, z, layer):
        pu = {e: k for k, e in enumerate(u)}; pv = {e: k for k, e in enumerate(v)}; pz = {e: k for k, e in enumerate(z)}
        return (sorted(z) == list(range(n)) and tuple(z) not in layer and
                all(pz[x] < pz[y] for x in range(n) for y in range(n) if pu[x] < pu[y] and pv[x] < pv[y]))
    lb_pairs = 0; lb_ok = True; certs = []
    for row in rows:
        cls = layers[row['cost']]; layer = {w for ws in cls.values() for w in ws}
        reps = [sorted(ws)[0] for _, ws in sorted(cls.items())]
        for i in range(len(reps)):
            for j in range(i + 1, len(reps)):
                z = common_ext_outside(reps[i], reps[j], layer); lb_pairs += 1
                ok = z is not None and verify_witness(reps[i], reps[j], z, layer)
                lb_ok &= ok
                certs.append([row['cost'], list(reps[i]), list(reps[j]), list(z) if z else None])
        row['lower_bound_pairs_ok'] = all(c[3] is not None for c in certs if c[0] == row['cost'])
    res[name + '_lower_bound_certificates'] = certs
    res[name] = {'events': n, 'Q_capacity_origin_edges': len(cap_edges), 'Q_capacity_origin_edge_list': cap_edges,
                 'lower_bound_pairs': lb_pairs, 'lower_bound_all_ok': lb_ok, 'Q_edges_transitive': len(Q), 'LE_Q': len(ext),
                 'capacity_legal': len(legal), 'capacity_free_legal': len(free),
                 'LE_Q_subset_capacity_free': set(ext) <= free,
                 'guarded_LE_Q_equals_legal': guarded == legal,
                 'layers': rows,
                 'total_signatures': sum(r['signatures'] for r in rows),
                 'all_P_sigma_exact': all_ok,
                 'Q': sorted(Q), 'layer_signatures': {r['cost']: r['signatures'] for r in rows}, 'weights': w8,
                 'local_words_sig': None}
    res[name]['_layers_obj'] = layers
# --- k=1: L_1 = F0 I F1 T1 (Theorem 4.4). Cost shift and signature counts of the global layers.
LI = res['I']['_layers_obj']; wI = res['I']['weights']
F0 = [+1, +1, +1, +1, +1, -1]            # P1..P5 R4, from the empty board
F1 = [+1, -1, +1, -1]                    # P_t R_h P_c^2 R_d
T_ev = [+1, -1, -1, -1, -1]              # P_a^2 R_c^2 R_b R_a^2 R_s
T_words = [(0, 1, 2, 3, 4), (1, 0, 2, 3, 4)]
wt = F0 + wI + F1 + T_ev; N = len(wt)
oI, oF1, oT = len(F0), len(F0) + len(wI), len(F0) + len(wI) + len(F1)
gpairs = [(x, y) for x in range(N) for y in range(x + 1, N) if wt[x] != wt[y]]
def hsum(word, h0=0):
    h = h0; s = 0
    for i in word: h += wt[i]; s += h
    return s
tcost = {tw: sum(__import__('itertools').accumulate([4] + [T_ev[i] for i in tw]))- 4 for tw in T_words}
glay = defaultdict(set); shift_ok = True
for a, cls in LI.items():
    for ws in cls.values():
        for w in ws:
            for tw in T_words:
                g = list(range(len(F0))) + [oI + i for i in w] + list(range(oF1, oT)) + [oT + i for i in tw]
                c = hsum(g)
                shift_ok &= (c == 19 + 18 * 1 + a + tcost[tw])
                pos = {e: k for k, e in enumerate(g)}
                glay[c].add(tuple(pos[x] < pos[y] for x, y in gpairs))
conv = defaultdict(int)
for a, cls in LI.items():
    for tw in T_words:
        conv[19 + 18 + a + tcost[tw]] += len(cls)
res['k1'] = {'T_costs': sorted(tcost.values()), 'shift_19_plus_18k_ok': shift_ok,
             'global_layers': {c: len(s) for c, s in sorted(glay.items())},
             'convolution': dict(sorted(conv.items())),
             'signatures_equal_convolution': {c: len(s) for c, s in glay.items()} == dict(conv)}
for nm in ['I', 'M']:
    del res[nm]['_layers_obj']; del res[nm]['local_words_sig']
json.dump(res, open(out_path, 'w'), indent=1)
print('k1', {k: v for k, v in res['k1'].items()})
for name in ['I', 'M']:
    r = res[name]
    print(name, {k: v for k, v in r.items() if k not in ('layers', 'Q', 'Q_capacity_origin_edge_list', 'layer_signatures', 'weights')})
    for row in r['layers']:
        print('  A=%d words=%d sig=%d sizes=%s exact=%s' % (row['cost'], row['words'], row['signatures'], row['class_sizes'], row['P_sigma_exact']))
