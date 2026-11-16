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
    res[name] = {'events': n, 'Q_edges_transitive': len(Q), 'LE_Q': len(ext),
                 'capacity_legal': len(legal), 'capacity_free_legal': len(free),
                 'LE_Q_subset_capacity_free': set(ext) <= free,
                 'guarded_LE_Q_equals_legal': guarded == legal,
                 'layers': rows,
                 'total_signatures': sum(r['signatures'] for r in rows),
                 'all_P_sigma_exact': all_ok,
                 'Q': sorted(Q)}
json.dump(res, open(out_path, 'w'), indent=1)
for name in ['I', 'M']:
    r = res[name]
    print(name, {k: v for k, v in r.items() if k not in ('layers', 'Q')})
    for row in r['layers']:
        print('  A=%d words=%d sig=%d sizes=%s exact=%s' % (row['cost'], row['words'], row['signatures'], row['class_sizes'], row['P_sigma_exact']))
