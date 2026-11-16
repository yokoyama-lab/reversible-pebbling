"""最適戦略を1本復元して手順を表示する（構成の型を読むため）。"""
import sys
from collections import deque
from spooky import chain, roots, _digits, EMPTY, PEBBLE, GHOST

def path(in_nodes, cap):
    n = len(in_nodes); pw = [3**i for i in range(n)]
    target = sum(pw[v]*PEBBLE for v in roots(in_nodes))
    par = {0: None}; q = deque([0])
    while q:
        code = q.popleft()
        if code == target: break
        st = _digits(code, n)
        npeb = sum(1 for x in st if x == PEBBLE)
        rdy = [all(st[u]==PEBBLE for u in in_nodes[v]) for v in range(n)]
        for v in range(n):
            c = st[v]; mv = []
            if c==EMPTY and rdy[v] and npeb<cap: mv.append((code+pw[v]*PEBBLE, f"pebble({v})"))
            elif c==PEBBLE:
                if rdy[v]: mv.append((code-pw[v]*PEBBLE, f"unpebble({v})"))
                mv.append((code+pw[v], f"ghost({v})"))
            elif c==GHOST and rdy[v] and npeb<cap: mv.append((code-pw[v], f"unghost({v})"))
            for nx, lab in mv:
                if nx not in par: par[nx] = (code, lab); q.append(nx)
    out = []; cur = target
    while par[cur] is not None:
        p, lab = par[cur]; out.append(lab); cur = p
    return out[::-1]

for n in (5, 6):
    ms = path(chain(n), 3)
    print(f"n={n}, p=3, T={len(ms)}")
    st = ['.']*n
    for i, m in enumerate(ms):
        op, v = m.split('('); v = int(v[:-1])
        st[v] = {'pebble':'P','unpebble':'.','ghost':'g','unghost':'P'}[op]
        print(f"  {i+1:3d} {m:<12} {''.join(st)}")
    print()
