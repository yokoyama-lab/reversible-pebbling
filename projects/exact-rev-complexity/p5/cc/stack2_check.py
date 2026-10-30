"""補題 STACK' の検査: 森 {(c), D} → 1 本（長さ c の区間を D の上に載せる）。D は区間が短い順で c ≤ D の一番上の区間。
   変種 any: D の整列を課さず c ≤ D の区間すべて．bad: c > D の一番上の区間（成り立たない側の対照）。
   使い方: python3 stack2_check.py <pair_cmp> <Lmax> [good|any|bad]"""
import subprocess
import sys
BIN, LMAX = sys.argv[1], int(sys.argv[2])
VAR = sys.argv[3] if len(sys.argv) > 3 else 'good'
def segs(pebbles, n):
    return [q - p for p, q in zip(pebbles, pebbles[1:] + [n])]
def bits(sg, off):
    y = p = 0
    for s in sg:
        y |= 1 << (off + p)
        p += s
    return y
tot = nrun = 0
for L in range(2, LMAX + 1):
    for c in range(1, L):
        d = L - c
        pairs = []
        for xd in range(1 << d):
            if not xd & 1:
                continue
            D = segs([i for i in range(d) if xd >> i & 1], d)
            if VAR == 'good':
                ok = D == sorted(D) and c <= D[0]
            elif VAR == 'any':
                ok = c <= min(D)
            else:
                ok = c > D[0]
            if not ok:
                continue
            pairs.append((1 | (xd << c), bits([c] + D, 0)))
        if not pairs:
            continue
        inp = ''.join(f'{x} {y}\n' for x, y in pairs)
        r = subprocess.run([BIN, f'{c},{d}', str(L)], input=inp, capture_output=True, text=True).stdout.splitlines()[0]
        nrun += 1
        v = int(r.split('viol=')[1].split()[0])
        tot += v
        if v or 'CAP' in r:
            print(r)
print("stack'", VAR, 'Lmax', LMAX, 'runs', nrun, 'total viol', tot)
