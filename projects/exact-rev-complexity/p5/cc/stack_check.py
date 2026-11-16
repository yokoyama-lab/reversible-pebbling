"""補題 STACK の検査: 森 {C, (t), 文脈の鎖…} → 森 {C を (t) の上に載せた 1 本, 文脈の鎖…}。
   C は区間が短い順で，区間はすべて t 以下。(t) は頂上だけに石。文脈の鎖は頂上に石がある任意の盤（何本でも，長さの並びを引数で）。
   変種 unsorted: 整列を課さない．lastonly: 一番下の区間だけ t 以下．
   変異 bad: 区間に t より長いものがある C も入れる（成り立たないはずの側）。
   使い方: python3 stack_check.py <pair_cmp> <Lmax> <文脈の鎖の数 0|1> [bad]"""
import subprocess
import sys
BIN, LMAX, NCTX = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
VAR = sys.argv[4] if len(sys.argv) > 4 else 'good'
BAD = VAR == 'bad'
def segs(pebbles, n):
    return [q - p for p, q in zip(pebbles, pebbles[1:] + [n])]
def bits(sg, off):
    y = p = 0
    for s in sg:
        y |= 1 << (off + p)
        p += s
    return y
def run(P, Q, pairs):
    inp = ''.join(f'{x} {y}\n' for x, y in pairs)
    out = subprocess.run([BIN, ','.join(map(str, P)), ','.join(map(str, Q))], input=inp, capture_output=True, text=True).stdout
    return out.splitlines()[0]
tot = 0
nrun = 0
for L in range(2, LMAX + 1):
    for c in ([0] if NCTX == 0 else range(1, L - 1)):
        for a in range(1, L - c):
            t = L - c - a
            if t < 1:
                continue
            P = (a, t) + ((c,) if c else ())
            Q = (a + t,) + ((c,) if c else ())
            pairs = []
            for xa in range(1 << a):
                if not xa & 1:
                    continue
                C = segs([i for i in range(a) if xa >> i & 1], a)
                ok = C == sorted(C) and max(C) <= t
                if VAR == 'unsorted':  # 変種: 整列を課さず，区間がすべて t 以下
                    ok, BADX = max(C) <= t, False
                elif VAR == 'lastonly':  # 変種: 整列を課さず，C の一番下の区間だけ t 以下
                    ok, BADX = C[-1] <= t, False
                else:
                    BADX = BAD
                if ok == BADX:
                    continue
                ctxs = [0] if not c else [z for z in range(1 << c) if z & 1]
                for z in ctxs:
                    x = bits(C, 0) | (1 << a) | (z << (a + t))
                    y = bits(C + [t], 0) | (z << (a + t))
                    pairs.append((x, y))
            if not pairs:
                continue
            r = run(P, Q, pairs)
            nrun += 1
            v = int(r.split('viol=')[1].split()[0])
            tot += v
            if v or 'CAP' in r:
                print(r)
print('stack', 'ctx' if NCTX else 'noctx', VAR, 'Lmax', LMAX, 'runs', nrun, 'total viol', tot)
