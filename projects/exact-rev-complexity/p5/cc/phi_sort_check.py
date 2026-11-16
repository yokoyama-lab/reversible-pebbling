"""規則 φ_sort: 2 本の盤 X を「石から下へ次の石の手前までの区間」に分け，区間の長さを短い順に上から並べた 1 本の盤を Y とする。"""
import os
d = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'phic', '')  # phi_c の出力（9.7MB，未コミット．`phi_c a b > out/phic/phi_a_b.txt` で再生成）
def load(a, b):
    c = {}
    for line in list(open(d + f'phi_{a}_{b}.txt'))[1:]:
        k, v = line.split(':')
        c[int(k)] = set(map(int, v.split()))
    return c
def segs(x, lo, hi):
    ps = [i for i in range(lo, hi) if x >> i & 1]
    return [q - p for p, q in zip(ps, ps[1:] + [hi])]
def stack(lens):
    y, p = 0, 0
    for s in lens:
        y |= 1 << p
        p += s
    return y
def phi_sort(x, a, L, rev=False):
    return stack(sorted(segs(x, 0, a) + segs(x, a, L), reverse=rev))
tot = bad = 0
for s in range(3, 13):
    for a in range(1, s):
        b = s - a
        c = load(a, b)
        for x, ys in c.items():
            tot += 1
            if phi_sort(x, a, s) not in ys:
                bad += 1
                if bad <= 20:
                    print('miss', a, b, bin(x))
print('total', tot, 'miss', bad)
import random
random.seed(1)
def ident(x, a, L):
    return x
def rev(x, a, L):
    return phi_sort(x, a, L, rev=True)
def ab_concat(x, a, L):  # A の区間を上，B の区間を下にそのまま積む
    return stack(segs(x, 0, a) + segs(x, a, L))
def ba_concat(x, a, L):
    return stack(segs(x, a, L) + segs(x, 0, a))
def shuffled(x, a, L):
    s = segs(x, 0, a) + segs(x, a, L)
    random.shuffle(s)
    return stack(s)
for name, f in [('identity', ident), ('reverse', rev), ('A_then_B', ab_concat), ('B_then_A', ba_concat), ('shuffle', shuffled)]:
    t = m = 0
    for s in range(3, 13):
        for a in range(1, s):
            for x, ys in load(a, s - a).items():
                t += 1
                m += f(x, a, s) not in ys
    print(name, 'miss', m, '/', t)
u = t = 0
for s in range(3, 13):
    for a in range(1, s):
        for x, ys in load(a, s - a).items():
            t += 1
            u += len(ys) == 1
print('unique candidate sets', u, '/', t)
