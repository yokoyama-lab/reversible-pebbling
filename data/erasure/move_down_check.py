#!/usr/bin/env python3
"""The move-down inequality (MD) behind the open boundary step.

Y = (L, G, r, R) at threshold S; x is the pebble with gap G.  Moving x down
by d (0 < d < G) gives Ydown = (L, G - d, r + d, R).  Checked statement:

    phi_S(Ydown) <= phi_S(Y) + W3(G, d, S),
    W3(G, d, S) = sum over n >= 0 of min(d, max(0, G - 2^n S))

(one unit of d for every future threshold below the gap of x).  With
Y = b - v, S = 2T, G = gap v + gap x, d = gap x <= T this gives
phi(b - x) <= phi(b - v) + (gap v - T), i.e. the hard case of FreeRemoval.

Also reports 'stuck': the instances where the first-step induction for MD
does not close (alpha = G - d > S, every optimal first step of Y is the
predecessor u of x, gap u > 2S, and the budget W3 grows after removing u).

usage: move_down_check.py S k G dmax
Exit code 1 if the inequality fails.
"""
import sys, itertools
from functools import lru_cache
sys.setrecursionlimit(10000)

def rm(B, i):
    return B[:i] if i == len(B) - 1 else B[:i] + (B[i] + B[i + 1],) + B[i + 2:]

@lru_cache(maxsize=None)
def phi(B, T):
    if not B:
        return 0
    return min(max(0, B[i] - T) + phi(rm(B, i), 2 * T) for i in range(len(B)))

def W3(G, d, S):
    w, t = 0, S
    while t < G:
        w += min(d, G - t)
        t *= 2
    return w

def main():
    S, k, G, dmax = (int(a) for a in sys.argv[1:5])
    n = viol = stuck = 0
    for B in itertools.product(range(1, G + 1), repeat=k):
        pB = phi(B, S)
        Z = None
        for i in range(k):
            for d in range(1, min(B[i], dmax + 1)):
                a = B[i] - d
                B2 = B[:i] + (a,) if i == k - 1 else B[:i] + (a, B[i + 1] + d) + B[i + 2:]
                n += 1
                w = W3(B[i], d, S)
                viol += phi(B2, S) > pB + w
                if a <= S:
                    continue
                if Z is None:
                    Z = [j for j in range(k)
                         if max(0, B[j] - S) + phi(rm(B, j), 2 * S) == pB]
                if all(y == i - 1 and B[y] > 2 * S and W3(B[i] + B[y], d, 2 * S) > w
                       for y in Z):
                    stuck += 1
    print(f"S={S} k={k} G={G} dmax={dmax} | MD n={n} fail={viol} | stuck={stuck}")
    return 1 if viol else 0

if __name__ == "__main__":
    sys.exit(main())
