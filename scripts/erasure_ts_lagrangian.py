"""Compare the erasure-pebbling results with the priced recurrence of
Thumann-Soloveichik (arXiv:2610.24435, Thm 1): an erasure costs 1 + mu, a
reversible move 1; C_mu(n, S) is the least priced cost (key: cost, then fewest
erasures).  This is numerical evidence (layer 2), conditional on that theorem.

Checks, for 3 <= S <= SMAX and n <= NMAX:
 1. mu = 2(S-1): C = max(4n - 2S - 1, 2n - 1)  (= Contraction.length_ge as a
    Lagrangian bound);
 2. at mu = 2(S-1), the fewest erasures I_min(n) satisfies
    I_min <= e  <=>  n <= T(S) + e*T(S-1)  (= the frontier of Triangular);
 3. one past the frontier, max_mu (C_mu(n,S) - mu*e) = L0 + 2 for S >= 4
    (L0 = NextPoint's lower candidate), i.e. L0 is excluded.
Usage: python3 scripts/erasure_ts_lagrangian.py [NMAX] [SMAX]
"""
import sys

INF = 10**18
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 60
SMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6

F = {}
for S in range(1, SMAX + 1):
    for n in range(1, NMAX + 1):
        if n == 1:
            F[n, S] = 1
        elif S == 1:
            F[n, S] = INF
        else:
            F[n, S] = min(F[m, S] + F[n - m, S - 1] + F[m, S - 1] for m in range(1, n))


def lex(mu):
    C = {}
    for S in range(1, SMAX + 1):
        for n in range(1, NMAX + 1):
            if n == 1:
                C[n, S] = (1, 0)
                continue
            if S == 1:
                C[n, S] = (INF, INF)
                continue
            best = (INF, INF)
            for m in range(1, n):
                a, b, f = C[m, S], C[n - m, S - 1], F[m, S - 1]
                cl = min((f, 0) if f < INF else (INF, INF), (1 + mu, 1))
                best = min(best, (a[0] + b[0] + cl[0], a[1] + b[1] + cl[1]))
            C[n, S] = best
    return C


def tri(p):
    return p * (p - 1) // 2 + 1


bad = 0
MUS = list(range(0, 4 * NMAX))
CS = {mu: lex(mu) for mu in MUS}
for S in range(3, SMAX + 1):
    C = CS[2 * (S - 1)]
    for n in range(1, NMAX + 1):
        if C[n, S][0] != max(4 * n - 2 * S - 1, 2 * n - 1):
            bad += 1
            print("check1", S, n, C[n, S])
        for e in range(0, 12):
            if n >= S and (C[n, S][1] <= e) != (n <= tri(S) + e * tri(S - 1)):
                bad += 1
                print("check2", S, n, e)
    if S >= 4:
        for e in range(0, 12):
            n = tri(S) + e * tri(S - 1) + 1
            if n > NMAX:
                break
            L0 = 2 * n - 1 + 2 * (n - ((S - 1) * (e + 1) + 1))
            lb = max(CS[mu][n, S][0] - mu * e for mu in MUS)
            print(f"S={S} e={e} n={n}: L0={L0} priced lower bound={lb}")
            if lb != L0 + 2:
                bad += 1
print("NMAX", NMAX, "SMAX", SMAX, "mismatches", bad)
