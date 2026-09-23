/* Exhaustive layered BFS for erasure-budgeted clean reversible chain pebbling.
 * Chain 0->1->...->N (node 0 free entrance).  States = (config with <= p pebbles, erasures used eu <= E).
 * Config indexed by combinatorial rank (positions 1..N -> bits 0..N-1).  Visited bitset per eu level.
 * Prints, for each (n, eu), the BFS depth at which config {n} is first reached with exactly eu erasures.
 * Usage: ./reachbfs N p E   (N <= 250, p <= 8, E <= 15)
 * Build: gcc -O2 -o reachbfs reachbfs.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 256
#define MAXP 8
static uint64_t C[MAXN + 1][MAXP + 2];
static uint64_t offs[MAXP + 2];
static int N, P, E;
static uint64_t T;              /* configs with <= P pebbles */
static uint8_t **vis;           /* vis[eu][rank/8] (bitset mode) or vis[eu][rank] (depth mode) */
static int WIT = 0;             /* depth mode: store 1+(depth mod 254) per state, reconstruct witnesses */
static inline uint8_t enc(int d) { return (uint8_t)(1 + (d % 254)); }
static int64_t first[MAXN + 1][16];

typedef struct { uint64_t *a; size_t n, cap; } vec;
static void vpush(vec *v, uint64_t x) {
    if (v->n == v->cap) { v->cap = v->cap ? v->cap * 2 : 1 << 16; v->a = realloc(v->a, v->cap * 8); if (!v->a) { fprintf(stderr, "oom\n"); exit(1); } }
    v->a[v->n++] = x;
}

static inline uint64_t rank_of(const uint8_t *pos, int k) { /* pos: 1-based nodes, sorted ascending */
    uint64_t r = offs[k];
    for (int i = 0; i < k; i++) r += C[pos[i] - 1][i + 1];
    return r;
}
static inline int unrank(uint64_t r, uint8_t *pos) {
    int k = 0;
    while (k + 1 <= P && offs[k + 1] <= r) k++;
    r -= offs[k];
    for (int i = k; i >= 1; i--) {
        /* largest b with C[b][i] <= r */
        int lo = i - 1, hi = N - 1;  /* C[lo][i]=0 <= r always */
        while (lo < hi) { int mid = (lo + hi + 1) >> 1; if (C[mid][i] <= r) lo = mid; else hi = mid - 1; }
        pos[i - 1] = (uint8_t)(lo + 1);
        r -= C[lo][i];
    }
    return k;
}

static int curdepth = 0;
static inline int visit(int eu, uint64_t r) { /* returns 1 if newly visited */
    if (WIT) { if (vis[eu][r]) return 0; vis[eu][r] = enc(curdepth); return 1; }
    uint8_t *b = &vis[eu][r >> 3]; uint8_t m = 1 << (r & 7);
    if (*b & m) return 0; *b |= m; return 1;
}
static inline int depth_is(int eu, uint64_t r, int d) { return vis[eu][r] == enc(d); }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: reachbfs N p E\n"); return 1; }
    N = atoi(argv[1]); P = atoi(argv[2]); E = atoi(argv[3]); WIT = (argc > 4 && strcmp(argv[4], "-w") == 0);
    if (N > MAXN - 1 || P > MAXP || E > 15) { fprintf(stderr, "limits: N<=255 p<=8 E<=15\n"); return 1; }
    for (int n = 0; n <= MAXN; n++) { C[n][0] = 1; for (int k = 1; k <= MAXP + 1; k++) C[n][k] = n ? C[n - 1][k - 1] + C[n - 1][k] : 0; }
    offs[0] = 0; for (int k = 1; k <= P + 1; k++) offs[k] = offs[k - 1] + C[N][k - 1];
    T = offs[P + 1];
    fprintf(stderr, "N=%d p=%d E=%d: configs per level T=%llu, bitset %.1f MB per level\n", N, P, E, (unsigned long long)T, T / 8.0 / 1e6);
    vis = malloc((E + 1) * sizeof(uint8_t *));
    for (int e = 0; e <= E; e++) { vis[e] = calloc(WIT ? T : (T >> 3) + 1, 1); if (!vis[e]) { fprintf(stderr, "oom bitset\n"); return 1; } }
    for (int n = 0; n <= N; n++) for (int e = 0; e < 16; e++) first[n][e] = -1;

    vec cur = {0}, nxt = {0};
    vpush(&cur, 0); visit(0, 0);  /* empty config: depth 0 */
    uint64_t total = 1; int d = 0; time_t t0 = time(NULL);
    uint8_t pos[MAXP + 2], np[MAXP + 2];
    while (cur.n) {
        d++; nxt.n = 0; curdepth = d;
        for (size_t idx = 0; idx < cur.n; idx++) {
            uint64_t s = cur.a[idx]; int eu = (int)(s >> 48); uint64_t r = s & ((1ULL << 48) - 1);
            int k = unrank(r, pos);
            /* removals (reversible if predecessor pebbled or node 1; else erasure) */
            for (int j = 0; j < k; j++) {
                int rev = (pos[j] == 1) || (j > 0 && pos[j - 1] == pos[j] - 1);
                int ne = rev ? eu : eu + 1;
                if (ne > E) continue;
                int m = 0; for (int i = 0; i < k; i++) if (i != j) np[m++] = pos[i];
                uint64_t nr = rank_of(np, m);
                if (visit(ne, nr)) {
                    vpush(&nxt, nr | ((uint64_t)ne << 48)); total++;
                    if (m == 1 && first[np[0]][ne] < 0) first[np[0]][ne] = d;
                }
            }
            /* placements: node 1 if empty, and pos[j]+1 if empty and <= N */
            if (k < P) {
                for (int j = -1; j < k; j++) {
                    int x = (j < 0) ? 1 : pos[j] + 1;
                    if (x > N) continue;
                    if (j + 1 < k && pos[j + 1] == x) continue; /* already pebbled */
                    int m = 0, ins = 0;
                    for (int i = 0; i < k; i++) { if (!ins && pos[i] > x) { np[m++] = (uint8_t)x; ins = 1; } np[m++] = pos[i]; }
                    if (!ins) np[m++] = (uint8_t)x;
                    uint64_t nr = rank_of(np, m);
                    if (visit(eu, nr)) {
                        vpush(&nxt, nr | ((uint64_t)eu << 48)); total++;
                        if (m == 1 && first[np[0]][eu] < 0) first[np[0]][eu] = d;
                    }
                }
            }
        }
        vec tmp = cur; cur = nxt; nxt = tmp;
        if (d % 10 == 0) fprintf(stderr, "  layer %d: frontier %zu total %llu (%lds)\n", d, cur.n, (unsigned long long)total, (long)(time(NULL) - t0));
    }
    fprintf(stderr, "done: depth %d, states %llu, %lds\n", d - 1, (unsigned long long)total, (long)(time(NULL) - t0));
    printf("# N=%d p=%d E=%d states=%llu depth=%d seconds=%ld\n", N, P, E, (unsigned long long)total, d - 1, (long)(time(NULL) - t0));
    printf("n,eu,first_depth\n");
    for (int n = 1; n <= N; n++) for (int e = 0; e <= E; e++) if (first[n][e] >= 0) printf("%d,%d,%lld\n", n, e, (long long)first[n][e]);
    if (!WIT) return 0;
    /* witnesses: for each budget e, target n = reach(p,e) (max n reached with eu<=e), eu = argmin depth */
    for (int e = 0; e <= E; e++) {
        int rn = 0; long long best = -1; int beu = 0;
        for (int n = 1; n <= N; n++) for (int eu = 0; eu <= e; eu++) if (first[n][eu] >= 0) {
            if (n > rn) { rn = n; best = first[n][eu]; beu = eu; }
            else if (n == rn && first[n][eu] < best) { best = first[n][eu]; beu = eu; }
        }
        if (!rn) continue;
        printf("witness e=%d n=%d eu=%d moves=%lld\n", e, rn, beu, best);
        /* walk back */
        uint8_t cp[MAXP + 2], pp[MAXP + 2]; int k = 1; cp[0] = (uint8_t)rn; int eu = beu; int dd = (int)best;
        /* collect moves in reverse */
        char **mv = malloc(sizeof(char *) * (dd + 1)); int nm = 0;
        while (dd > 0) {
            int found = 0;
            /* predecessor by reversible flip: same eu; the flipped node x must be available in cp (x==1 or x-1 in cp) */
            /* (a) predecessor had x additionally (we removed x reversibly): x not in cp, x==1 or x-1 in cp, k<P */
            if (k < P) for (int j = -1; j < k && !found; j++) {
                int x = (j < 0) ? 1 : cp[j] + 1; if (x > N) continue;
                if (j + 1 < k && cp[j + 1] == x) continue;
                int m = 0, ins = 0; for (int i = 0; i < k; i++) { if (!ins && cp[i] > x) { pp[m++] = (uint8_t)x; ins = 1; } pp[m++] = cp[i]; } if (!ins) pp[m++] = (uint8_t)x;
                if (depth_is(eu, rank_of(pp, m), dd - 1)) { char *s = malloc(32); sprintf(s, "remove %d", x); mv[nm++] = s; memcpy(cp, pp, m); k = m; found = 1; }
            }
            /* (b) predecessor lacked x (we placed x): x in cp, x==1 or x-1 in cp */
            for (int j = 0; j < k && !found; j++) {
                int x = cp[j]; if (!(x == 1 || (j > 0 && cp[j - 1] == x - 1))) continue;
                int m = 0; for (int i = 0; i < k; i++) if (i != j) pp[m++] = cp[i];
                if (depth_is(eu, rank_of(pp, m), dd - 1)) { char *s = malloc(32); sprintf(s, "place %d", x); mv[nm++] = s; memcpy(cp, pp, m); k = m; found = 1; }
            }
            /* (c) predecessor had x additionally with x-1 empty, x>=2, eu-1 (erasure) */
            if (!found && eu > 0 && k < P) for (int x = 2; x <= N && !found; x++) {
                int inC = 0, pred = 0; for (int i = 0; i < k; i++) { if (cp[i] == x) inC = 1; if (cp[i] == x - 1) pred = 1; }
                if (inC || pred) continue;
                int m = 0, ins = 0; for (int i = 0; i < k; i++) { if (!ins && cp[i] > x) { pp[m++] = (uint8_t)x; ins = 1; } pp[m++] = cp[i]; } if (!ins) pp[m++] = (uint8_t)x;
                if (depth_is(eu - 1, rank_of(pp, m), dd - 1)) { char *s = malloc(32); sprintf(s, "ERASE %d", x); mv[nm++] = s; memcpy(cp, pp, m); k = m; eu--; found = 1; }
            }
            if (!found) { fprintf(stderr, "reconstruction failed at depth %d\n", dd); break; }
            dd--;
        }
        for (int i = nm - 1; i >= 0; i--) { printf("%s\n", mv[i]); free(mv[i]); }
        free(mv);
        printf("end\n");
    }
    return 0;
}
