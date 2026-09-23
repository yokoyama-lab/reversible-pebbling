/* Parallel (OpenMP) exact normal-form search for reach(p,e).  Same algorithm as nfsearch.c (see normalform.py
 * for the theory); the generation trees of the level's normal forms are expanded a few levels and the subtrees
 * are distributed over threads.  Successor normal forms are deduplicated per thread and merged into the global
 * table in batches.
 * Usage: OMP_NUM_THREADS=k ./nfsearch_omp p E nmax
 * Build: gcc -O2 -fopenmp -o nfsearch_omp nfsearch_omp.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <omp.h>

#define MAXP 8
static int P, E, NMAX, BITS;
typedef struct { uint16_t pos[MAXP]; uint8_t k; } cfg_t;
static uint64_t pack(const uint16_t *pos, int k) { uint64_t v = 0; for (int i = 0; i < k; i++) v |= (uint64_t)pos[i] << (BITS * i); return v; }
static int unpack(uint64_t v, uint16_t *pos) { uint64_t m = (1ULL << BITS) - 1; int i = 0; while (v) { pos[i++] = (uint16_t)(v & m); v >>= BITS; } return i; }

typedef struct { uint64_t *a; size_t n, cap; } vec;
static void vpush(vec *v, uint64_t x) { if (v->n == v->cap) { v->cap = v->cap ? 2 * v->cap : 1024; v->a = realloc(v->a, v->cap * 8); if (!v->a) { fprintf(stderr, "oom vec\n"); exit(1); } } v->a[v->n++] = x; }

/* global table of normal forms (packed; 0 = free slot; empty config tracked separately) */
static uint64_t *tab; static uint64_t cap = 1 << 22, cnt = 0; static int empty_in = 0;
static inline uint64_t hash64(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static void rehash(void);
static int insert_packed(uint64_t v) {
    if (v == 0) { if (empty_in) return 0; empty_in = 1; cnt++; return 1; }
    if (cnt * 2 > cap) rehash();
    uint64_t h = hash64(v) & (cap - 1);
    while (tab[h]) { if (tab[h] == v) return 0; h = (h + 1) & (cap - 1); }
    tab[h] = v; cnt++; return 1;
}
static void rehash(void) {
    uint64_t *ot = tab; uint64_t oc = cap;
    cap *= 2; tab = calloc(cap, 8); if (!tab) { fprintf(stderr, "oom hash\n"); exit(1); }
    cnt = empty_in ? 1 : 0;
    for (uint64_t i = 0; i < oc; i++) if (ot[i]) insert_packed(ot[i]);
    free(ot);
}

static vec nxtl;                       /* next level's worklist (global, written under critical) */
static long long reach_lev[16];
static int curlev;
static uint64_t ncfg = 0;

/* per-thread state */
#define LCAP (1u << 21)
static __thread uint64_t *ltab = NULL; static __thread uint32_t lcnt = 0;
static __thread vec pending; static __thread uint64_t t_ncfg = 0;
static int LASTLEV = -1;               /* level whose successors are NOT stored (only the largest 1-pebble normal form is tracked) */
static __thread long long t_maxsingle = 0;

static void flush(void) {
    #pragma omp critical
    {
        for (size_t j = 0; j < pending.n; j++) {
            uint64_t v = pending.a[j];
            if (insert_packed(v)) { vpush(&nxtl, v); uint16_t pos[MAXP]; int k = unpack(v, pos); if (k == 1 && pos[0] > reach_lev[curlev + 1]) reach_lev[curlev + 1] = pos[0]; }
        }
        ncfg += t_ncfg;
        if (t_maxsingle > reach_lev[curlev + 1]) reach_lev[curlev + 1] = t_maxsingle;
    }
    t_ncfg = 0; pending.n = 0; t_maxsingle = 0;
    if (ltab) memset(ltab, 0, LCAP * 8); lcnt = 0;
}
static inline void local_insert(uint64_t v) {
    if (!ltab) ltab = calloc(LCAP, 8);
    if (v == 0) return;  /* the empty config is always already known */
    if (lcnt * 2 > LCAP) flush();
    uint64_t h = hash64(v) & (LCAP - 1);
    while (ltab[h]) { if (ltab[h] == v) return; h = (h + 1) & (LCAP - 1); }
    ltab[h] = v; lcnt++; vpush(&pending, v);
}

static inline int removable(const uint16_t *C, int k, int i) { int g = C[i] - (i ? C[i - 1] : 0); return g <= (1 << (P - k)); }
static uint64_t nf(const uint16_t *C, int k) {
    uint16_t D[MAXP]; memcpy(D, C, k * 2);
    int changed = 1;
    while (changed) { changed = 0; for (int i = 0; i < k; i++) if (removable(D, k, i)) { for (int j = i; j + 1 < k; j++) D[j] = D[j + 1]; k--; changed = 1; break; } }
    return pack(D, k);
}
static void process(const uint16_t *C, int k) {
    t_ncfg++;
    for (int i = 0; i < k; i++) {
        if (C[i] < 2 || (i > 0 && C[i - 1] == C[i] - 1)) continue;   /* only non-available pebbles can be erased */
        uint16_t D[MAXP]; int m = 0; for (int j = 0; j < k; j++) if (j != i) D[m++] = C[j];
        uint64_t v = nf(D, m);
        if (curlev == LASTLEV) { if (v && !(v >> BITS) && (long long)v > t_maxsingle) t_maxsingle = (long long)v; }   /* single pebble at position v */
        else local_insert(v);
    }
}
/* children of C in the canonical generation tree (insert x as the lowest removable pebble of the new config) */
static void children(const uint16_t *C, int k, vec *out) {
    if (k >= P) return;
    int budget = 1 << (P - k - 1); int prev = 0; uint16_t D[MAXP];
    for (int i = 0; i <= k; i++) {
        int nxt = (i < k) ? C[i] : NMAX + 1;
        int hi = prev + budget; if (hi >= nxt) hi = nxt - 1;
        for (int x = prev + 1; x <= hi; x++) {
            for (int j = 0; j < i; j++) D[j] = C[j]; D[i] = (uint16_t)x; for (int j = i; j < k; j++) D[j + 1] = C[j];
            int ok = 1; for (int j = 0; j < i; j++) if (removable(D, k + 1, j)) { ok = 0; break; }
            if (ok) vpush(out, pack(D, k + 1));
        }
        prev = nxt;
    }
}
static void gen(uint16_t *C, int k) {   /* full subtree */
    process(C, k);
    if (k >= P) return;
    int budget = 1 << (P - k - 1); int prev = 0; uint16_t D[MAXP];
    for (int i = 0; i <= k; i++) {
        int nxt = (i < k) ? C[i] : NMAX + 1;
        int hi = prev + budget; if (hi >= nxt) hi = nxt - 1;
        for (int x = prev + 1; x <= hi; x++) {
            for (int j = 0; j < i; j++) D[j] = C[j]; D[i] = (uint16_t)x; for (int j = i; j < k; j++) D[j + 1] = C[j];
            int ok = 1; for (int j = 0; j < i; j++) if (removable(D, k + 1, j)) { ok = 0; break; }
            if (ok) gen(D, k + 1);
        }
        prev = nxt;
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: nfsearch_omp p E nmax\n"); return 1; }
    P = atoi(argv[1]); E = atoi(argv[2]); NMAX = atoi(argv[3]);
    if (P > MAXP || E > 14) { fprintf(stderr, "limits\n"); return 1; }
    BITS = 1; while ((1 << BITS) <= NMAX) BITS++;
    if (BITS * P > 64) { fprintf(stderr, "cannot pack %d positions of %d bits into 64 bits\n", P, BITS); return 1; }
    tab = calloc(cap, 8);
    insert_packed(0);
    vec cur = {0}; vpush(&cur, 0);
    for (int e = 0; e < 16; e++) reach_lev[e] = 0;
    reach_lev[0] = 1 << (P - 1);
    int nth = omp_get_max_threads();
    LASTLEV = E - 1;   /* successors of the last processed level are only inspected, not stored */
    time_t t0 = time(NULL);
    printf("# nfsearch_omp p=%d E=%d nmax=%d threads=%d\n", P, E, NMAX, nth); fflush(stdout);
    /* N_{e+1} is complete once level e has been processed, so the last level E need not be processed at all */
    for (int e = 0; e < E || (e == 0 && E == 0); e++) {
        curlev = e; uint64_t ncfg0 = ncfg; nxtl.n = 0;
        /* expand generation trees until enough parallel work; expanded nodes are processed here (master thread) */
        vec work = {0}; for (size_t i = 0; i < cur.n; i++) vpush(&work, cur.a[i]);
        while (work.n && work.n < (size_t)(256 * nth)) {
            vec nw = {0};
            for (size_t i = 0; i < work.n; i++) { uint16_t C[MAXP]; int k = unpack(work.a[i], C); process(C, k); children(C, k, &nw); }
            free(work.a); work = nw;
        }
        flush();
        #pragma omp parallel
        {
            #pragma omp for schedule(dynamic, 8)
            for (size_t i = 0; i < work.n; i++) { uint16_t C[MAXP]; int k = unpack(work.a[i], C); gen(C, k); }
            flush();
        }
        free(work.a);
        long long r = 0; for (int f = 0; f <= e; f++) if (reach_lev[f] > r) r = reach_lev[f];
        printf("e=%d reach=%lld conj=%lld %s new_normal_forms=%zu configs_this_level=%llu configs_total=%llu seconds=%ld\n",
               e, r, (long long)(e + 2) * (1 << (P - 2)), r < NMAX ? "PROVED" : "UNPROVED(nmax)", cur.n, (unsigned long long)(ncfg - ncfg0), (unsigned long long)ncfg, (long)(time(NULL) - t0));
        long long r1 = r > reach_lev[e + 1] ? r : reach_lev[e + 1];   /* level e+1 is now complete */
        printf("complete e=%d reach=%lld conj=%lld %s normal_forms_at_level=%s seconds=%ld\n",
               e + 1, r1, (long long)(e + 3) * (1 << (P - 2)), r1 < NMAX ? "PROVED" : "UNPROVED(nmax)", e == LASTLEV ? "not_stored" : ({ static char b[32]; snprintf(b, 32, "%zu", nxtl.n); b; }), (long)(time(NULL) - t0));
        fflush(stdout);
        free(cur.a); cur = nxtl; nxtl.a = NULL; nxtl.n = nxtl.cap = 0;
    }
    printf("# total normal forms %llu\n", (unsigned long long)cnt);
    return 0;
}
