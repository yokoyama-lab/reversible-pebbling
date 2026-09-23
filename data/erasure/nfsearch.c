/* Normal-form search for reach(p,e) (exact; see normalform.py for the theory).
 * Usage: ./nfsearch p E nmax      -> prints reach(p,e) for e<=E, counts, and the 1-pebble normal forms per level.
 * Build: gcc -O2 -o nfsearch nfsearch.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXP 8
static int P, E, NMAX;
typedef struct { uint16_t pos[MAXP]; uint8_t k; uint8_t lev; } key_t_;
static int BITS; /* bits per position; packed key = sum pos[i] << (BITS*i); positions >= 1 so key 0 = empty config */
static uint64_t pack(const key_t_ *k) { uint64_t v = 0; for (int i = 0; i < k->k; i++) v |= (uint64_t)k->pos[i] << (BITS * i); return v; }
static void unpack(uint64_t v, key_t_ *k) { memset(k, 0, sizeof *k); uint64_t m = (1ULL << BITS) - 1; int i = 0; while (v) { k->pos[i++] = (uint16_t)(v & m); v >>= BITS; } k->k = i; }

/* hash table of packed normal forms (0 = free slot; the empty config is tracked separately) */
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
static int insert(const key_t_ *k) { return insert_packed(pack(k)); }
static void rehash(void) {
    uint64_t *ot = tab; uint64_t oc = cap;
    cap *= 2; tab = calloc(cap, sizeof(uint64_t)); if (!tab) { fprintf(stderr, "oom hash\n"); exit(1); }
    cnt = empty_in ? 1 : 0;
    for (uint64_t i = 0; i < oc; i++) if (ot[i]) insert_packed(ot[i]);
    free(ot);
}

/* worklists per level */
typedef struct { uint64_t *a; size_t n, cap; } vec;
static void vpush(vec *v, const key_t_ *x) { if (v->n == v->cap) { v->cap = v->cap ? 2 * v->cap : 1024; v->a = realloc(v->a, v->cap * 8); if (!v->a) { fprintf(stderr, "oom vec\n"); exit(1); } } v->a[v->n++] = pack(x); }

static inline int removable(const uint16_t *C, int k, int i) { int g = C[i] - (i ? C[i - 1] : 0); return g <= (1 << (P - k)); }
static void nf(const uint16_t *C, int k, key_t_ *out) {
    uint16_t D[MAXP]; memcpy(D, C, k * 2);
    int changed = 1;
    while (changed) { changed = 0; for (int i = 0; i < k; i++) if (removable(D, k, i)) { for (int j = i; j + 1 < k; j++) D[j] = D[j + 1]; k--; changed = 1; break; } }
    memset(out, 0, sizeof *out); memcpy(out->pos, D, k * 2); out->k = k;
}

static uint64_t ncfg = 0, ncfg_level = 0;
static vec newlist; static int curlev;
static long long reach_lev[16];

static void process(const uint16_t *C, int k) {
    ncfg++;
    /* erasures: pebble i with C[i]>=2 and predecessor empty */
    for (int i = 0; i < k; i++) {
        if (C[i] < 2 || (i > 0 && C[i - 1] == C[i] - 1)) continue;
        uint16_t D[MAXP]; int m = 0; for (int j = 0; j < k; j++) if (j != i) D[m++] = C[j];
        key_t_ nk; nf(D, m, &nk); nk.lev = curlev + 1;
        if (insert(&nk)) { vpush(&newlist, &nk); if (nk.k == 1 && nk.pos[0] > reach_lev[curlev + 1]) reach_lev[curlev + 1] = nk.pos[0]; }
    }
}
static void gen(uint16_t *C, int k) { /* canonical reverse elimination */
    process(C, k);
    if (k >= P) return;
    int budget = 1 << (P - k - 1);
    int prev = 0;
    uint16_t D[MAXP];
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
    if (argc < 4) { fprintf(stderr, "usage: nfsearch p E nmax\n"); return 1; }
    P = atoi(argv[1]); E = atoi(argv[2]); NMAX = atoi(argv[3]);
    if (P > MAXP || E > 14 || NMAX > 65000) { fprintf(stderr, "limits\n"); return 1; }
    BITS = 1; while ((1 << BITS) <= NMAX) BITS++;
    if (BITS * P > 64) { fprintf(stderr, "cannot pack %d positions of %d bits into 64 bits\n", P, BITS); return 1; }
    tab = calloc(cap, sizeof(uint64_t));
    key_t_ empty; memset(&empty, 0, sizeof empty); insert(&empty);
    vec cur = {0}; vpush(&cur, &empty);
    for (int e = 0; e < 16; e++) reach_lev[e] = 0;
    reach_lev[0] = 1 << (P - 1);
    time_t t0 = time(NULL);
    printf("# nfsearch p=%d E=%d nmax=%d\n", P, E, NMAX);
    for (int e = 0; e <= E; e++) {
        curlev = e; newlist.n = 0; ncfg_level = ncfg;
        for (size_t i = 0; i < cur.n; i++) { key_t_ kk; unpack(cur.a[i], &kk); uint16_t C[MAXP]; memcpy(C, kk.pos, kk.k * 2); gen(C, kk.k); }
        long long r = 0; for (int f = 0; f <= e; f++) if (reach_lev[f] > r) r = reach_lev[f];
        printf("e=%d reach=%lld conj=%lld %s new_normal_forms=%zu configs_this_level=%llu configs_total=%llu seconds=%ld\n",
               e, r, (long long)(e + 2) * (1 << (P - 2)), r < NMAX ? "PROVED" : "UNPROVED(nmax)", cur.n, (unsigned long long)(ncfg - ncfg_level), (unsigned long long)ncfg, (long)(time(NULL) - t0));
        fflush(stdout);
        vec tmp = cur; cur = newlist; newlist = tmp;
    }
    printf("# total normal forms %llu\n", (unsigned long long)cnt);
    return 0;
}
