/* night75_canonbfs_fo.c -- night74_canonbfs.c の frontier-only 版。
 *
 * M*(T_h, p) を Aut(T_h) 商グラフ上の BFS で求める。night74 との差は 1 点だけ:
 * 訪問済み集合を全レベル分持たず、直前 2 レベル (prev = d-1, cur = d) と
 * 作りかけのレベル (next = d+1) の 3 集合だけを保持する。
 *
 * 根拠: 商グラフは無向（toggle は対合、可否条件は両向きで同じ、ピーク制約は
 * 駒を置く向きでだけ効くが逆向きは取る向きなので常に許される）。
 * 無向グラフの BFS ではレベル d の頂点の隣接点はレベル d-1, d, d+1 のいずれか。
 * よって新規生成した c が既出かは prev ∪ cur ∪ next の所属だけで決まる。
 *
 * canon / subm / build / mkmask / toggle 可否 / ピーク制約 / goal 判定 /
 * レベルごとの fingerprint の式と TSV 形式は night74 と同一。
 * total= は正確に数えられないので max kept（prev+cur+next の状態数の最大）に置換。
 *
 * build: gcc -O2 -o night75_canonbfs_fo night75_canonbfs_fo.c
 * usage: ./night75_canonbfs_fo <h> <p> [max_depth] [levels_out.tsv]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned __int128 u128;
typedef uint64_t u64;

static int H, NV, P;
static int Ssz[32];          /* S(m) = 2^m - 1 */
static int ht_[200];         /* height of each preorder index */
static int lch[200], rch[200];
static u128 subm[200];       /* bit mask of the subtree rooted at index */
static int order_idx[200];   /* indices sorted so children come before parent */

static void build(int idx, int m)
{
    ht_[idx] = m;
    if (m >= 2) {
        lch[idx] = idx + 1;
        rch[idx] = idx + 1 + Ssz[m - 1];
        build(lch[idx], m - 1);
        build(rch[idx], m - 1);
    } else {
        lch[idx] = -1;
        rch[idx] = -1;
    }
}

static void mkmask(int idx, int m)
{
    u128 s = ((u128)1) << idx;
    if (m >= 2) {
        mkmask(lch[idx], m - 1);
        mkmask(rch[idx], m - 1);
        s |= subm[lch[idx]] | subm[rch[idx]];
    }
    subm[idx] = s;
}

/* canonical form of the configuration restricted to the subtree at idx */
static u128 canon(u128 s, int idx, int m)
{
    u128 b, L, R, t;
    if (m == 0) return 0;
    if ((s & subm[idx]) == 0) return 0;          /* empty subtree: short cut */
    b = (s >> idx) & 1;
    if (m == 1) return b;
    L = canon(s, lch[idx], m - 1);
    R = canon(s, rch[idx], m - 1);
    if (L < R) { t = L; L = R; R = t; }
    return b | (L << 1) | (R << (1 + Ssz[m - 1]));
}

static inline int pc128(u128 x)
{
    return __builtin_popcountll((u64)x) + __builtin_popcountll((u64)(x >> 64));
}

static inline u64 hsh(u128 k)
{
    u64 a = (u64)k, b = (u64)(k >> 64);
    u64 x = a * 0x9E3779B97F4A7C15ULL ^ (b + 0xC2B2AE3D27D4EB4FULL);
    x ^= x >> 29; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 32;
    return x;
}

/* ---- open addressing hash set of u128 (key 0 means empty slot; 0 = the
 *      empty configuration, handled separately by have_zero) ---------------- */
typedef struct {
    u128 *tab;
    u64 mask, cnt, cap;
    int have_zero;
} hset;

static void hs_init(hset *h, u64 cap)
{
    h->tab = (u128 *)calloc(cap, sizeof(u128));
    if (!h->tab) { fprintf(stderr, "OOM table %llu\n", (unsigned long long)cap); exit(2); }
    h->cap = cap; h->mask = cap - 1; h->cnt = 0; h->have_zero = 0;
}

static void hs_free(hset *h)
{
    free(h->tab); h->tab = NULL; h->cap = h->mask = h->cnt = 0; h->have_zero = 0;
}

static void hs_grow(hset *h)
{
    u128 *old = h->tab; u64 oc = h->cap, i;
    int hz = h->have_zero; u64 cn = h->cnt;
    hs_init(h, oc * 2);
    h->have_zero = hz; h->cnt = cn;
    for (i = 0; i < oc; i++) {
        if (old[i]) {
            u64 j = hsh(old[i]) & h->mask;
            while (h->tab[j]) j = (j + 1) & h->mask;
            h->tab[j] = old[i];
        }
    }
    free(old);
}

static inline int hs_has(const hset *h, u128 k)
{
    u64 j;
    if (k == 0) return h->have_zero;
    j = hsh(k) & h->mask;
    while (h->tab[j]) { if (h->tab[j] == k) return 1; j = (j + 1) & h->mask; }
    return 0;
}

/* returns 1 if newly inserted (caller has already checked absence) */
static inline int hs_insert(hset *h, u128 k)
{
    u64 j;
    if (k == 0) { if (h->have_zero) return 0; h->have_zero = 1; h->cnt++; return 1; }
    j = hsh(k) & h->mask;
    while (h->tab[j]) { if (h->tab[j] == k) return 0; j = (j + 1) & h->mask; }
    h->tab[j] = k; h->cnt++;
    if (h->cnt * 10 > h->cap * 6) hs_grow(h);
    return 1;
}

int main(int argc, char **argv)
{
    int m, d, i, maxd;
    u128 *cur, *nxt, goal;
    u64 ncur, nnxt, capn, maxkept = 0;
    hset prev, cs, next;           /* cs = set of level d (same members as cur[]) */
    FILE *lf = NULL;

    if (argc < 3) { fprintf(stderr, "usage: %s h p [max_depth] [levels.tsv]\n", argv[0]); return 1; }
    H = atoi(argv[1]);
    P = atoi(argv[2]);
    maxd = (argc > 3) ? atoi(argv[3]) : 1 << 30;
    if (argc > 4) { lf = fopen(argv[4], "w"); if (!lf) { perror("levels"); return 2; } }
    if (H < 1 || H > 7) { fprintf(stderr, "h out of range\n"); return 1; }

    for (m = 0; m < 32 && m <= H; m++) Ssz[m] = (1 << m) - 1;
    NV = Ssz[H];
    build(0, H);
    mkmask(0, H);
    for (i = 0; i < NV; i++) order_idx[i] = i;

    goal = 1;                                   /* only the root pebbled */
    hs_init(&prev, 1ULL << 4);                  /* level -1: empty */
    hs_init(&cs, 1ULL << 4);
    hs_init(&next, 1ULL << 4);

    capn = 1ULL << 16;
    cur = (u128 *)malloc(capn * sizeof(u128));
    nxt = (u128 *)malloc(capn * sizeof(u128));
    if (!cur || !nxt) { fprintf(stderr, "OOM frontier\n"); return 2; }

    hs_insert(&cs, 0);
    cur[0] = 0; ncur = 1;

    printf("# h=%d p=%d NV=%d  (preorder encoding, Aut-quotient, frontier-only)\n", H, P, NV);
    if (lf) fprintf(lf, "# h=%d p=%d NV=%d preorder-Aut-quotient\n#depth\tcount\tfingerprint\n", H, P, NV);
    fflush(stdout);

    for (d = 0; ; d++) {
        u64 fp = 0, k;
        /* fingerprint: same as night74_canonbfs.py _fingerprint (128-bit mix,
         * low 64 bits summed).  NOTE: differs from night74_canonbfs.c. */
        for (k = 0; k < ncur; k++) {
            u128 y = cur[k] * (u128)0x9E3779B97F4A7C15ULL;
            y ^= y >> 61;
            y *= (u128)0xBF58476D1CE4E5B9ULL;
            y ^= y >> 47;
            fp += (u64)y;
        }
        {
            u64 kept = prev.cnt + cs.cnt + next.cnt;
            if (kept > maxkept) maxkept = kept;
        }
        printf("level %d: %llu states (fp=%016llx) kept=%llu maxkept=%llu\n",
               d, (unsigned long long)ncur, (unsigned long long)fp,
               (unsigned long long)(prev.cnt + cs.cnt + next.cnt),
               (unsigned long long)maxkept);
        fflush(stdout);
        if (lf) { fprintf(lf, "%d\t%llu\t%016llx\n", d, (unsigned long long)ncur,
                          (unsigned long long)fp); fflush(lf); }

        for (k = 0; k < ncur; k++) if (cur[k] == goal) {
            printf("RESULT h=%d p=%d M=%d maxkept=%llu\n", H, P, d,
                   (unsigned long long)maxkept);
            if (lf) { fprintf(lf, "# RESULT h=%d p=%d M=%d maxkept=%llu\n", H, P, d,
                              (unsigned long long)maxkept); fclose(lf); }
            return 0;
        }
        if (ncur == 0) {
            printf("RESULT h=%d p=%d M=UNREACHABLE maxkept=%llu\n", H, P,
                   (unsigned long long)maxkept);
            if (lf) { fprintf(lf, "# RESULT h=%d p=%d M=UNREACHABLE\n", H, P); fclose(lf); }
            return 0;
        }
        if (d >= maxd) {
            printf("RESULT h=%d p=%d M=>%d (cut at max_depth) maxkept=%llu\n", H, P, d,
                   (unsigned long long)maxkept);
            if (lf) { fprintf(lf, "# RESULT h=%d p=%d M=>%d cut maxkept=%llu\n", H, P, d,
                              (unsigned long long)maxkept); fclose(lf); }
            return 0;
        }

        nnxt = 0;
        for (k = 0; k < ncur; k++) {
            u128 s = cur[k];
            int np = pc128(s);
            for (i = 0; i < NV; i++) {
                u128 t, c;
                int bit = (int)((s >> i) & 1);
                if (ht_[i] >= 2) {
                    if (!((s >> lch[i]) & 1)) continue;
                    if (!((s >> rch[i]) & 1)) continue;
                }
                if (!bit && np + 1 > P) continue;     /* peak constraint */
                t = s ^ (((u128)1) << i);
                c = canon(t, 0, H);
                if (hs_has(&prev, c) || hs_has(&cs, c)) continue;
                if (hs_insert(&next, c)) {
                    if (nnxt == capn) {
                        capn *= 2;
                        nxt = (u128 *)realloc(nxt, capn * sizeof(u128));
                        cur = (u128 *)realloc(cur, capn * sizeof(u128));
                        if (!nxt || !cur) { fprintf(stderr, "OOM frontier grow\n"); return 2; }
                        s = cur[k];
                    }
                    nxt[nnxt++] = c;
                }
            }
        }
        {
            u64 kept = prev.cnt + cs.cnt + next.cnt;   /* peak: all three full */
            if (kept > maxkept) maxkept = kept;
        }
        /* rotate: prev <- cur set, cur set <- next, next <- fresh */
        hs_free(&prev);
        prev = cs;
        cs = next;
        hs_init(&next, 1ULL << 4);
        { u128 *tmp = cur; cur = nxt; nxt = tmp; }
        ncur = nnxt;
    }
}
