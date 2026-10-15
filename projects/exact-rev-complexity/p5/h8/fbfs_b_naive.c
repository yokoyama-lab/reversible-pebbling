/* fbfs_b_naive.c — 実装 B の素朴版（枝刈りなし・32 バイト鍵）。fbfs_b.c の枝刈りと鍵の検査用.
 *
 * 実装 A（fbfs.c）と同じ問いを、別の状態表現・別の後継生成で解く。共通なのは
 * 「フロンティア BFS（3 層だけ保持）」という探索の骨格だけで、その正しさの根拠
 * （無向・ペブル数の偶奇で二部）は実行時に検査する。
 *
 * ## 表現（A との違い）
 * A は高さ H-2 の部分木の軌道に id を振って後継表を前計算する。B は id も表も持たない。
 * 状態は「再帰配置」の 2^H-1 ビット列そのもの:
 *     block(T_k) = [根のビット][block(左の T_{k-1})][block(右の T_{k-1})]
 * 正準形 = すべての節点で 左の block <= 右の block（ビット列の辞書式順）。
 * これは Aut(T_H)（各節点での左右の入れ替えが生成する群）の軌道の代表として一意である
 * （下から帰納: 部分木の軌道は (根のビット, 子の軌道の多重集合) で決まり、
 *   多重集合を辞書式に小さい順に並べた列は一意）。
 *
 * ## 後継（A との違い）
 * 正準形の上で、すべての頂点 v について合法性を直接ビットで調べ（葉は常に合法、
 * 内部頂点は 2 つの子のビットが立っているとき）、置く手はペブル数 < P のときだけ。
 * toggle したあと v の祖先を下から順にたどり、各祖先で左右の block を比べて
 * 大きい順なら入れ替える（変わったのは v を含む側だけなので 1 回の上り走査で正準形に戻る）。
 * 軌道による手の間引きはしない（同じ軌道に行く手は局所的に整列・重複除去する）。
 *
 * build: gcc -O3 -march=native -fopenmp -o fbfs_b fbfs_b.c
 * usage: ./fbfs_b <H> <P> [--threads N] [--stop-at-goal 0|1] [--maxdepth D] [--layers FILE]
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <sys/resource.h>

#define MAXN 255           /* H <= 8 */
#define WORDS 4            /* 256 ビット */

static int H, P, N;
static int lch[MAXN], rch[MAXN], par[MAXN], blen[MAXN]; /* blen = その頂点を根とする block の長さ */

static void fail(const char *m) { fprintf(stderr, "fatal: %s\n", m); exit(2); }
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
static long rss_mb(void) { struct rusage r; getrusage(RUSAGE_SELF, &r); return r.ru_maxrss / 1024; }

/* 再帰配置の位置を作る。pos から始まる高さ k の block。 */
static void layout(int pos, int k, int parent) {
    par[pos] = parent;
    blen[pos] = (1 << k) - 1;
    if (k == 1) { lch[pos] = rch[pos] = -1; return; }
    int m = (1 << (k - 1)) - 1;
    lch[pos] = pos + 1;
    rch[pos] = pos + 1 + m;
    layout(pos + 1, k - 1, pos);
    layout(pos + 1 + m, k - 1, pos);
}

typedef struct { uint64_t w[WORDS]; } St; /* ビット i は w[i>>6] の (i&63) */

static inline void unpack(const St *s, uint8_t *b) {
    for (int i = 0; i < N; i++) b[i] = (s->w[i >> 6] >> (i & 63)) & 1;
}
static inline void pack(const uint8_t *b, St *s) {
    memset(s, 0, sizeof *s);
    for (int i = 0; i < N; i++) if (b[i]) s->w[i >> 6] |= 1ULL << (i & 63);
}

/* 頂点 a の左右の block を比べ、左 > 右 なら入れ替える。 */
static inline void fix(uint8_t *b, int a) {
    int l = lch[a], r = rch[a], m = blen[l];
    int c = memcmp(b + l, b + r, (size_t)m);
    if (c > 0) {
        uint8_t tmp[MAXN];
        memcpy(tmp, b + l, (size_t)m);
        memcpy(b + l, b + r, (size_t)m);
        memcpy(b + r, tmp, (size_t)m);
    }
}

/* 正準形かどうか（検査用） */
static int is_canon(const uint8_t *b) {
    for (int a = 0; a < N; a++) if (lch[a] >= 0 && memcmp(b + lch[a], b + rch[a], (size_t)blen[lch[a]]) > 0) return 0;
    return 1;
}

static inline uint64_t hst(const St *s) {
    uint64_t h = 0x243f6a8885a308d3ULL;
    for (int i = 0; i < WORDS; i++) {
        h ^= s->w[i] + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
        h *= 0xff51afd7ed558ccdULL; h ^= h >> 32;
    }
    h *= 0xc4ceb9fe1a85ec53ULL; h ^= h >> 29;
    return h;
}
static inline int steq(const St *a, const St *b) { return memcmp(a, b, sizeof *a) == 0; }
static inline int stcmp(const void *x, const void *y) { return memcmp(x, y, sizeof(St)); }

/* ---- 集合: ロック分割の開番地法。区画ごとに配列と使用フラグ ---- */
#define NPART 8192
typedef struct { St *k; uint8_t *used; uint64_t cap, cnt; omp_lock_t lk; } Part;
typedef struct { Part p[NPART]; } HSet;

static HSet *hs_new(void) {
    HSet *s = malloc(sizeof *s);
    if (!s) fail("oom");
    for (int i = 0; i < NPART; i++) {
        s->p[i].cap = 8; s->p[i].cnt = 0;
        s->p[i].k = malloc(8 * sizeof(St)); s->p[i].used = calloc(8, 1);
        if (!s->p[i].k || !s->p[i].used) fail("oom");
        omp_init_lock(&s->p[i].lk);
    }
    return s;
}
static void hs_del(HSet *s) {
    for (int i = 0; i < NPART; i++) { free(s->p[i].k); free(s->p[i].used); omp_destroy_lock(&s->p[i].lk); }
    free(s);
}
static uint64_t hs_count(HSet *s) { uint64_t c = 0; for (int i = 0; i < NPART; i++) c += s->p[i].cnt; return c; }
static uint64_t hs_bytes(HSet *s) { uint64_t c = 0; for (int i = 0; i < NPART; i++) c += s->p[i].cap * (sizeof(St) + 1); return c; }

static int hs_has(HSet *s, const St *x, uint64_t h) {
    Part *p = &s->p[h % NPART];
    uint64_t mask = p->cap - 1, i = (h / NPART) & mask;
    while (p->used[i]) {
        if (steq(&p->k[i], x)) return 1;
        i = (i + 1) & mask;
    }
    return 0;
}

static void part_grow(Part *p) {
    uint64_t nc = p->cap * 2, mask = nc - 1;
    St *k = malloc(nc * sizeof(St)); uint8_t *u = calloc(nc, 1);
    if (!k || !u) fail("oom");
    for (uint64_t i = 0; i < p->cap; i++) {
        if (!p->used[i]) continue;
        uint64_t j = (hst(&p->k[i]) / NPART) & mask;
        while (u[j]) j = (j + 1) & mask;
        k[j] = p->k[i]; u[j] = 1;
    }
    free(p->k); free(p->used); p->k = k; p->used = u; p->cap = nc;
}

static int hs_add(HSet *s, const St *x, uint64_t h) {
    Part *p = &s->p[h % NPART];
    omp_set_lock(&p->lk);
    if (4 * (p->cnt + 1) > 3 * p->cap) part_grow(p);
    uint64_t mask = p->cap - 1, i = (h / NPART) & mask;
    int added = 0;
    for (;;) {
        if (!p->used[i]) { p->k[i] = *x; p->used[i] = 1; p->cnt++; added = 1; break; }
        if (steq(&p->k[i], x)) break;
        i = (i + 1) & mask;
    }
    omp_unset_lock(&p->lk);
    return added;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s H P [--threads N] [--stop-at-goal 0|1] [--maxdepth D] [--layers FILE]\n", argv[0]); return 2; }
    H = atoi(argv[1]); P = atoi(argv[2]);
    int nth = 0, stop = 1; long maxd = -1; const char *lp = NULL;
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "--threads") && i + 1 < argc) nth = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--stop-at-goal") && i + 1 < argc) stop = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--maxdepth") && i + 1 < argc) maxd = atol(argv[++i]);
        else if (!strcmp(argv[i], "--layers") && i + 1 < argc) lp = argv[++i];
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }
    if (H < 1 || H > 8) fail("H must be 1..8");
    if (nth > 0) omp_set_num_threads(nth);
    N = (1 << H) - 1;
    layout(0, H, -1);
    FILE *lf = lp ? fopen(lp, "w") : NULL;
    if (lp && !lf) fail("cannot open layers file");
    printf("# fbfs_b H=%d P=%d N=%d threads=%d\n", H, P, N, omp_get_max_threads());
    fflush(stdout);

    St start, goal;
    memset(&start, 0, sizeof start);
    { uint8_t b[MAXN] = {0}; b[0] = 1; pack(b, &goal); }

    double t0 = wall();
    HSet *prev = hs_new(), *cur = hs_new();
    hs_add(cur, &start, hst(&start));
    long d = 0, gd = steq(&start, &goal) ? 0 : -1;
    uint64_t total = 1, big = 1; long bigd = 0;
    if (lf) fprintf(lf, "0 1\n");
    while (hs_count(cur) > 0) {
        if (gd >= 0 && stop) break;
        if (maxd >= 0 && d >= maxd) break;
        HSet *next = hs_new();
        int err = 0, hit = 0;
        #pragma omp parallel reduction(|:err, hit)
        {
            St *nb = malloc(sizeof(St) * (MAXN + 1));
            uint8_t b[MAXN], c[MAXN];
            #pragma omp for schedule(dynamic, 4)
            for (int pi = 0; pi < NPART; pi++) {
                Part *pt = &cur->p[pi];
                for (uint64_t i = 0; i < pt->cap; i++) {
                    if (!pt->used[i]) continue;
                    unpack(&pt->k[i], b);
                    int pc = 0;
                    for (int v = 0; v < N; v++) pc += b[v];
                    if ((pc & 1) != (int)(d & 1)) err |= 1;      /* 二部性の検査 */
                    if (pc > P) err |= 2;
                    if (!is_canon(b)) err |= 4;
                    int nn = 0;
                    for (int v = 0; v < N; v++) {
                        if (lch[v] >= 0 && !(b[lch[v]] && b[rch[v]])) continue; /* 子がそろっていない */
                        if (!b[v] && pc + 1 > P) continue;                      /* 上限 */
                        memcpy(c, b, (size_t)N);
                        c[v] ^= 1;
                        for (int a = par[v]; a >= 0; a = par[a]) fix(c, a);
                        pack(c, &nb[nn++]);
                    }
                    qsort(nb, (size_t)nn, sizeof(St), stcmp);
                    for (int j = 0; j < nn; j++) {
                        if (j > 0 && steq(&nb[j], &nb[j - 1])) continue;
                        uint64_t h = hst(&nb[j]);
                        if (hs_has(prev, &nb[j], h)) continue;
                        if (hs_has(cur, &nb[j], h)) { err |= 8; continue; }    /* 同じ層の隣 = 二部性の破れ */
                        if (hs_add(next, &nb[j], h) && steq(&nb[j], &goal)) hit = 1;
                    }
                }
            }
            free(nb);
        }
        if (err) { fprintf(stderr, "fatal: invariant violated (code %d) at depth %ld\n", err, d); return 3; }
        d++;
        uint64_t ns = hs_count(next);
        total += ns;
        if (ns > big) { big = ns; bigd = d; }
        if (hit && gd < 0) gd = d;
        if (lf) { fprintf(lf, "%ld %lu\n", d, (unsigned long)ns); fflush(lf); }
        if (d % 100 == 0 || hit) {
            printf("# depth %ld layer %lu total %lu sets %.2fGB %.1fs maxrss %ldMB%s\n", d, (unsigned long)ns, (unsigned long)total,
                   (hs_bytes(prev) + hs_bytes(cur) + hs_bytes(next)) / 1e9, wall() - t0, rss_mb(), hit ? " GOAL" : "");
            fflush(stdout);
        }
        hs_del(prev); prev = cur; cur = next;
    }
    int ex = hs_count(cur) == 0;
    printf("RESULT_B H=%d P=%d goal_depth=%ld exhausted=%d last_depth=%ld total_states=%lu max_layer=%lu@%ld time=%.1fs maxrss=%ldMB\n",
           H, P, gd, ex, d, (unsigned long)total, (unsigned long)big, bigd, wall() - t0, rss_mb());
    if (gd < 0) printf("VERDICT_B unreachable%s\n", ex ? " (queue exhausted)" : " (NOT exhausted: truncated)");
    else printf("VERDICT_B M=%ld\n", gd);
    if (lf) fclose(lf);
    return 0;
}
