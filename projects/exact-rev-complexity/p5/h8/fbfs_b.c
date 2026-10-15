/* fbfs_b.c — M*(T_H, P) の独立の第 2 実装（実装 B）.
 *
 * 実装 A（fbfs.c）と同じ問いを、別の状態表現・別の後継生成で解く。共通なのは
 * 「フロンティア BFS（3 層だけ保持）」という探索の骨格だけで、その正しさの根拠
 * （無向・ペブル数の偶奇で二部）は実行時に検査する（同じ層への辺が出たら停止）。
 *
 * ## 表現（A との違い）
 * A は高さ H-2 の部分木の軌道に id を振って後継表を前計算する。B は id も表も持たない。
 * 状態は「再帰配置」の 2^H-1 ビット列そのもの:
 *     block(T_k) = [根のビット][block(左の T_{k-1})][block(右の T_{k-1})]
 * 正準形 = すべての節点で 左の block <= 右の block（ビット列の辞書式順）。
 * これは Aut(T_H)（各節点での左右の入れ替えが生成する群）の軌道の代表として一意である
 * （下から帰納: 部分木の軌道は (根のビット, 子の軌道の多重集合) で決まり、
 *   多重集合を辞書式に小さい順に並べた列は一意）。
 * 集合に入れる鍵は、正準形でペブルの立つ位置（0..2^H-2）の昇順の列（16 バイト、余りは 0xFF）。
 * P <= 15 を要する（最後のバイトは常に 0xFF で、ハッシュ表ではそれが 0 の枠を空きとみなす）。
 *
 * ## 後継（A との違い）
 * 正準形の上で頂点 v の合法性を直接ビットで調べ（葉は常に合法、内部頂点は 2 つの子の
 * ビットが立っているとき）、置く手はペブル数 < P のときだけ。toggle したあと v の祖先を
 * 下から順にたどり、各祖先で左右の block を比べて左 > 右 なら入れ替える
 * （変わったのは v を含む側だけなので 1 回の上り走査で正準形に戻る）。
 *
 * ## 枝刈り（--noprune で外せる）
 * 祖先 a の左右の block が等しく、v が a の右の block にあるなら v の手は省く。
 * 根拠: a での左右の入れ替え σ は状態を保つ自己同型で、σ(v) は左の block にある。
 * v を toggle した状態と σ(v) を toggle した状態は σ で移り合うので同じ軌道（同じ正準形）。
 * 祖先が複数あっても、省いた v ごとに、そのような祖先のうち最も上のものでの入れ替えを
 * 繰り返せば（毎回その祖先より上の関係は変わらず、最も上の該当祖先は真に下がる）、
 * どの祖先でも右に入らない頂点（代表）に移る。よって後継の軌道の集合は変わらない。
 * 実装は根から降りる再帰（cands）で、等しい兄弟の右側には降りない。空の部分木では
 * 最左の葉だけが残る（空の部分木の兄弟はすべて等しいので、上の規則の特別な場合）。
 * 候補の合法性は打つ直前にもう一度直接調べる。--noprune（全頂点を直接走査）との
 * 層ごとの一致で実測でも確かめる。
 *
 * build: gcc -O3 -march=native -fopenmp -o fbfs_b fbfs_b.c
 * usage: ./fbfs_b <H> <P> [--threads N] [--stop-at-goal 0|1] [--maxdepth D] [--layers FILE] [--noprune]
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
#define KEYLEN 16

static int H, P, N, PRUNE = 1;
static int lch[MAXN], rch[MAXN], par[MAXN], blen[MAXN]; /* blen = その頂点を根とする block の長さ */
static void fail(const char *m) { fprintf(stderr, "fatal: %s\n", m); exit(2); }
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
static long rss_mb(void) { struct rusage r; getrusage(RUSAGE_SELF, &r); return r.ru_maxrss / 1024; }

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

static int leftleaf[MAXN];
static void make_leftleaf(void) {
    for (int v = 0; v < N; v++) { int x = v; while (lch[x] >= 0) x = lch[x]; leftleaf[v] = x; }
}

/* 枝刈りありの候補: 根から降り、等しい兄弟 block の右側には降りない。
 * 空の部分木（sc=0）の中で合法なのは葉に置く手だけで、その葉はすべて同じ軌道（空の部分木の
 * 兄弟はすべて等しい）なので最左の葉だけを候補にする。 */
static int cands(const uint8_t *b, const uint8_t *sc, int a, int pc, int *out, int n) {
    if (sc[a] == 0) { if (pc < P) out[n++] = leftleaf[a]; return n; }
    if (lch[a] < 0) { out[n++] = a; return n; }            /* ペブル済みの葉: 外す手 */
    int l = lch[a], r = rch[a];
    if (b[l] && b[r] && (b[a] || pc < P)) out[n++] = a;
    n = cands(b, sc, l, pc, out, n);
    int same = sc[l] == sc[r] && memcmp(b + l, b + r, (size_t)blen[l]) == 0;
    if (!same) n = cands(b, sc, r, pc, out, n);
    return n;
}

typedef struct { uint8_t p[KEYLEN]; } St; /* ペブルの位置の昇順。余りは 0xFF */

static inline void unpack(const St *s, uint8_t *b, int *pc) {
    memset(b, 0, (size_t)N);
    int c = 0;
    for (int i = 0; i < KEYLEN && s->p[i] != 0xFF; i++) { b[s->p[i]] = 1; c++; }
    *pc = c;
}
static inline void pack(const uint8_t *b, St *s) {
    memset(s->p, 0xFF, KEYLEN);
    int c = 0;
    for (int i = 0; i < N; i += 8) {           /* 8 バイトずつ読み、全部 0 なら飛ばす（b は 256 バイト確保） */
        uint64_t w;
        memcpy(&w, b + i, 8);
        if (!w) continue;
        for (int j = i; j < i + 8 && j < N; j++)
            if (b[j]) { if (c == KEYLEN) fail("too many pebbles for key"); s->p[c++] = (uint8_t)j; }
    }
}

/* 頂点 a の左右の block を比べ、左 > 右 なら入れ替える。 */
static inline void fix(uint8_t *b, int a) {
    int l = lch[a], r = rch[a], m = blen[l];
    if (memcmp(b + l, b + r, (size_t)m) > 0) {
        uint8_t tmp[MAXN];
        memcpy(tmp, b + l, (size_t)m);
        memcpy(b + l, b + r, (size_t)m);
        memcpy(b + r, tmp, (size_t)m);
    }
}

static int is_canon(const uint8_t *b) {
    for (int a = 0; a < N; a++) if (lch[a] >= 0 && memcmp(b + lch[a], b + rch[a], (size_t)blen[lch[a]]) > 0) return 0;
    return 1;
}

static inline uint64_t hst(const St *s) {
    uint64_t x, y;
    memcpy(&x, s->p, 8); memcpy(&y, s->p + 8, 8);
    uint64_t h = x * 0x9e3779b97f4a7c15ULL;
    h ^= (y + 0x632be59bd9b4e019ULL) * 0xc2b2ae3d27d4eb4fULL;
    h ^= h >> 31; h *= 0xff51afd7ed558ccdULL; h ^= h >> 33; h *= 0xc4ceb9fe1a85ec53ULL; h ^= h >> 29;
    return h;
}
static inline int steq(const St *a, const St *b) { return memcmp(a, b, sizeof *a) == 0; }
static int stcmp(const void *x, const void *y) { return memcmp(x, y, sizeof(St)); }

/* ---- 集合: ロック分割の開番地法。空きの枠は p[KEYLEN-1] == 0（有効な鍵では 0xFF） ---- */
#define NPART 8192
#define USED(e) ((e).p[KEYLEN - 1] != 0)
typedef struct { St *k; uint64_t cap, cnt; omp_lock_t lk; } Part;
typedef struct { Part p[NPART]; } HSet;

static HSet *hs_new(void) {
    HSet *s = malloc(sizeof *s);
    if (!s) fail("oom");
    for (int i = 0; i < NPART; i++) {
        s->p[i].cap = 8; s->p[i].cnt = 0;
        s->p[i].k = calloc(8, sizeof(St));
        if (!s->p[i].k) fail("oom");
        omp_init_lock(&s->p[i].lk);
    }
    return s;
}
static void hs_del(HSet *s) {
    for (int i = 0; i < NPART; i++) { free(s->p[i].k); omp_destroy_lock(&s->p[i].lk); }
    free(s);
}
static uint64_t hs_count(HSet *s) { uint64_t c = 0; for (int i = 0; i < NPART; i++) c += s->p[i].cnt; return c; }
static uint64_t hs_bytes(HSet *s) { uint64_t c = 0; for (int i = 0; i < NPART; i++) c += s->p[i].cap * sizeof(St); return c; }

static int hs_has(HSet *s, const St *x, uint64_t h) {
    Part *p = &s->p[h % NPART];
    uint64_t mask = p->cap - 1, i = (h / NPART) & mask;
    while (USED(p->k[i])) {
        if (steq(&p->k[i], x)) return 1;
        i = (i + 1) & mask;
    }
    return 0;
}

static void part_grow(Part *p) {
    uint64_t nc = p->cap * 2, mask = nc - 1;
    St *k = calloc(nc, sizeof(St));
    if (!k) fail("oom");
    for (uint64_t i = 0; i < p->cap; i++) {
        if (!USED(p->k[i])) continue;
        uint64_t j = (hst(&p->k[i]) / NPART) & mask;
        while (USED(k[j])) j = (j + 1) & mask;
        k[j] = p->k[i];
    }
    free(p->k); p->k = k; p->cap = nc;
}

static int hs_add(HSet *s, const St *x, uint64_t h) {
    Part *p = &s->p[h % NPART];
    omp_set_lock(&p->lk);
    if (4 * (p->cnt + 1) > 3 * p->cap) part_grow(p);
    uint64_t mask = p->cap - 1, i = (h / NPART) & mask;
    int added = 0;
    for (;;) {
        if (!USED(p->k[i])) { p->k[i] = *x; p->cnt++; added = 1; break; }
        if (steq(&p->k[i], x)) break;
        i = (i + 1) & mask;
    }
    omp_unset_lock(&p->lk);
    return added;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s H P [--threads N] [--stop-at-goal 0|1] [--maxdepth D] [--layers FILE] [--noprune]\n", argv[0]); return 2; }
    H = atoi(argv[1]); P = atoi(argv[2]);
    int nth = 0, stop = 1; long maxd = -1; const char *lp = NULL;
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "--threads") && i + 1 < argc) nth = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--stop-at-goal") && i + 1 < argc) stop = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--maxdepth") && i + 1 < argc) maxd = atol(argv[++i]);
        else if (!strcmp(argv[i], "--layers") && i + 1 < argc) lp = argv[++i];
        else if (!strcmp(argv[i], "--noprune")) PRUNE = 0;
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }
    if (H < 1 || H > 8) fail("H must be 1..8");
    if (P > KEYLEN - 1) fail("P must be <= 15");
    if (nth > 0) omp_set_num_threads(nth);
    N = (1 << H) - 1;
    layout(0, H, -1);
    make_leftleaf();
    /* 正準性の全数検査は H<=6 で毎状態、H>=7 では 1/16 の標本（時間のため） */
    uint64_t canon_mask = H <= 6 ? 0 : 15;
    FILE *lf = lp ? fopen(lp, "w") : NULL;
    if (lp && !lf) fail("cannot open layers file");
    printf("# fbfs_b H=%d P=%d N=%d prune=%d threads=%d\n", H, P, N, PRUNE, omp_get_max_threads());
    fflush(stdout);

    St start, goal;
    { uint8_t b[MAXN] = {0}; pack(b, &start); b[0] = 1; pack(b, &goal); }

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
            uint8_t b[MAXN + 1] = {0}, c[MAXN + 1] = {0}, sc[MAXN]; /* N 以降は 0 のまま（pack が 8 バイト単位で読む） */
            #pragma omp for schedule(dynamic, 4)
            for (int pi = 0; pi < NPART; pi++) {
                Part *pt = &cur->p[pi];
                for (uint64_t i = 0; i < pt->cap; i++) {
                    if (!USED(pt->k[i])) continue;
                    int pc;
                    unpack(&pt->k[i], b, &pc);
                    if ((pc & 1) != (int)(d & 1)) err |= 1;      /* 二部性の検査 */
                    if (pc > P) err |= 2;
                    if ((hst(&pt->k[i]) & canon_mask) == 0 && !is_canon(b)) err |= 4;
                    int cv[MAXN], ncv = 0;
                    if (PRUNE) {
                        memset(sc, 0, (size_t)N);
                        for (int t = 0; t < KEYLEN && pt->k[i].p[t] != 0xFF; t++)
                            for (int a = pt->k[i].p[t]; a >= 0; a = par[a]) sc[a]++;
                        ncv = cands(b, sc, 0, pc, cv, 0);
                    } else {
                        for (int v = 0; v < N; v++) {
                            if (lch[v] >= 0 && !(b[lch[v]] && b[rch[v]])) continue; /* 子がそろっていない */
                            if (!b[v] && pc + 1 > P) continue;                      /* 上限 */
                            cv[ncv++] = v;
                        }
                    }
                    int nn = 0;
                    for (int t = 0; t < ncv; t++) {
                        int v = cv[t];
                        /* 合法性はここでもう一度直接調べる（候補の列挙の誤りで不合法な手を打たない） */
                        if (lch[v] >= 0 && !(b[lch[v]] && b[rch[v]])) { err |= 16; continue; }
                        if (!b[v] && pc + 1 > P) { err |= 16; continue; }
                        memcpy(c, b, (size_t)N);
                        c[v] ^= 1;
                        for (int a = par[v]; a >= 0; a = par[a]) fix(c, a);
                        pack(c, &nb[nn++]);
                    }
                    for (int x = 1; x < nn; x++) {           /* 挿入整列（nn は小さい） */
                        St t = nb[x]; int y = x - 1;
                        while (y >= 0 && stcmp(&nb[y], &t) > 0) { nb[y + 1] = nb[y]; y--; }
                        nb[y + 1] = t;
                    }
                    for (int j = 0; j < nn; j++) {
                        if (j > 0 && steq(&nb[j], &nb[j - 1])) continue;
                        uint64_t h = hst(&nb[j]);
                        if (hs_has(prev, &nb[j], h)) continue;
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
    printf("RESULT_B H=%d P=%d prune=%d goal_depth=%ld exhausted=%d last_depth=%ld total_states=%lu max_layer=%lu@%ld time=%.1fs maxrss=%ldMB\n",
           H, P, PRUNE, gd, ex, d, (unsigned long)total, (unsigned long)big, bigd, wall() - t0, rss_mb());
    if (gd < 0) printf("VERDICT_B unreachable%s\n", ex ? " (queue exhausted)" : " (NOT exhausted: truncated)");
    else printf("VERDICT_B M=%ld\n", gd);
    if (lf) fclose(lf);
    return 0;
}
