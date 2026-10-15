/* fbfs.c — M*(T_H, P) の決定: Aut(T_H) の商グラフ上のフロンティア BFS（実装 A）.
 *
 * ## ゲーム（P5 原稿 §3・code/p5_tree_count.py と同じ）
 * T_H は高さ H の完全二分木（2^H-1 頂点。葉も通常の頂点で、置く・外すに 1 手かかる）。
 * 頂点 v を置く／外す手は v の子がすべてペブル済みのときだけ合法（葉は常に合法）。
 * 同時に置けるペブルは P 個まで。空の盤から根だけの盤へ移る最短手数を M(T_H, P) とする。
 *
 * ## 探索の正しさ（フロンティア BFS が使える理由）
 * (1) 無向: x から y へ v を置く手が合法なら y から x へ v を外す手も合法（v の子は変わらない）。
 * (2) 二部: 1 手でペブル数が ±1 変わるので、深さ d の層のペブル数の偶奇は d と一致する。
 * (3) よって深さ d の状態の隣は深さ d-1 か d+1 にしかなく、L_{d+1} = N(L_d) \ L_{d-1}。
 *     保持するのは 3 層だけでよい（全状態を覚えない）。偶奇は実行時に assert で確かめる。
 * (4) 商: Aut(T_H) は手（合法性・ペブル数）を保つので、軌道の上の BFS の距離は元の距離と一致する
 *     （始点 ∅ と終点 {根} はどちらも Aut 不変）。
 *
 * ## 状態の表現
 * 高さ K=H-2 の部分木の配置は、軌道ごとに正準 id を振る（高さ j の節点 = (b, L, R)、L<=R を
 * hash-cons。高さ 0 は空の木 id=0）。T_H の状態 = (b0, 半分1, 半分2)、半分 = (b, A, B)、A<=B、
 * 半分1 <= 半分2（55 ビットの詰め込み値の大小）。高さ K の軌道は ∅ から ペブル数 <= P で
 * 閉包をとって列挙し、隣接表を前計算する（T_H の到達状態の部分木の射影は必ずこの閉包に入る）。
 *
 * build: gcc -O3 -march=native -fopenmp -o fbfs fbfs.c
 * usage: ./fbfs <H> <P> [--threads N] [--stop-at-goal 0|1] [--maxdepth D] [--layers FILE]
 *   出力: 各層の状態数、ゴール到達の深さ（無ければ "unreachable"）、全状態数、時間、最大常駐。
 *   変異注入はこのファイルのリポジトリ外のコピーに対して行う（mutate.sh）。
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <omp.h>
#include <sys/resource.h>

#define NOID 0xFFFFFFFFu
#define MAXK 12

static int H, P, K;

static void die(const char *m) { fprintf(stderr, "fatal: %s\n", m); exit(2); }
static void *xmalloc(size_t n) { void *p = malloc(n ? n : 1); if (!p) die("out of memory"); return p; }
static void *xcalloc(size_t n, size_t s) { void *p = calloc(n ? n : 1, s); if (!p) die("out of memory"); return p; }
static void *xrealloc(void *q, size_t n) { void *p = realloc(q, n ? n : 1); if (!p) die("out of memory"); return p; }

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static long maxrss_mb(void) { struct rusage r; getrusage(RUSAGE_SELF, &r); return r.ru_maxrss / 1024; }

static inline uint64_t mix64(uint64_t x) {
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    x ^= x >> 31;
    return x;
}

/* ------------------------------------------------------------------------- */
/* 部分木の軌道（高さ 0..K）                                                   */
/* ------------------------------------------------------------------------- */

typedef struct {
    uint32_t *L, *R;
    uint8_t *b, *cnt;
    uint64_t n, cap;
    uint32_t *tab; uint64_t tmask; /* open addressing: id+1, 0=空 */
    /* 隣接（高さ j の後継の id 列）。off[i]..off[i]+len[i] */
    uint64_t *off; uint32_t *len;
    uint32_t *arena; uint64_t an, acap;
} Lev;

static Lev LV[MAXK + 1];

static void lev_init(Lev *v) {
    memset(v, 0, sizeof *v);
    v->tmask = 1023;
    v->tab = xcalloc(v->tmask + 1, 4);
}

static void lev_grow(Lev *v) {
    uint64_t nc = v->cap ? v->cap * 2 : 1024;
    v->L = xrealloc(v->L, nc * 4); v->R = xrealloc(v->R, nc * 4);
    v->b = xrealloc(v->b, nc); v->cnt = xrealloc(v->cnt, nc);
    v->off = xrealloc(v->off, nc * 8); v->len = xrealloc(v->len, nc * 4);
    for (uint64_t i = v->cap; i < nc; i++) v->len[i] = NOID;
    v->cap = nc;
}

static inline uint64_t nodehash(int b, uint32_t L, uint32_t R) {
    return mix64(((uint64_t)L << 32 | R) ^ ((uint64_t)b << 63) ^ 0x9e3779b97f4a7c15ULL);
}

static void lev_rehash(Lev *v) {
    uint64_t ns = (v->tmask + 1) * 2, m = ns - 1;
    uint32_t *t = xcalloc(ns, 4);
    for (uint64_t i = 0; i < v->n; i++) {
        uint64_t h = nodehash(v->b[i], v->L[i], v->R[i]) & m;
        while (t[h]) h = (h + 1) & m;
        t[h] = (uint32_t)(i + 1);
    }
    free(v->tab); v->tab = t; v->tmask = m;
}

/* 高さ j の正準節点 (b, {L,R}) の id。ペブル数が P を超えるなら NOID。 */
static uint32_t node(int j, int b, uint32_t L, uint32_t R) {
    if (L > R) { uint32_t t = L; L = R; R = t; }
    int c = b + (j >= 2 ? LV[j - 1].cnt[L] + LV[j - 1].cnt[R] : 0);
    if (c > P) return NOID;
    Lev *v = &LV[j];
    if ((v->n + 1) * 2 > v->tmask + 1) lev_rehash(v);
    uint64_t h = nodehash(b, L, R) & v->tmask;
    while (v->tab[h]) {
        uint32_t id = v->tab[h] - 1;
        if (v->L[id] == L && v->R[id] == R && v->b[id] == b) return id;
        h = (h + 1) & v->tmask;
    }
    if (v->n >= 0xFFFFFFF0ULL) die("too many nodes");
    if (v->n == v->cap) lev_grow(v);
    uint32_t id = (uint32_t)v->n++;
    v->L[id] = L; v->R[id] = R; v->b[id] = (uint8_t)b; v->cnt[id] = (uint8_t)c;
    v->tab[h] = id + 1;
    return id;
}

/* 高さ j の id が「根がペブル済み」とみなせるか（高さ 0 は空の木 = 入力として常に可）。 */
static inline int avail(int j, uint32_t id) { return j == 0 || LV[j].b[id]; }

/* 高さ j (>=1) の id の後継表を作る（再帰・メモ化）。重複は除く。 */
static void build_succ(int j, uint32_t id);

static void ensure_succ(int j, uint32_t id) {
    if (LV[j].len[id] == NOID) build_succ(j, id);
}

static void build_succ(int j, uint32_t id) {
    Lev *v = &LV[j];
    uint32_t L = v->L[id], R = v->R[id];
    int b = v->b[id];
    /* 一時バッファ（再帰で上書きされないよう局所に確保） */
    uint32_t cap = 64, n = 0;
    uint32_t *buf = xmalloc(cap * 4);
#define PUSH(x) do { if (n == cap) { cap *= 2; buf = xrealloc(buf, cap * 4); } buf[n++] = (x); } while (0)
    /* 根の toggle */
    int ok = avail(j - 1, L) && avail(j - 1, R);
    if (ok) {
        uint32_t t = node(j, 1 - b, L, R);
        if (t != NOID) PUSH(t);
    }
    if (j >= 2) {
        ensure_succ(j - 1, L);
        uint64_t o = LV[j - 1].off[L]; uint32_t ln = LV[j - 1].len[L];
        for (uint32_t k = 0; k < ln; k++) {
            uint32_t t = node(j, b, LV[j - 1].arena[o + k], R);
            if (t != NOID) PUSH(t);
        }
        if (R != L) {
            ensure_succ(j - 1, R);
            o = LV[j - 1].off[R]; ln = LV[j - 1].len[R];
            for (uint32_t k = 0; k < ln; k++) {
                uint32_t t = node(j, b, L, LV[j - 1].arena[o + k]);
                if (t != NOID) PUSH(t);
            }
        }
    }
    /* 重複除去（挿入ソート相当の素朴な方法。n は小さい） */
    uint32_t m = 0;
    for (uint32_t a = 0; a < n; a++) {
        int dup = 0;
        for (uint32_t c = 0; c < m; c++) if (buf[c] == buf[a]) { dup = 1; break; }
        if (!dup) buf[m++] = buf[a];
    }
    v = &LV[j]; /* node() が realloc しうるので取り直す */
    if (v->an + m > v->acap) {
        uint64_t nc = v->acap ? v->acap : 4096;
        while (nc < v->an + m) nc *= 2;
        v->arena = xrealloc(v->arena, nc * 4); v->acap = nc;
    }
    memcpy(v->arena + v->an, buf, m * 4);
    v->off[id] = v->an; v->len[id] = m; v->an += m;
    free(buf);
#undef PUSH
}

/* 高さ K の軌道を ∅ から閉包で列挙し、すべての後継表を作る。 */
static void build_levels(void) {
    for (int j = 0; j <= K; j++) lev_init(&LV[j]);
    /* 高さ 0: 空の木 1 個（id 0）。後継なし。 */
    lev_grow(&LV[0]); LV[0].n = 1; LV[0].L[0] = LV[0].R[0] = 0; LV[0].b[0] = 0; LV[0].cnt[0] = 0;
    LV[0].len[0] = 0; LV[0].off[0] = 0;
    if (K == 0) return;
    /* 空の木 id を各高さで作る */
    uint32_t e = 0;
    for (int j = 1; j <= K; j++) e = node(j, 0, e, e);
    /* 閉包: 高さ K の id を発生順に後継表を作っていく（id は単調に増えるので走査で足りる） */
    for (uint64_t i = 0; i < LV[K].n; i++) ensure_succ(K, (uint32_t)i);
}

/* ------------------------------------------------------------------------- */
/* 上 2 段の状態と層の集合                                                      */
/* ------------------------------------------------------------------------- */

/* 半分 (b, A, B) を 55 ビットに: b<<54 | A<<27 | B（A<=B）。 */
#define IDBITS 27
#define IDMASK ((1ULL << IDBITS) - 1)
static inline uint64_t half_pack(int b, uint32_t A, uint32_t B) {
    if (A > B) { uint32_t t = A; A = B; B = t; }
    return ((uint64_t)b << 54) | ((uint64_t)A << 27) | B;
}
static inline int half_b(uint64_t h) { return (int)(h >> 54) & 1; }
static inline uint32_t half_A(uint64_t h) { return (uint32_t)((h >> 27) & IDMASK); }
static inline uint32_t half_B(uint64_t h) { return (uint32_t)(h & IDMASK); }
static inline int half_cnt(uint64_t h) { return half_b(h) + LV[K].cnt[half_A(h)] + LV[K].cnt[half_B(h)]; }

typedef struct { uint64_t lo, hi; } Key; /* lo = b0<<60 | 半分1, hi = 半分2（半分1 <= 半分2） */

static inline Key mkkey(int b0, uint64_t h1, uint64_t h2) {
    if (h1 > h2) { uint64_t t = h1; h1 = h2; h2 = t; }
    Key k = { ((uint64_t)b0 << 60) | h1, h2 };
    return k;
}
static inline int key_b0(Key k) { return (int)(k.lo >> 60) & 1; }
static inline uint64_t key_h1(Key k) { return k.lo & ((1ULL << 55) - 1); }
static inline uint64_t key_h2(Key k) { return k.hi; }
static inline int key_cnt(Key k) { return key_b0(k) + half_cnt(key_h1(k)) + half_cnt(key_h2(k)); }
static inline uint64_t key_hash(Key k) { return mix64(k.lo * 0x9e3779b97f4a7c15ULL ^ mix64(k.hi + 0x632be59bd9b4e019ULL)); }

/* 分割ハッシュ集合。区画ごとに spinlock。占有は hi の最上位ビットで表す。 */
#define NSHARD 4096
#define OCC (1ULL << 63)
typedef struct {
    Key *t; uint64_t mask, n;
    volatile int lock;
    char pad[64 - sizeof(Key *) - 2 * sizeof(uint64_t) - sizeof(int)];
} Shard;
typedef struct { Shard s[NSHARD]; } Set;

static Set *set_new(void) {
    Set *S = xmalloc(sizeof *S);
    for (int i = 0; i < NSHARD; i++) {
        S->s[i].mask = 15; S->s[i].n = 0; S->s[i].lock = 0;
        S->s[i].t = xcalloc(16, sizeof(Key));
    }
    return S;
}
static void set_free(Set *S) { for (int i = 0; i < NSHARD; i++) free(S->s[i].t); free(S); }
static uint64_t set_size(Set *S) { uint64_t n = 0; for (int i = 0; i < NSHARD; i++) n += S->s[i].n; return n; }
static uint64_t set_bytes(Set *S) { uint64_t n = 0; for (int i = 0; i < NSHARD; i++) n += (S->s[i].mask + 1) * sizeof(Key); return n; }

static inline int shard_of(uint64_t h) { return (int)(h >> 52) & (NSHARD - 1); }

static int set_contains(Set *S, Key k, uint64_t h) {
    Shard *sh = &S->s[shard_of(h)];
    uint64_t i = h & sh->mask;
    uint64_t hi = k.hi | OCC;
    for (;;) {
        Key *e = &sh->t[i];
        if (!(e->hi & OCC)) return 0;
        if (e->hi == hi && e->lo == k.lo) return 1;
        i = (i + 1) & sh->mask;
    }
}

static void shard_grow(Shard *sh) {
    uint64_t ns = (sh->mask + 1) * 2, m = ns - 1;
    Key *t = xcalloc(ns, sizeof(Key));
    for (uint64_t i = 0; i <= sh->mask; i++) {
        Key e = sh->t[i];
        if (!(e.hi & OCC)) continue;
        Key k = { e.lo, e.hi & ~OCC };
        uint64_t j = key_hash(k) & m;
        while (t[j].hi & OCC) j = (j + 1) & m;
        t[j] = e;
    }
    free(sh->t); sh->t = t; sh->mask = m;
}

/* 挿入。新規なら 1。 */
static int set_insert(Set *S, Key k, uint64_t h) {
    Shard *sh = &S->s[shard_of(h)];
    while (__atomic_test_and_set(&sh->lock, __ATOMIC_ACQUIRE)) { while (sh->lock) __builtin_ia32_pause(); }
    if ((sh->n + 1) * 10 > (sh->mask + 1) * 7) shard_grow(sh);
    uint64_t i = h & sh->mask, hi = k.hi | OCC;
    int r = 0;
    for (;;) {
        Key *e = &sh->t[i];
        if (!(e->hi & OCC)) { e->lo = k.lo; e->hi = hi; sh->n++; r = 1; break; }
        if (e->hi == hi && e->lo == k.lo) break;
        i = (i + 1) & sh->mask;
    }
    __atomic_clear(&sh->lock, __ATOMIC_RELEASE);
    return r;
}

/* ------------------------------------------------------------------------- */
/* 後継の生成                                                                   */
/* ------------------------------------------------------------------------- */

/* 半分 h の後継（半分の値と、ペブル数の増分）を列挙。 */
typedef struct { uint64_t h; int d; } HS;

static int half_succ(uint64_t h, HS *out) {
    int b = half_b(h); uint32_t A = half_A(h), B = half_B(h);
    int n = 0;
    Lev *v = &LV[K];
    int ok = avail(K, A) && avail(K, B);
    if (ok) { out[n].h = half_pack(1 - b, A, B); out[n].d = b ? -1 : 1; n++; }
    if (K >= 1) {
        int cA = v->cnt[A];
        for (uint32_t k = 0, ln = v->len[A]; k < ln; k++) {
            uint32_t A2 = v->arena[v->off[A] + k];
            out[n].h = half_pack(b, A2, B); out[n].d = v->cnt[A2] - cA; n++;
        }
        if (B != A) { /* A==B なら B の手は A の手と同じ軌道を作る */
            int cB = v->cnt[B];
            for (uint32_t k = 0, ln = v->len[B]; k < ln; k++) {
                uint32_t B2 = v->arena[v->off[B] + k];
                out[n].h = half_pack(b, A, B2); out[n].d = v->cnt[B2] - cB; n++;
            }
        }
    }
    return n;
}

static int max_half_succ(void) {
    uint32_t m = 0;
    for (uint64_t i = 0; i < LV[K].n; i++) if (LV[K].len[i] > m) m = LV[K].len[i];
    return 2 * (int)m + 2;
}

/* ------------------------------------------------------------------------- */

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s H P [--threads N] [--stop-at-goal 0|1] [--maxdepth D] [--layers FILE]\n", argv[0]); return 2; }
    H = atoi(argv[1]); P = atoi(argv[2]);
    int threads = 0, stop_at_goal = 1; long maxdepth = -1; const char *layers_path = NULL;
    for (int i = 3; i < argc; i++) {
        if (!strcmp(argv[i], "--threads") && i + 1 < argc) threads = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--stop-at-goal") && i + 1 < argc) stop_at_goal = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--maxdepth") && i + 1 < argc) maxdepth = atol(argv[++i]);
        else if (!strcmp(argv[i], "--layers") && i + 1 < argc) layers_path = argv[++i];
        else { fprintf(stderr, "unknown arg %s\n", argv[i]); return 2; }
    }
    if (H < 2 || H - 2 > MAXK) die("H must be in [2, MAXK+2]");
    K = H - 2;
    if (threads > 0) omp_set_num_threads(threads);
    int budget = P;
    double t0 = now();
    build_levels();
    if (LV[K].n > IDMASK) die("too many level-K orbits for 27-bit ids");
    printf("# fbfs H=%d P=%d K=%d threads=%d\n", H, P, K, omp_get_max_threads());
    for (int j = 1; j <= K; j++) printf("# level %d: %lu orbits (cnt<=%d), succ arena %lu\n", j, (unsigned long)LV[j].n, budget, (unsigned long)LV[j].an);
    printf("# build %.1fs maxrss %ldMB\n", now() - t0, maxrss_mb());
    fflush(stdout);

    int mhs = max_half_succ();
    uint32_t e = 0; /* 高さ K の空の木の id は 0（最初に作られる） */
    if (LV[K].n && (LV[K].b[0] || LV[K].cnt[0])) die("empty id is not 0");
    Key start = mkkey(0, half_pack(0, e, e), half_pack(0, e, e));
    Key goal = mkkey(1, half_pack(0, e, e), half_pack(0, e, e));
    FILE *lf = layers_path ? fopen(layers_path, "w") : NULL;
    if (layers_path && !lf) die("cannot open layers file");

    Set *prev = set_new(), *cur = set_new();
    set_insert(cur, start, key_hash(start));
    long depth = 0; long goal_depth = -1;
    uint64_t total = 1;
    uint64_t maxlayer = 1; long maxlayer_d = 0;
    if (lf) fprintf(lf, "0 1\n");
    if (start.lo == goal.lo && start.hi == goal.hi) goal_depth = 0;
    double tl = now();
    while (set_size(cur) > 0) {
        if (goal_depth >= 0 && stop_at_goal) break;
        if (maxdepth >= 0 && depth >= maxdepth) break;
        Set *next = set_new();
        int bad_parity = 0, found = 0;
        #pragma omp parallel reduction(|:bad_parity, found)
        {
            HS *s1 = xmalloc(sizeof(HS) * (mhs + 2));
            HS *s2 = xmalloc(sizeof(HS) * (mhs + 2));
            #pragma omp for schedule(dynamic, 1)
            for (int si = 0; si < NSHARD; si++) {
                Shard *sh = &cur->s[si];
                for (uint64_t i = 0; i <= sh->mask; i++) {
                    Key e2 = sh->t[i];
                    if (!(e2.hi & OCC)) continue;
                    Key x = { e2.lo, e2.hi & ~OCC };
                    int b0 = key_b0(x);
                    uint64_t h1 = key_h1(x), h2 = key_h2(x);
                    int c = b0 + half_cnt(h1) + half_cnt(h2);
                    if ((c & 1) != (depth & 1)) bad_parity = 1;
                    /* 半分 1 の手 */
                    int n1 = half_succ(h1, s1);
                    for (int k = 0; k < n1; k++) {
                        if (c + s1[k].d > budget) continue;
                        Key y = mkkey(b0, s1[k].h, h2);
                        uint64_t hh = key_hash(y);
                        if (set_contains(prev, y, hh)) continue;
                        if (set_insert(next, y, hh) && y.lo == goal.lo && y.hi == goal.hi) found = 1;
                    }
                    /* 半分 2 の手（半分が等しければ半分 1 と同じ軌道を作るので省く） */
                    if (h2 != h1) {
                        int n2 = half_succ(h2, s2);
                        for (int k = 0; k < n2; k++) {
                            if (c + s2[k].d > budget) continue;
                            Key y = mkkey(b0, h1, s2[k].h);
                            uint64_t hh = key_hash(y);
                            if (set_contains(prev, y, hh)) continue;
                            if (set_insert(next, y, hh) && y.lo == goal.lo && y.hi == goal.hi) found = 1;
                        }
                    }
                    /* 根の toggle */
                    int rok = half_b(h1) && half_b(h2);
                    if (rok && !(b0 == 0 && c + 1 > budget)) {
                        Key y = mkkey(1 - b0, h1, h2);
                        uint64_t hh = key_hash(y);
                        if (!set_contains(prev, y, hh)) {
                            if (set_insert(next, y, hh) && y.lo == goal.lo && y.hi == goal.hi) found = 1;
                        }
                    }
                }
            }
            free(s1); free(s2);
        }
        if (bad_parity) die("parity violated: graph is not bipartite as assumed");
        depth++;
        uint64_t ns = set_size(next);
        total += ns;
        if (ns > maxlayer) { maxlayer = ns; maxlayer_d = depth; }
        if (found && goal_depth < 0) goal_depth = depth;
        if (lf) { fprintf(lf, "%ld %lu\n", depth, (unsigned long)ns); fflush(lf); }
        if (depth % 100 == 0 || found) {
            printf("# depth %ld layer %lu total %lu  sets %.2fGB  %.1fs  maxrss %ldMB%s\n", depth, (unsigned long)ns, (unsigned long)total,
                   (set_bytes(prev) + set_bytes(cur) + set_bytes(next)) / 1e9, now() - tl, maxrss_mb(), found ? "  GOAL" : "");
            fflush(stdout);
        }
        set_free(prev); prev = cur; cur = next;
    }
    int exhausted = set_size(cur) == 0;
    printf("RESULT H=%d P=%d goal_depth=%ld exhausted=%d last_depth=%ld total_states=%lu max_layer=%lu@%ld time=%.1fs maxrss=%ldMB\n",
           H, P, goal_depth, exhausted, depth, (unsigned long)total, (unsigned long)maxlayer, maxlayer_d, now() - t0, maxrss_mb());
    if (goal_depth < 0) printf("VERDICT unreachable%s\n", exhausted ? " (queue exhausted)" : " (NOT exhausted: truncated)");
    else printf("VERDICT M=%ld\n", goal_depth);
    if (lf) fclose(lf);
    return 0;
}
