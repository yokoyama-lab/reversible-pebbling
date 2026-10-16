/* night80r2_quotbfs.c — M*(T_h, p) を Aut(T_h) の商グラフ上の BFS で厳密に求める.
 *
 * 第 49 夜の tools/night49_bitbfs128.py とは独立に書いた（コードは読んでいない）。
 * 違い:
 *   - 状態表現: 128 ビットのビットマスクではなく、部分木ごとの正準形を
 *     hash-cons した整数 id（高さ j の節点 = (b, L, R), L <= R）。
 *   - 対称性: 根の左右交換だけでなく Aut(T_h) 全体（反復環積・位数 2^(2^h-1)）で割る。
 *     始点 ∅ も終点 {root} も Aut 不変なので、商の距離は元の距離に一致する。
 *
 * モデル: 葉は free（数えない・toggle しない）。内部頂点 v を toggle できるのは
 * v の両方の子が「ペブル済みまたは葉」のとき。ピーク p は内部頂点上の同時ペブル数。
 *
 * build: gcc -O2 -o night80r2_quotbfs night80r2_quotbfs.c
 * usage: ./night80r2_quotbfs <h> <p> [memo_height]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define NOID 0xFFFFFFFFu
#define INF16 0xFFFFu
#define MAXH 10

static int H, P, MEMO_H;

/* ---- 高さごとの節点表 ---- */
typedef struct {
    uint32_t *L, *R;
    uint8_t *b, *cnt;
    uint64_t n, cap;
    /* hash: slot -> id+1 (0 = empty) */
    uint32_t *slot;
    uint64_t mask; /* size-1, power of two */
    uint64_t used;
    /* succ memo: off/len into arena (memo 対象の高さのみ) */
    uint32_t *soff, *slen;
    uint32_t *arena;
    uint64_t acap, an;
    int memo;
} Level;

static Level LV[MAXH + 1];
static uint16_t *dist_top = NULL; /* 高さ H の節点ごとの距離 */
static uint64_t dist_cap = 0;

static void die(const char *m) { fprintf(stderr, "fatal: %s\n", m); exit(2); }

static void *xrealloc(void *q, size_t n) {
    void *r = realloc(q, n);
    if (!r && n) die("out of memory");
    return r;
}

static void lv_grow(Level *v) {
    uint64_t nc = v->cap ? v->cap * 2 : 1024;
    v->L = xrealloc(v->L, nc * 4);
    v->R = xrealloc(v->R, nc * 4);
    v->b = xrealloc(v->b, nc);
    v->cnt = xrealloc(v->cnt, nc);
    if (v->memo) {
        v->soff = xrealloc(v->soff, nc * 4);
        v->slen = xrealloc(v->slen, nc * 4);
        for (uint64_t i = v->cap; i < nc; i++) v->slen[i] = NOID;
    }
    v->cap = nc;
}

static inline uint64_t mix(uint64_t x) {
    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL;
    x ^= x >> 33;
    return x;
}

static void rehash(Level *v) {
    uint64_t ns = (v->mask + 1) ? (v->mask + 1) * 2 : 1024;
    if (!v->slot) ns = 1024;
    uint32_t *s = xrealloc(NULL, ns * 4);
    memset(s, 0, ns * 4);
    uint64_t m = ns - 1;
    for (uint64_t i = 0; i < v->n; i++) {
        uint64_t hh = mix(((uint64_t)v->L[i] << 33) ^ ((uint64_t)v->R[i] << 1) ^ v->b[i]) & m;
        while (s[hh]) hh = (hh + 1) & m;
        s[hh] = (uint32_t)(i + 1);
    }
    free(v->slot);
    v->slot = s;
    v->mask = m;
}

/* (b,L,R) の正準 id。cnt > P なら NOID。 */
static uint32_t canon(int j, int b, uint32_t L, uint32_t R) {
    if (L > R) { uint32_t t = L; L = R; R = t; }
    Level *c = &LV[j - 1];
    int cnt = b + c->cnt[L] + c->cnt[R];
    if (cnt > P) return NOID;
    Level *v = &LV[j];
    if (!v->slot || (v->used + 1) * 3 > (v->mask + 1) * 2) rehash(v);
    uint64_t hh = mix(((uint64_t)L << 33) ^ ((uint64_t)R << 1) ^ (uint64_t)b) & v->mask;
    while (v->slot[hh]) {
        uint32_t id = v->slot[hh] - 1;
        if (v->L[id] == L && v->R[id] == R && v->b[id] == (uint8_t)b) return id;
        hh = (hh + 1) & v->mask;
    }
    if (v->n == v->cap) lv_grow(v);
    uint32_t id = (uint32_t)v->n++;
    v->L[id] = L; v->R[id] = R; v->b[id] = (uint8_t)b; v->cnt[id] = (uint8_t)cnt;
    v->slot[hh] = id + 1;
    v->used++;
    if (j == H) {
        if (v->cap > dist_cap) {
            dist_top = xrealloc(dist_top, v->cap * 2);
            dist_cap = v->cap;
        }
        dist_top[id] = INF16;
    }
    return id;
}

static inline int avail(int j, uint32_t i) { return j == 0 || LV[j].b[i] == 1; }

/* 高さ j の状態 i の後継を out に書き、個数を返す（重複を含みうる）。 */
static uint32_t scratch[MAXH + 1][256];

static int succ(int j, uint32_t i, uint32_t **out) {
    if (j == 0) { *out = NULL; return 0; }
    Level *v = &LV[j];
    if (v->memo && v->slen[i] != NOID) { *out = v->arena + v->soff[i]; return (int)v->slen[i]; }
    uint32_t L = v->L[i], R = v->R[i];
    int b = v->b[i];
    uint32_t *buf = scratch[j];
    int n = 0;
    if (avail(j - 1, L) && avail(j - 1, R)) {
        uint32_t c = canon(j, 1 - b, L, R);
        if (c != NOID) buf[n++] = c;
    }
    uint32_t *sl; int nl = succ(j - 1, L, &sl);
    /* 子の後継表は canon の最中に arena が realloc されうるので控えを取る */
    uint32_t tmpl[256];
    if (nl) { memcpy(tmpl, sl, nl * 4); }
    for (int k = 0; k < nl; k++) {
        uint32_t c = canon(j, b, tmpl[k], R);
        if (c != NOID) buf[n++] = c;
    }
    uint32_t *sr; int nr = succ(j - 1, R, &sr);
    uint32_t tmpr[256];
    if (nr) { memcpy(tmpr, sr, nr * 4); }
    for (int k = 0; k < nr; k++) {
        uint32_t c = canon(j, b, L, tmpr[k]);
        if (c != NOID) buf[n++] = c;
    }
    if (v->memo) {
        if (v->an + n > v->acap) {
            uint64_t nc = v->acap ? v->acap * 2 : 1 << 16;
            while (nc < v->an + n) nc *= 2;
            v->arena = xrealloc(v->arena, nc * 4);
            v->acap = nc;
        }
        memcpy(v->arena + v->an, buf, n * 4);
        v->soff[i] = (uint32_t)v->an;
        v->slen[i] = (uint32_t)n;
        v->an += n;
        *out = v->arena + v->soff[i];
        return n;
    }
    *out = buf;
    return n;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s h p [memo_height]\n", argv[0]); return 2; }
    H = atoi(argv[1]);
    P = atoi(argv[2]);
    MEMO_H = (argc > 3) ? atoi(argv[3]) : H - 1;
    if (H < 1 || H > MAXH) die("h out of range");

    for (int j = 0; j <= H; j++) {
        memset(&LV[j], 0, sizeof(Level));
        LV[j].memo = (j >= 1 && j <= MEMO_H);
    }
    /* 高さ 0 = 葉: id 0 のみ、cnt 0 */
    lv_grow(&LV[0]);
    LV[0].n = 1; LV[0].L[0] = NOID; LV[0].R[0] = NOID; LV[0].b[0] = 0; LV[0].cnt[0] = 0;

    uint32_t empty[MAXH + 1];
    empty[0] = 0;
    for (int j = 1; j <= H; j++) empty[j] = canon(j, 0, empty[j - 1], empty[j - 1]);
    uint32_t start = empty[H];
    uint32_t goal = canon(H, 1, empty[H - 1], empty[H - 1]);
    if (goal == NOID) { printf("{\"h\":%d,\"p\":%d,\"M\":null,\"reason\":\"goal over p\"}\n", H, P); return 0; }

    uint32_t *cur = xrealloc(NULL, 1024 * 4), *nxt = xrealloc(NULL, 1024 * 4);
    uint64_t ccap = 1024, ncap = 1024, cn = 0, nn = 0;
    dist_top[start] = 0;
    cur[cn++] = start;
    uint64_t visited = 1;
    int d = 0, ans = -1;
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    while (cn && ans < 0) {
        d++;
        nn = 0;
        for (uint64_t ii = 0; ii < cn && ans < 0; ii++) {
            uint32_t s = cur[ii];
            uint32_t *o; int n = succ(H, s, &o);
            uint32_t tmp[256];
            memcpy(tmp, o, n * 4);
            for (int k = 0; k < n; k++) {
                uint32_t t = tmp[k];
                if (dist_top[t] == INF16) {
                    dist_top[t] = (uint16_t)d;
                    visited++;
                    if (t == goal) { ans = d; break; }
                    if (nn == ncap) { ncap *= 2; nxt = xrealloc(nxt, ncap * 4); }
                    nxt[nn++] = t;
                }
            }
        }
        uint32_t *sw = cur; cur = nxt; nxt = sw;
        uint64_t sc = ccap; ccap = ncap; ncap = sc;
        cn = nn;
        if (d % 50 == 0) {
            clock_gettime(CLOCK_MONOTONIC, &t1);
            fprintf(stderr, "  depth %d  visited %llu  nodes[H] %llu  %.1fs\n", d,
                    (unsigned long long)visited, (unsigned long long)LV[H].n,
                    (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec));
            fflush(stderr);
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double dt = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
    if (ans < 0)
        printf("{\"h\":%d,\"p\":%d,\"M\":null,\"states\":%llu,\"seconds\":%.2f}\n", H, P,
               (unsigned long long)visited, dt);
    else
        printf("{\"h\":%d,\"p\":%d,\"M\":%d,\"states\":%llu,\"nodesH\":%llu,\"seconds\":%.2f}\n",
               H, P, ans, (unsigned long long)visited, (unsigned long long)LV[H].n, dt);
    fflush(stdout);
    return 0;
}
