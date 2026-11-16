/* night74_canonbfs.c -- M*(T_h, p) by BFS in the quotient by Aut(T_h).
 *
 * 第 74 夜（2026-10-07）周 2。目的は第 49 夜 (tools/night49_bitbfs128.py) の
 * M*(T_7,10) = 1001 を **独立の 2 実装目** で再現すること。
 * 第 49 夜のコードは読んでいない。意図的に別物にしてある:
 *
 *   - 状態表現: heap 番号のビットマスクではなく **preorder ブロック符号化**
 *     （index 0 = 部分木の根、[1 .. S(m-1)] = 左部分木、
 *       [1+S(m-1) .. 2 S(m-1)] = 右部分木、S(m) = 2^m - 1）。
 *   - 対称性: 「左右部分木の交換」1 個ではなく、**Aut(T_h) 全体**
 *     （すべての内部頂点での兄弟部分木の交換、位数 2^(2^(h-1)-1)）で
 *     商を取る。各配置を再帰的な正準形へ畳む（子の正準形を降順に並べる）。
 *     Aut は隣接関係・駒数・∅・{根} をすべて保つので、商グラフ上の BFS 距離は
 *     元のグラフの距離に等しい。
 *
 * ゲームの定義（revpebble.py の docstring と同じ）:
 *   葉は free（常に利用可能・駒数に数えない・toggle しない）。
 *   内部頂点 v が toggle 可 ⟺ v の両方の子がペブル済みまたは葉。
 *   ピーク = 内部頂点上の同時ペブル数 ≤ p。clean 終端 = 根のみ。
 *
 * 出力: 各レベルの状態数と順序非依存のフィンガープリント（別実装が
 *       レベル集合を再生して突き合わせられるように）。
 *
 * build: gcc -O2 -o night74_canonbfs night74_canonbfs.c
 * usage: ./night74_canonbfs <h> <p> [max_depth] [levels_out.tsv]
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

/* ---- open addressing hash set of u128 (key 0 means empty slot; 0 = the
 *      empty configuration, handled separately by have_zero) ---------------- */
static u128 *tab;
static u64 tmask, tcnt, tcap;
static int have_zero;

static inline u64 hsh(u128 k)
{
    u64 a = (u64)k, b = (u64)(k >> 64);
    u64 x = a * 0x9E3779B97F4A7C15ULL ^ (b + 0xC2B2AE3D27D4EB4FULL);
    x ^= x >> 29; x *= 0xBF58476D1CE4E5B9ULL; x ^= x >> 32;
    return x;
}

static void tab_alloc(u64 cap)
{
    tab = (u128 *)calloc(cap, sizeof(u128));
    if (!tab) { fprintf(stderr, "OOM table %llu\n", (unsigned long long)cap); exit(2); }
    tcap = cap; tmask = cap - 1;
}

static void tab_grow(void)
{
    u128 *old = tab; u64 oc = tcap, i;
    tab_alloc(oc * 2);
    for (i = 0; i < oc; i++) {
        if (old[i]) {
            u64 j = hsh(old[i]) & tmask;
            while (tab[j]) j = (j + 1) & tmask;
            tab[j] = old[i];
        }
    }
    free(old);
}

/* returns 1 if newly inserted */
static inline int tab_insert(u128 k)
{
    u64 j;
    if (k == 0) { if (have_zero) return 0; have_zero = 1; tcnt++; return 1; }
    j = hsh(k) & tmask;
    while (tab[j]) { if (tab[j] == k) return 0; j = (j + 1) & tmask; }
    tab[j] = k; tcnt++;
    if (tcnt * 10 > tcap * 6) tab_grow();
    return 1;
}

int main(int argc, char **argv)
{
    int m, d, i, maxd;
    u128 *cur, *nxt, goal;
    u64 ncur, nnxt, capn;
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
    /* parents after children is not needed; keep the array for clarity */
    for (i = 0; i < NV; i++) order_idx[i] = i;

    goal = 1;                                   /* only the root pebbled */
    tab_alloc(1ULL << 20);
    have_zero = 0; tcnt = 0;

    capn = 1ULL << 16;
    cur = (u128 *)malloc(capn * sizeof(u128));
    nxt = (u128 *)malloc(capn * sizeof(u128));
    if (!cur || !nxt) { fprintf(stderr, "OOM frontier\n"); return 2; }

    tab_insert(0);
    cur[0] = 0; ncur = 1;

    printf("# h=%d p=%d NV=%d  (preorder encoding, Aut-quotient)\n", H, P, NV);
    if (lf) fprintf(lf, "# h=%d p=%d NV=%d preorder-Aut-quotient\n#depth\tcount\tfingerprint\n", H, P, NV);

    for (d = 0; ; d++) {
        u64 fp = 0, k;
        for (k = 0; k < ncur; k++) fp += hsh(cur[k] ^ 0x5DEECE66DULL) | 1ULL;
        printf("level %d: %llu states (fp=%016llx) total=%llu\n",
               d, (unsigned long long)ncur, (unsigned long long)fp,
               (unsigned long long)tcnt);
        fflush(stdout);
        if (lf) { fprintf(lf, "%d\t%llu\t%016llx\n", d, (unsigned long long)ncur,
                          (unsigned long long)fp); fflush(lf); }

        for (k = 0; k < ncur; k++) if (cur[k] == goal) {
            printf("RESULT h=%d p=%d M=%d states=%llu\n", H, P, d,
                   (unsigned long long)tcnt);
            if (lf) { fprintf(lf, "# RESULT h=%d p=%d M=%d states=%llu\n", H, P, d,
                              (unsigned long long)tcnt); fclose(lf); }
            return 0;
        }
        if (ncur == 0) {
            printf("RESULT h=%d p=%d M=UNREACHABLE states=%llu\n", H, P,
                   (unsigned long long)tcnt);
            if (lf) { fprintf(lf, "# RESULT h=%d p=%d M=UNREACHABLE\n", H, P); fclose(lf); }
            return 0;
        }
        if (d >= maxd) {
            printf("RESULT h=%d p=%d M=>%d (cut at max_depth) states=%llu\n", H, P, d,
                   (unsigned long long)tcnt);
            if (lf) { fprintf(lf, "# RESULT h=%d p=%d M=>%d cut states=%llu\n", H, P, d,
                              (unsigned long long)tcnt); fclose(lf); }
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
                if (tab_insert(c)) {
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
        { u128 *tmp = cur; cur = nxt; nxt = tmp; }
        ncur = nnxt;
    }
}
