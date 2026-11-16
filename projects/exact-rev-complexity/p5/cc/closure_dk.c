/* 2CM の境目の数を限った版（closure_real.c を元に）。u の手は高々 maxP 回（置く，外す，…の順），終わりの判定は k == maxP のときだけ。
 * maxP = 1: u が根（最後に 1 回置くだけ）．maxP = 2: u が根の子（1 回置いて 1 回外す）。
 * 状態 = 正規化した (D2, DM) と β（予算）と u（盤にあるか）。遷移: β±1（u 以外の文脈の手），u の手（境目．置く: β−1，外す: β+1）。
 * DM は −K 未満を −K，K 超を ∞ に丸める（2CM に不利な向き．破れが出たら realizable.py の厳密版で列を確かめる）。
 * 破れを見つけたら列（遷移の種類）を出して止まる。使い方: ./closure_dk a b K maxstates maxP */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXL 10
#define INF16 32767
static int L, N, BMAX;
static uint32_t need2[MAXL], needM[MAXL], tops2, topM;
static void relax(int16_t *E, const uint32_t *need, int B) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int x = 0; x < N; x++) {
            if (E[x] == INF16) continue;
            for (int v = 0; v < L; v++) {
                if (((uint32_t)x & need[v]) != need[v]) continue;
                int y = x ^ (1 << v);
                if (__builtin_popcount(y) > B) continue;
                if (E[x] + 1 < E[y]) { E[y] = E[x] + 1; changed = 1; }
            }
        }
    }
}
static void apply(const int16_t *D, int16_t *E, const uint32_t *need, int lim, uint32_t mask, int nb) {
    for (int x = 0; x < N; x++)
        E[x] = (D[x] != INF16 && __builtin_popcount(x) <= lim && ((uint32_t)x & mask) == mask) ? D[x] : INF16;
    relax(E, need, nb);
}
static int SW; /* 状態の幅（int16 の個数）: 2N + 2 */
static int16_t *store; static long *par; static signed char *act;
static long nst = 0, cap, *htab, hcap;
static uint64_t hash(const int16_t *s) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < SW; i++) { h ^= (uint16_t)s[i]; h *= 1099511628211ULL; }
    return h;
}
static long insert(const int16_t *s, long p, int a) {
    uint64_t h = hash(s);
    long i = (long)(h & (hcap - 1));
    while (htab[i] >= 0) {
        if (!memcmp(store + htab[i] * SW, s, sizeof(int16_t) * SW)) return -1;
        i = (i + 1) & (hcap - 1);
    }
    if (nst >= cap) return -2;
    memcpy(store + nst * SW, s, sizeof(int16_t) * SW);
    par[nst] = p; act[nst] = (signed char)a;
    htab[i] = nst;
    return nst++;
}
static void printpath(long k, int lastact) {
    long st[100000]; int n = 0;
    for (long q = k; q >= 0 && n < 100000; q = par[q]) st[n++] = q;
    long root = st[n - 1];
    printf("start beta=%d; moves:", store[root * SW + 2 * N]);
    for (int i = n - 2; i >= 0; i--) printf(" %c", "UDP"[act[st[i]]]);
    printf(" %c\n", "UDP"[lastact]);
}
int main(int argc, char **argv) {
    int a = atoi(argv[1]), b = atoi(argv[2]), K = atoi(argv[3]);
    int maxP = argc > 5 ? atoi(argv[5]) : 1;
    cap = argc > 4 ? atol(argv[4]) : 20000000L;
    L = a + b; N = 1 << L; BMAX = L; SW = 2 * N + 2;
    for (int i = 0; i < a; i++) need2[i] = (i + 1 < a) ? 1u << (i + 1) : 0;
    for (int i = 0; i < b; i++) need2[a + i] = (i + 1 < b) ? 1u << (a + i + 1) : 0;
    tops2 = 1u | (1u << a);
    for (int i = 0; i < L; i++) needM[i] = (i + 1 < L) ? 1u << (i + 1) : 0;
    topM = 1u;
    store = malloc(sizeof(int16_t) * SW * cap); par = malloc(sizeof(long) * cap); act = malloc(cap);
    hcap = 1; while (hcap < 2 * cap) hcap <<= 1;
    htab = malloc(sizeof(long) * hcap);
    if (!store || !htab || !par || !act) { fprintf(stderr, "malloc\n"); return 2; }
    for (long i = 0; i < hcap; i++) htab[i] = -1;
    int16_t *s0 = malloc(sizeof(int16_t) * SW), *ns = malloc(sizeof(int16_t) * SW);
    int16_t E2[1 << MAXL], EM[1 << MAXL], Z[1 << MAXL];
    for (int b0 = 0; b0 <= BMAX; b0++) {
        for (int x = 0; x < N; x++) Z[x] = x == 0 ? 0 : INF16;
        apply(Z, E2, need2, b0, 0, b0); apply(Z, EM, needM, b0, 0, b0);
        memcpy(s0, E2, sizeof(int16_t) * N); memcpy(s0 + N, EM, sizeof(int16_t) * N);
        s0[2 * N] = b0; s0[2 * N + 1] = 0;
        insert(s0, -1, 0);
    }
    long head = 0; int worst = -INF16;
    while (head < nst) {
        const int16_t *D2 = store + head * SW, *DM = D2 + N;
        int beta = D2[2 * N], u = D2[2 * N + 1];
        for (int k = 0; k < 3; k++) {
            int nb, nu = u, lim; uint32_t m2 = 0, mM = 0;
            if (k == 0) { nb = beta + 1; lim = beta + 1; if (nb > BMAX) continue; }
            else if (k == 1) { nb = beta - 1; lim = beta - 1; if (nb < 0) continue; }
            else { if (u >= maxP) continue; m2 = tops2; mM = topM; if (u % 2 == 0) { nb = beta - 1; lim = beta - 1; } else { nb = beta + 1; lim = beta; } nu = u + 1;
                   if (nb < 0 || nb > BMAX) continue; }
            apply(D2, E2, need2, lim, m2, nb);
            int m = INF16;
            for (int x = 0; x < N; x++) if (E2[x] < m) m = E2[x];
            if (m == INF16) continue;
            apply(DM, EM, needM, lim, mM, nb);
            for (int x = 0; x < N; x++) {
                ns[x] = E2[x] == INF16 ? INF16 : E2[x] - m;
                if (EM[x] == INF16) { ns[N + x] = INF16; continue; }
                int w = EM[x] - m;
                if (w < -K) w = -K; else if (w > K) w = INF16;
                ns[N + x] = (int16_t)w;
            }
            ns[2 * N] = nb; ns[2 * N + 1] = nu;
            if (ns[0] != INF16 && nu == maxP) {
                int gap = ns[N] == INF16 ? INF16 : ns[N] - ns[0];
                if (gap > worst) worst = gap;
                if (gap > 0) {
                    printf("a=%d b=%d K=%d: 破れ gap=%d（状態 %ld 個目から．丸めの影響の可能性あり→厳密版で確認）\n", a, b, K, gap, head);
                    printpath(head, k);
                    return 1;
                }
            }
            long r = insert(ns, head, k);
            if (r == -2) { printf("a=%d b=%d K=%d: 状態の上限 %ld（打ち切り．結果ではない）worst=%d\n", a, b, K, cap, worst); return 3; }
        }
        head++;
        if ((head & ((1 << 20) - 1)) == 0) fprintf(stderr, "  %ld / %ld\n", head, nst);
    }
    printf("a=%d b=%d K=%d maxP=%d: 状態 %ld 個で閉じた．worst=%d → %s\n", a, b, K, maxP, nst, worst, worst <= 0 ? "成り立つ（計算機援用．丸めは不利な向きのみ）" : "不成立");
    return worst <= 0 ? 0 : 1;
}
