/* closure.py の C 版（2CM(a,b) の有限の証明書．先読みあり＝最適値どうしの比較）.
 *
 * 状態 = 正規化した (D2, DM)．D2 は 2 本の鎖の各盤への最小手数，DM は 1 本の鎖（A の下に B）の各盤への最小手数．
 * 作用 = 予算 β（0..L）の相（min-plus で距離をかける）と，その後に境目（頂を含まない盤を ∞）を入れるか．
 * 正規化: D2 の有限な値の最小 m を両方から引く．DM は −K 未満を −K，K 超を ∞ に丸める（味方に不利な向きだけ）．
 * D2 は K2 を超えたら K2 に下げる（2 本の側を安く見積もる向きなので健全．既定は実質丸めなし）．
 * 判定: 到達しうるすべての状態で DM(∅) <= D2(∅)（D2(∅) が有限のとき）．
 *
 * 使い方: ./closure a b K [maxstates [K2]]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXL 8
#define INF16 32767

static int L, N;
static uint32_t need2[MAXL], needM[MAXL], tops2, topM;

static void relax(int16_t *E, const uint32_t *need, int B) {
    /* E は始点ごとの初期値（予算外は ∞ にしてある）．重み 1 の辺で緩和を不動点まで． */
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int x = 0; x < N; x++) {
            if (E[x] == INF16) continue;
            int pc = __builtin_popcount(x);
            for (int v = 0; v < L; v++) {
                if (((uint32_t)x & need[v]) != need[v]) continue;
                if (!(x >> v & 1) && pc + 1 > B) continue;
                int y = x ^ (1 << v);
                if (E[x] + 1 < E[y]) { E[y] = E[x] + 1; changed = 1; }
            }
        }
    }
}

static void apply(const int16_t *D, int16_t *E, const uint32_t *need, int B, int chk, uint32_t mask) {
    for (int x = 0; x < N; x++) E[x] = (D[x] != INF16 && __builtin_popcount(x) <= B) ? D[x] : INF16;
    relax(E, need, B);
    if (chk)
        for (int x = 0; x < N; x++) if (((uint32_t)x & mask) != mask) E[x] = INF16;
}

/* 状態の保存とハッシュ */
static int16_t *store;
static long nst = 0, cap;
static long *htab;
static long hcap;

static uint64_t hash(const int16_t *s) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < 2 * N; i++) { h ^= (uint16_t)s[i]; h *= 1099511628211ULL; }
    return h;
}

static long insert(const int16_t *s) {
    uint64_t h = hash(s);
    long i = (long)(h & (hcap - 1));
    while (htab[i] >= 0) {
        if (!memcmp(store + htab[i] * 2 * N, s, sizeof(int16_t) * 2 * N)) return -1;
        i = (i + 1) & (hcap - 1);
    }
    if (nst >= cap) return -2;
    memcpy(store + nst * 2 * N, s, sizeof(int16_t) * 2 * N);
    htab[i] = nst;
    return nst++;
}

int main(int argc, char **argv) {
    int a = atoi(argv[1]), b = atoi(argv[2]), K = atoi(argv[3]);
    int K2 = argc > 5 ? atoi(argv[5]) : 30000; /* D2 の正規化した値の上限（超えたら K2 に下げる） */
    cap = argc > 4 ? atol(argv[4]) : 20000000L;
    L = a + b;
    N = 1 << L;
    for (int i = 0; i < a; i++) need2[i] = (i + 1 < a) ? 1u << (i + 1) : 0;
    for (int i = 0; i < b; i++) need2[a + i] = (i + 1 < b) ? 1u << (a + i + 1) : 0;
    tops2 = 1u | (1u << a);
    for (int i = 0; i < L; i++) needM[i] = (i + 1 < L) ? 1u << (i + 1) : 0;
    topM = 1u;
    store = malloc(sizeof(int16_t) * 2 * N * cap);
    hcap = 1;
    while (hcap < 2 * cap) hcap <<= 1;
    htab = malloc(sizeof(long) * hcap);
    if (!store || !htab) { fprintf(stderr, "malloc\n"); return 2; }
    for (long i = 0; i < hcap; i++) htab[i] = -1;
    int16_t s0[2 * MAXL * 64 * 4];
    for (int i = 0; i < 2 * N; i++) s0[i] = INF16;
    s0[0] = 0;
    s0[N] = 0;
    insert(s0);
    long head = 0, rounded = 0, d2big = 0;
    int worst = -INF16;
    int16_t E2[1 << MAXL], EM[1 << MAXL], ns[2 << MAXL];
    while (head < nst) {
        const int16_t *D2 = store + head * 2 * N, *DM = D2 + N;
        for (int B = 0; B <= L; B++)
            for (int chk = 0; chk <= 1; chk++) {
                apply(D2, E2, need2, B, chk, tops2);
                int m = INF16;
                for (int x = 0; x < N; x++) if (E2[x] < m) m = E2[x];
                if (m == INF16) continue;
                apply(DM, EM, needM, B, chk, topM);
                for (int x = 0; x < N; x++) {
                    ns[x] = E2[x] == INF16 ? INF16 : E2[x] - m;
                    if (ns[x] != INF16 && ns[x] > K2) { ns[x] = K2; d2big++; } /* D2 を下げる丸め（敵に有利な向き．健全） */
                    if (EM[x] == INF16) { ns[N + x] = INF16; continue; }
                    int w = EM[x] - m;
                    if (w < -K) { w = -K; rounded++; }
                    else if (w > K) { w = INF16; rounded++; }
                    ns[N + x] = (int16_t)w;
                }
                if (ns[0] != INF16) {
                    int gap = ns[N] == INF16 ? INF16 : ns[N] - ns[0];
                    if (gap > worst) worst = gap;
                    if (gap > 0) {
                        printf("a=%d b=%d K=%d: 破れ（丸めの影響かもしれない）gap=%d（状態 %ld 個目から）\n", a, b, K, gap, head);
                        return 1;
                    }
                }
                long r = insert(ns);
                if (r == -2) {
                    printf("a=%d b=%d K=%d: 状態の上限 %ld に達した（打ち切り．結果ではない）\n", a, b, K, cap);
                    return 3;
                }
            }
        head++;
        if ((head & ((1 << 20) - 1)) == 0) { fprintf(stderr, "  %ld / %ld\n", head, nst); }
    }
    printf("a=%d b=%d K=%d: 正規化された組 %ld 個で閉じた．DM(∅)−D2(∅) の最大 %d → %s．丸め %ld 回，D2 を K2 に下げた回数 %ld\n",
           a, b, K, nst, worst, worst <= 0 ? "2CM(a,b) が成り立つ（計算機援用の決定）" : "不成立", rounded, d2big);
    return worst <= 0 ? 0 : 1;
}
