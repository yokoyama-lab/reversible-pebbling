/* 2CM(a,b) を「すべての予算の列と境目」について一度に示すための，有限のエネルギーゲーム.
 *
 * 敵（2 本の鎖の手順）と味方（併合した 1 本の鎖）．状態 (y, x)：y は 1 本の鎖の盤，x は 2 本の盤．
 * 1 回ごとに敵は次のどれかを選ぶ:
 *   (手)   2 本の鎖の合法な 1 手 x -> x'．予算 β = max(|x|, |x'|)．
 *          味方は予算 β の中で y から y' へ任意の手数 ℓ >= 0 で動く．エネルギー += 1 - ℓ．
 *   (境目) x が両方の頂を含むとき．味方は予算 |x| の中で頂を含む y' へ動く（ℓ 手）．エネルギー -= ℓ．
 *   (終わり) x = ∅ のとき．味方は y = ∅ でなければならず，エネルギー >= 0 でなければならない．
 * W(y,x) = 味方が勝つのに要る最小のエネルギー（∞ もありうる）．W(∅,∅) <= 0 なら，
 * どんな文脈（相ごとの予算と境目の列，長さは任意）でも OPT_merged <= OPT_two（= 2CM(a,b)）．
 * （実際の相の予算は，その相の中の盤の大きさの最大以上なので，この敵より弱い．味方の手を
 *   敵の各手の直後に置くのは，実際の自由度の一部．よって勝ちは 2CM の十分条件．）
 *
 * 使い方: ./energy a b [order [GP GQ]]   order は無意味（1 本の鎖の形は a+b だけで決まる）．
 *   GP/GQ を与えると，敵の 1 手に対し味方が平均 GP/GQ 手まで使ってよい版（比の版．エネルギーは GQ 倍で数える）．
 * 値は最小不動点（短い手順から順に）で求め，|W| が上限を超えたら ∞ とみなす．
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXL 8
#define INF  1000000
#define NEG  (-1000000)

static int L, a, b;
static int GP = 1, GQ = 1; /* 敵の 1 手で味方は GP/GQ 手まで（比の版）．既定は 1 */
static uint32_t need2[MAXL], needM[MAXL], tops2, topM;
static int *distM[MAXL + 1]; /* distM[β][y*N + y'] */

static void bfs(const uint32_t *need, int B, uint32_t s, int *d) {
    int N = 1 << L;
    for (int i = 0; i < N; i++) d[i] = INF;
    static uint32_t q[1 << MAXL];
    if (__builtin_popcount(s) > B) return;
    int h = 0, t = 0;
    d[s] = 0;
    q[t++] = s;
    while (h < t) {
        uint32_t x = q[h++];
        int pc = __builtin_popcount(x);
        for (int v = 0; v < L; v++) {
            if ((x & need[v]) != need[v]) continue;
            if (!(x >> v & 1) && pc + 1 > B) continue;
            uint32_t y = x ^ (1u << v);
            if (d[y] == INF) { d[y] = d[x] + 1; q[t++] = y; }
        }
    }
}

int main(int argc, char **argv) {
    a = atoi(argv[1]);
    b = atoi(argv[2]);
    int order = argc > 3 ? atoi(argv[3]) : 0;
    if (argc > 5) { GP = atoi(argv[4]); GQ = atoi(argv[5]); }
    L = a + b;
    int N = 1 << L;
    /* 2 本: 0..a-1 が A（0 が頂），a.. が B（a が頂） */
    for (int i = 0; i < a; i++) need2[i] = (i + 1 < a) ? 1u << (i + 1) : 0;
    for (int i = 0; i < b; i++) need2[a + i] = (i + 1 < b) ? 1u << (a + i + 1) : 0;
    tops2 = 1u | (1u << a);
    /* 1 本: 0 が頂，L-1 が底．order は頂点の名前の付け方だけの違いなので同じグラフ（上の長さが a か b か）．
     * ゲームでは 2 本側の頂点と 1 本側の頂点は別の物なので，order は意味を持たない（記録用に残す）． */
    for (int i = 0; i < L; i++) needM[i] = (i + 1 < L) ? 1u << (i + 1) : 0;
    topM = 1u;
    (void)order;
    for (int B = 0; B <= L; B++) {
        distM[B] = malloc(sizeof(int) * N * N);
        for (int y = 0; y < N; y++) bfs(needM, B, y, distM[B] + (size_t)y * N);
    }
    int *W = malloc(sizeof(int) * N * N), *W2 = malloc(sizeof(int) * N * N);
    for (int y = 0; y < N; y++)
        for (int x = 0; x < N; x++)
            W[y * N + x] = (x == 0) ? (y == 0 ? 0 : INF) : NEG;
    int BOUND = 64 * N; /* これを超えたら ∞ */
    for (int it = 0; it < 100000; it++) {
        int changed = 0;
        for (int y = 0; y < N; y++)
            for (int x = 0; x < N; x++) {
                int best = (x == 0) ? (y == 0 ? 0 : INF) : NEG;
                int px = __builtin_popcount(x);
                /* 敵の手 */
                for (int v = 0; v < L && best < INF; v++) {
                    if ((x & need2[v]) != need2[v]) continue;
                    uint32_t x2 = x ^ (1u << v);
                    int beta = px > __builtin_popcount(x2) ? px : __builtin_popcount(x2);
                    const int *d = distM[beta] + (size_t)y * N;
                    int m = INF;
                    for (int y2 = 0; y2 < N; y2++) {
                        if (d[y2] >= INF) continue;
                        int w = W[y2 * N + x2];
                        if (w >= INF) continue;
                        int val = w + GQ * d[y2] - GP;
                        if (val < m) m = val;
                    }
                    if (m > best) best = m;
                }
                /* 境目 */
                if ((x & tops2) == tops2 && best < INF) {
                    const int *d = distM[px] + (size_t)y * N;
                    int m = INF;
                    for (int y2 = 0; y2 < N; y2++) {
                        if (!(y2 & topM) || d[y2] >= INF) continue;
                        int w = W[y2 * N + x];
                        if (w >= INF) continue;
                        int val = w + GQ * d[y2];
                        if (val < m) m = val;
                    }
                    if (m > best) best = m;
                }
                if (best > BOUND) best = INF;
                if (best < NEG) best = NEG;
                W2[y * N + x] = best;
                if (best != W[y * N + x]) changed = 1;
            }
        int *tmp = W; W = W2; W2 = tmp;
        if (!changed) {
            printf("a=%d b=%d: 収束（反復 %d）．W(∅,∅) = %d  → %s\n", a, b, it,
                   W[0], W[0] <= 0 ? "勝ち（この形の模倣で 2CM(a,b) が従う）" : (W[0] >= INF ? "負け（∞）" : "負け（有限の不足）"));
            /* 補助情報: W(∅, x) の最大（有限のもの） */
            int mx = NEG, ninf = 0;
            for (int x = 0; x < N; x++) {
                int w = W[x];
                if (w >= INF) ninf++;
                else if (w > mx) mx = w;
            }
            printf("  W(∅,x) の有限の最大 %d，∞ の x の数 %d / %d\n", mx, ninf, N);
            return W[0] <= 0 ? 0 : 1;
        }
    }
    printf("a=%d b=%d: 収束せず\n", a, b);
    return 2;
}
