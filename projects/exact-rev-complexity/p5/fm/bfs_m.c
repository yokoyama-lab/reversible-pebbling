/* 木の persistent 可逆ペブリングの最短手数 M(T,S) を幅優先探索で求める（独立実装）.
 *
 * 入力（標準入力）: 1 行に 1 本の木．"id n p_1 p_2 ... p_{n-1}"（頂点 0 が根，p_i は頂点 i の親）．
 * 出力（標準出力）: "id n M(1) M(2) ... M(n)"．到達不能は -1．
 *
 * 規則: 頂点 v を置く／外す手は v の子がすべてペブル済みのときだけ合法．空の盤から {根} へ．
 *       盤上のペブルは常に S 個以下．
 * S を 1 から上げ，M(T,S) = 2n-1 になったら以後の S も 2n-1 とする
 * （根以外の頂点は少なくとも 1 回置いて 1 回外し，根は 1 回置くので 2n-1 は下界．M は S について非増加）．
 * 環境変数 BFS_ALL_S=1 なら打ち切らずに全 S で探索する（打ち切りの正しさの検査用）．
 * 変異注入: BFS_MUTANT=freeremove なら外す手を無条件に許す（検出されるべき誤り）．
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 24

static int32_t *dist;
static uint32_t *queue_;

static int bfs(int n, const uint32_t *need, int S, int freeremove) {
    uint32_t N = 1u << n;
    for (uint32_t i = 0; i < N; i++) dist[i] = -1;
    uint32_t head = 0, tail = 0;
    dist[0] = 0;
    queue_[tail++] = 0;
    const uint32_t goal = 1u; /* 根 = 頂点 0 だけ */
    while (head < tail) {
        uint32_t x = queue_[head++];
        int d = dist[x];
        if (x == goal) return d;
        int pc = __builtin_popcount(x);
        for (int v = 0; v < n; v++) {
            uint32_t bit = 1u << v;
            int ok;
            if (freeremove && (x & bit)) ok = 1;
            else ok = (x & need[v]) == need[v];
            if (!ok) continue;
            if (!(x & bit) && pc + 1 > S) continue;
            uint32_t y = x ^ bit;
            if (dist[y] < 0) {
                dist[y] = d + 1;
                queue_[tail++] = y;
            }
        }
    }
    return -1;
}

int main(void) {
    const char *all = getenv("BFS_ALL_S");
    int all_s = all && all[0] == '1';
    const char *mu = getenv("BFS_MUTANT");
    int freeremove = mu && strcmp(mu, "freeremove") == 0;
    dist = malloc(sizeof(int32_t) * (1u << MAXN));
    queue_ = malloc(sizeof(uint32_t) * (1u << MAXN));
    if (!dist || !queue_) { fprintf(stderr, "malloc\n"); return 2; }
    long id;
    int n;
    while (scanf("%ld %d", &id, &n) == 2) {
        if (n < 1 || n > MAXN) { fprintf(stderr, "bad n %d\n", n); return 2; }
        uint32_t need[MAXN];
        memset(need, 0, sizeof need);
        for (int i = 1; i < n; i++) {
            int p;
            if (scanf("%d", &p) != 1 || p < 0 || p >= n) { fprintf(stderr, "bad parent\n"); return 2; }
            need[p] |= 1u << i;
        }
        printf("%ld %d", id, n);
        int done = 0;
        for (int S = 1; S <= n; S++) {
            int m;
            if (done && !all_s) m = 2 * n - 1;
            else m = bfs(n, need, S, freeremove);
            if (m == 2 * n - 1) done = 1;
            printf(" %d", m);
        }
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
