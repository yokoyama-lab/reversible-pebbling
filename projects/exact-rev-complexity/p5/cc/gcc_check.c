/* 予想 GCC（多目標の鎖比較）を森の全数探索で確かめる.
 *
 * 森 Φ（頂点数 n），盤 C（Φ の各成分の根をすべて含む），予算 B について
 *     d_B(∅, C) >= Σ_{i=1}^{k} F_c(m_i, B-i+1)
 * ここで m_1 >= m_2 >= ... >= m_k は C が Φ を分ける「領域」の頂点数（頂点 v の領域は
 * v の祖先（v 自身を含む）のうち C に入る最も近いもの），k = |C|．F_c は鎖の Knill の再帰．
 * C = {根} の 1 成分の森ではこれは予想 CC そのもの．
 *
 * 入力（標準入力）: p5/fm の木の形式 "id N p_1 ... p_{N-1}"（頂点 0 が根）．根 0 を取り除いた
 * 森（頂点 1..N-1，n = N-1）を調べる．
 * 出力: 木ごとに破れの数，最後に合計．環境変数 GCC_MODE で右辺を変える:
 *   sorted  （既定）上の式（大きい領域に大きい予算）
 *   mutant  右辺を Σ F_c(m_i + 1, B-i+1) にする変異（検出力の確認用．破れが出るべき）
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 24
#define INF  (1L << 40)

static long FC[MAXN + 2][MAXN + 2];

static void fc_init(void) {
    for (int b = 0; b <= MAXN + 1; b++) FC[0][b] = 0;
    for (int m = 1; m <= MAXN + 1; m++) FC[m][0] = INF;
    for (int b = 1; b <= MAXN + 1; b++) {
        FC[1][b] = 1;
        for (int m = 2; m <= MAXN + 1; m++) {
            long best = INF;
            for (int k = 1; k < m; k++) {
                long v = FC[k][b] + FC[k][b - 1] + FC[m - k][b - 1];
                if (v < best) best = v;
            }
            FC[m][b] = best >= INF ? INF : best;
        }
    }
}

static int32_t *dist;
static uint32_t *queue_;

static void bfs(int n, const uint32_t *need, int B) {
    uint32_t N = 1u << n;
    for (uint32_t i = 0; i < N; i++) dist[i] = -1;
    uint32_t head = 0, tail = 0;
    dist[0] = 0;
    queue_[tail++] = 0;
    while (head < tail) {
        uint32_t x = queue_[head++];
        int d = dist[x];
        int pc = __builtin_popcount(x);
        for (int v = 0; v < n; v++) {
            uint32_t bit = 1u << v;
            if ((x & need[v]) != need[v]) continue;
            if (!(x & bit) && pc + 1 > B) continue;
            uint32_t y = x ^ bit;
            if (dist[y] < 0) {
                dist[y] = d + 1;
                queue_[tail++] = y;
            }
        }
    }
}

static int cmpdesc(const void *a, const void *b) { return *(const int *)b - *(const int *)a; }

int main(void) {
    const char *mo = getenv("GCC_MODE");
    int mutant = mo && strcmp(mo, "mutant") == 0;
    fc_init();
    dist = malloc(sizeof(int32_t) * (1u << MAXN));
    queue_ = malloc(sizeof(uint32_t) * (1u << MAXN));
    long id;
    int Nt;
    long tot_pts = 0, tot_viol = 0, tot_eq = 0, tot_trees = 0;
    while (scanf("%ld %d", &id, &Nt) == 2) {
        int par[MAXN + 1];
        par[0] = -1;
        for (int i = 1; i < Nt; i++) scanf("%d", &par[i]);
        int n = Nt - 1;
        if (n < 1) continue;
        if (n > MAXN) { fprintf(stderr, "n too big\n"); return 2; }
        /* 森の頂点 i-1 <- 木の頂点 i */
        uint32_t need[MAXN];
        memset(need, 0, sizeof need);
        uint32_t roots = 0;
        int fpar[MAXN];
        for (int i = 1; i < Nt; i++) {
            int p = par[i];
            fpar[i - 1] = p - 1; /* -1 = 成分の根 */
            if (p == 0) roots |= 1u << (i - 1);
            else need[p - 1] |= 1u << (i - 1);
        }
        /* 祖先の順: 親の番号が子より小さいとは限らないので深さで並べる */
        int depth[MAXN], order[MAXN];
        for (int v = 0; v < n; v++) {
            int d = 0, u = v;
            while (fpar[u] >= 0) { u = fpar[u]; d++; }
            depth[v] = d;
        }
        int no = 0;
        for (int d = 0; d < n; d++)
            for (int v = 0; v < n; v++)
                if (depth[v] == d) order[no++] = v;
        long viol = 0;
        tot_trees++;
        for (int B = 1; B <= n; B++) {
            bfs(n, need, B);
            uint32_t N = 1u << n;
            for (uint32_t C = 0; C < N; C++) {
                if ((C & roots) != roots) continue;
                int k = __builtin_popcount(C);
                /* 領域の大きさ */
                int reg[MAXN];
                int sz[MAXN];
                memset(sz, 0, sizeof sz);
                for (int t = 0; t < n; t++) {
                    int v = order[t];
                    if (C >> v & 1) reg[v] = v;
                    else reg[v] = reg[fpar[v]];
                    sz[reg[v]]++;
                }
                int ms[MAXN], nm = 0;
                for (int v = 0; v < n; v++)
                    if (C >> v & 1) ms[nm++] = sz[v];
                qsort(ms, nm, sizeof(int), cmpdesc);
                long bound = 0;
                for (int i = 0; i < nm; i++) {
                    int b = B - i;
                    int m = ms[i] + (mutant ? 1 : 0);
                    long f = (b <= 0) ? INF : FC[m][b];
                    if (f >= INF) { bound = INF; break; }
                    bound += f;
                }
                (void)k;
                tot_pts++;
                long d = dist[C];
                if (d < 0) continue; /* 到達不能 = ∞ */
                if (bound >= INF) {
                    viol++;
                    if (tot_viol + viol <= 10)
                        printf("VIOL(inf) id=%ld B=%d C=%x d=%ld\n", id, B, C, d);
                    continue;
                }
                if (d < bound) {
                    viol++;
                    if (tot_viol + viol <= 10)
                        printf("VIOL id=%ld B=%d C=%x d=%ld bound=%ld\n", id, B, C, d, bound);
                } else if (d == bound) tot_eq++;
            }
        }
        tot_viol += viol;
    }
    printf("TOTAL forests=%ld points=%ld viol=%ld eq=%ld\n", tot_trees, tot_pts, tot_viol, tot_eq);
    return tot_viol ? 1 : 0;
}
