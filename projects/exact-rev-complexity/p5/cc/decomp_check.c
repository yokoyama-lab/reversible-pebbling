/* 多目標の距離の分解（補題 D）の検算と，帰納法の一段 INEQ を P の種類ごとに調べる.
 *
 * 補題 D（最後に「最終的に置かれる」C の元 c で切る）:
 *   d_B(∅,C) = 1 + min_{c,P} [ d_B(∅,P) + d_{B-k}^{Φ/C}(∅, P∖C) ]，
 *   c ∈ C，c ∉ P，P ⊇ (C∖{c}) ∪ ch(c)，|P| <= B-1，k = |C|．
 *   Φ/C は C の頂点を除いた森（C の頂点はずっとペブル済みなので入力として消える）．
 * これをまず全数で確かめる（左辺は Φ の BFS，右辺は Φ と Φ/C の BFS）．
 *
 * INEQ（Ψ 版）: 1 + Ψ_B(P) + Ψ_{B-k}^{Φ/C}(P∖C) >= Ψ_B(C)．
 * P の種類（余分 E = P ∖ ((C∖{c}) ∪ ch(c))）:
 *   cls 0: すべて
 *   cls 1: E = ∅
 *   cls 2: E ⊆ c の真の子孫
 *   cls 3: P が反鎖
 * 各種類について (i) 実現可能な P（両項の真の距離が有限）での INEQ の破れの数，
 * (ii) 最適な分解（等号を与える (c,P)）がその種類の中に無い (Φ,C,B) の数，
 * (iii) その種類の最適な分解の中に INEQ を満たすものが無い (Φ,C,B) の数，を数える．
 * (iii) が 0 の種類があれば，「その種類の最適な分解が常にある」と「その種類で INEQ」の 2 つで GCC が閉じる．
 *
 * 入力: p5/fm の木の形式（根 0 を除いた森）．
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 12
#define INF  (1 << 29)
#define NCLS 4

#define MAXB 64
static long FC[MAXN + 2][MAXB];
static int LA = 1, LB = 0; /* 緩めた仮説: 領域 i の予算 LA*B + LB - i */

static void fc_init(void) {
    for (int b = 0; b < MAXB; b++) FC[0][b] = 0;
    for (int m = 1; m <= MAXN + 1; m++) FC[m][0] = INF;
    for (int b = 1; b < MAXB; b++) {
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

static int cmpdesc(const void *a, const void *b) { return *(const int *)b - *(const int *)a; }

static long psi(int *ms, int nm, int B) {
    qsort(ms, nm, sizeof(int), cmpdesc);
    long s = 0;
    for (int i = 0; i < nm; i++) {
        if (ms[i] == 0) continue;
        if (B < 0) return INF;
        int b = LA * B + LB - i;
        if (b <= 0) return INF;
        if (b >= MAXB) b = MAXB - 1;
        long f = FC[ms[i]][b];
        if (f >= INF) return INF;
        s += f;
    }
    return s;
}

static int n;
static int par[MAXN], order[MAXN];
static uint32_t chm[MAXN], desc[MAXN];

static void bfs(uint32_t alive, const int *pp, int B, int32_t *dist) {
    uint32_t need[MAXN];
    memset(need, 0, sizeof need);
    for (int v = 0; v < n; v++)
        if ((alive >> v & 1) && pp[v] >= 0) need[pp[v]] |= 1u << v;
    uint32_t N = 1u << n;
    for (uint32_t i = 0; i < N; i++) dist[i] = INF;
    static uint32_t q[1 << MAXN];
    uint32_t h = 0, t = 0;
    dist[0] = 0;
    q[t++] = 0;
    while (h < t) {
        uint32_t x = q[h++];
        int pc = __builtin_popcount(x);
        for (int v = 0; v < n; v++) {
            uint32_t bit = 1u << v;
            if (!(alive & bit)) continue;
            if ((x & need[v]) != need[v]) continue;
            if (!(x & bit) && pc + 1 > B) continue;
            uint32_t y = x ^ bit;
            if (dist[y] == INF) { dist[y] = dist[x] + 1; q[t++] = y; }
        }
    }
}

/* 森 (alive, pp) での X の領域の大きさの列から Ψ_B */
static long psiX(uint32_t alive, const int *pp, uint32_t X, int B) {
    int reg[MAXN], sz[MAXN];
    memset(sz, 0, sizeof sz);
    for (int t = 0; t < n; t++) {
        int v = order[t];
        if (!(alive >> v & 1)) { reg[v] = -1; continue; }
        if (X >> v & 1) reg[v] = v;
        else reg[v] = (pp[v] < 0) ? -1 : reg[pp[v]];
        if (reg[v] >= 0) sz[reg[v]]++;
    }
    int ms[MAXN], nm = 0;
    for (int v = 0; v < n; v++) if ((alive >> v & 1) && (X >> v & 1)) ms[nm++] = sz[v];
    return psi(ms, nm, B);
}


/* 鎖への並べ方の下界 L_B(X)（arr_check.c と同じ定義）: X の領域を線形拡大（下の領域が先）の順に
 * 下から並べた鎖で，各領域の頂にペブルがある盤への鎖の距離の最小 */
static int *CD[MAXN + 1][MAXN + 2];
static void chain_bfs(int len, int B, int *dist) {
    uint32_t N = 1u << len;
    for (uint32_t i = 0; i < N; i++) dist[i] = INF;
    uint32_t *q = malloc(sizeof(uint32_t) * N);
    uint32_t h = 0, t = 0;
    dist[0] = 0;
    q[t++] = 0;
    while (h < t) {
        uint32_t x = q[h++];
        int pc = __builtin_popcount(x);
        for (int i = 0; i < len; i++) {
            if (i > 0 && !(x >> (i - 1) & 1)) continue;
            if (!(x >> i & 1) && pc + 1 > B) continue;
            uint32_t y = x ^ (1u << i);
            if (dist[y] == INF) { dist[y] = dist[x] + 1; q[t++] = y; }
        }
    }
    free(q);
}
static void chain_init(void) {
    for (int len = 1; len <= MAXN; len++)
        for (int B = 0; B <= MAXN + 1; B++) {
            CD[len][B] = malloc(sizeof(int) * (1u << len));
            chain_bfs(len, B < len ? B : len, CD[len][B]);
        }
}
static int a_sz[MAXN], a_up[MAXN], a_k, a_cov, a_B, a_best;
static void a_dfs(int depth, int cum, uint32_t mask, int used) {
    if (depth == a_k) {
        int d = a_cov ? CD[a_cov][a_B][mask] : 0;
        if (d < a_best) a_best = d;
        return;
    }
    for (int i = 0; i < a_k; i++) {
        if (used >> i & 1) continue;
        int ok = 1;
        for (int j = 0; j < a_k; j++)
            if (a_up[j] == i && !(used >> j & 1)) { ok = 0; break; }
        if (!ok) continue;
        int c2 = cum + a_sz[i];
        a_dfs(depth + 1, c2, mask | (1u << (c2 - 1)), used | (1 << i));
    }
}
static long arrX(uint32_t alive, const int *pp, uint32_t X, int B) {
    int reg[MAXN], idx[MAXN];
    a_k = 0;
    for (int v = 0; v < n; v++) idx[v] = ((alive >> v & 1) && (X >> v & 1)) ? a_k++ : -1;
    for (int i = 0; i < a_k; i++) { a_sz[i] = 0; a_up[i] = -1; }
    for (int t = 0; t < n; t++) {
        int v = order[t];
        if (!(alive >> v & 1)) { reg[v] = -1; continue; }
        int above = (pp[v] < 0) ? -1 : reg[pp[v]];
        if (idx[v] >= 0) { reg[v] = v; a_up[idx[v]] = above < 0 ? -1 : idx[above]; }
        else reg[v] = above;
        if (reg[v] >= 0) a_sz[idx[reg[v]]]++;
    }
    a_cov = 0;
    for (int i = 0; i < a_k; i++) a_cov += a_sz[i];
    if (B < 0) B = 0;
    a_B = B;
    a_best = INF;
    a_dfs(0, 0, 0, 0);
    return a_best;
}
static int use_arr = 0;
static long boundX(uint32_t alive, const int *pp, uint32_t X, int B) {
    return use_arr ? arrX(alive, pp, X, B) : psiX(alive, pp, X, B);
}

static int32_t D[MAXN + 1][1 << MAXN];
static int32_t D2[MAXN + 1][1 << MAXN];

int main(void) {
    fc_init();
    { const char *a = getenv("LA"), *b = getenv("LB"); if (a) LA = atoi(a); if (b) LB = atoi(b); }
    { const char *bo = getenv("BOUND"); use_arr = bo && strcmp(bo, "arr") == 0; }
    if (use_arr) chain_init();
    long id;
    int Nt;
    long decomp_bad = 0, triples = 0, ruleA_any = 0, ruleA_all = 0;
    long viol[NCLS] = {0}, pts[NCLS] = {0}, noopt[NCLS] = {0}, nogood[NCLS] = {0};
    while (scanf("%ld %d", &id, &Nt) == 2) {
        int tp[MAXN + 2];
        for (int i = 1; i < Nt; i++)
            if (scanf("%d", &tp[i]) != 1) return 2;
        n = Nt - 1;
        if (n < 1) continue;
        if (n > MAXN) return 2;
        memset(chm, 0, sizeof chm);
        for (int i = 1; i < Nt; i++) {
            par[i - 1] = tp[i] - 1;
            if (tp[i] > 0) chm[tp[i] - 1] |= 1u << (i - 1);
        }
        int depth[MAXN];
        for (int v = 0; v < n; v++) {
            int d = 0, u = v;
            while (par[u] >= 0) { u = par[u]; d++; }
            depth[v] = d;
        }
        int no = 0;
        for (int d = 0; d < n; d++)
            for (int v = 0; v < n; v++)
                if (depth[v] == d) order[no++] = v;
        for (int v = 0; v < n; v++) {
            desc[v] = 0;
            for (int u = 0; u < n; u++) {
                int w = par[u];
                while (w >= 0) { if (w == v) { desc[v] |= 1u << u; break; } w = par[w]; }
            }
        }
        uint32_t N = 1u << n, all = N - 1;
        for (int B = 0; B <= n; B++) bfs(all, par, B, D[B]);
        for (uint32_t C = 1; C < N; C++) {
            int k = __builtin_popcount(C);
            int pp2[MAXN];
            for (int v = 0; v < n; v++) pp2[v] = (par[v] >= 0 && (C >> par[v] & 1)) ? -1 : par[v];
            uint32_t alive2 = all & ~C;
            int need2 = 0;
            for (int B = k; B <= n; B++) if (D[B][C] < INF) need2 = 1;
            if (!need2) continue;
            for (int b = 0; b <= n; b++) bfs(alive2, pp2, b, D2[b]);
            for (int B = k; B <= n; B++) {
                if (D[B][C] >= INF) continue;
                triples++;
                long tgt = boundX(all, par, C, B);
                long best = INF;
                int hasopt[NCLS] = {0}, hasgood[NCLS] = {0};
                int minP = 99, minP_any = 0, minP_all = 1;
                for (int c = 0; c < n; c++) {
                    if (!(C >> c & 1)) continue;
                    uint32_t base = (C & ~(1u << c)) | chm[c];
                    if (base >> c & 1) continue;
                    uint32_t freeb = all & ~base & ~(1u << c);
                    for (uint32_t sub = freeb;; sub = (sub - 1) & freeb) {
                        uint32_t P = base | sub;
                        if (__builtin_popcount(P) <= B - 1) {
                            long pre = D[B][P], post = D2[B - k][P & ~C];
                            if (pre < INF && post < INF) {
                                long tot = 1 + pre + post;
                                if (tot < best) best = tot;
                                int cls[NCLS];
                                cls[0] = 1;
                                cls[1] = (sub == 0);
                                cls[2] = ((sub & ~desc[c]) == 0);
                                int anti = 1;
                                for (int v = 0; v < n && anti; v++)
                                    if ((P >> v & 1) && (desc[v] & P)) anti = 0;
                                cls[3] = anti;
                                long lp = boundX(all, par, P, B);
                                long lq = boundX(alive2, pp2, P & ~C, B - k);
                                int ok = (lp >= INF || lq >= INF) ? 1 : (1 + lp + lq >= tgt);
                                for (int j = 0; j < NCLS; j++) {
                                    if (!cls[j]) continue;
                                    pts[j]++;
                                    if (!ok) {
                                        viol[j]++;
                                        if (viol[j] <= 3)
                                            printf("cls%d VIOL id=%ld n=%d B=%d C=%x c=%d P=%x pre=%ld(psi %ld) post=%ld(psi %ld) tgt=%ld d=%d\n",
                                                   j, id, n, B, C, c, P, pre, lp, post, lq, tgt, D[B][C]);
                                    }
                                    if (tot == D[B][C]) {
                                        hasopt[j] = 1;
                                        if (ok) hasgood[j] = 1;
                                    }
                                }
                                if (tot == D[B][C]) {
                                    int pc = __builtin_popcount(P);
                                    if (pc < minP) { minP = pc; minP_any = ok; minP_all = ok; }
                                    else if (pc == minP) { minP_any |= ok; minP_all &= ok; }
                                }
                            }
                        }
                        if (sub == 0) break;
                    }
                }
                if (!minP_any) { ruleA_any++; if (ruleA_any <= 5) printf("RULEA_ANY FAIL id=%ld n=%d B=%d C=%x d=%d\n", id, n, B, C, D[B][C]); }
                if (!minP_all) { ruleA_all++; if (ruleA_all <= 5) printf("RULEA_ALL FAIL id=%ld n=%d B=%d C=%x d=%d\n", id, n, B, C, D[B][C]); }
                if (best != D[B][C]) {
                    decomp_bad++;
                    if (decomp_bad <= 5) printf("DECOMP MISMATCH id=%ld B=%d C=%x d=%d rhs=%ld\n", id, B, C, D[B][C], best);
                }
                for (int j = 0; j < NCLS; j++) {
                    if (!hasopt[j]) noopt[j]++;
                    if (!hasgood[j]) {
                        nogood[j]++;
                        if (nogood[j] <= 3) printf("cls%d NOGOOD id=%ld n=%d B=%d C=%x d=%d tgt=%ld\n", j, id, n, B, C, D[B][C], tgt);
                    }
                }
            }
        }
    }
    printf("triples=%ld decomp_mismatch=%ld ruleA_any_fail=%ld ruleA_all_fail=%ld\n", triples, decomp_bad, ruleA_any, ruleA_all);
    for (int j = 0; j < NCLS; j++)
        printf("cls%d: points=%ld INEQ_viol=%ld  no_opt_in_class=%ld  no_good_opt_in_class=%ld\n",
               j, pts[j], viol[j], noopt[j], nogood[j]);
    return 0;
}
