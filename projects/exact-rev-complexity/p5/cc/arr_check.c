/* 予想 GCC-arr と帰納法の一段 INEQ-arr を森の全数で確かめる.
 *
 * 盤 X の領域（gcc_check.c と同じ）は，「x' の最も近い X の祖先が x」で木（森）の順序をなす．
 * 鎖への並べ方 λ = 領域の線形拡大（下の領域が先）．並べ方 λ で領域を下から順に並べた
 * 長さ Σ|R| の鎖の上で，各領域の頂（下から累積した位置）にペブルがある盤への距離を
 * D_B(λ) と書き，L_B(X) = min_λ D_B(λ) とする．
 *
 * GCC-arr: d_B^Φ(∅,X) >= L_B(X)．（鎖では等号．反鎖の X では L_B = Ψ_B の予想と整合．）
 * INEQ-arr: 有効な (C,c,P,B)（ineq_check.c と同じ）について
 *     1 + L_B^Φ(P) + L_{B-k}^{Φ/C}(P∖C) >= L_B^Φ(C).
 * 環境変数 ARR_MODE=gcc なら GCC-arr だけ，ineq なら INEQ-arr だけ（既定は両方）．
 * ARR_MUTANT=1 なら L を「並べ方の最大」にする変異（GCC-arr が破れるべき）．
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 13
#define INF  (1 << 29)

static int mutant = 0;
static int feas = 1;

/* 鎖の距離表 CD[len][B][mask]（len <= MAXN） */
static int *CD[MAXN + 1][MAXN + 1];

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

static void chain_init(int maxlen) {
    for (int len = 1; len <= maxlen; len++)
        for (int B = 0; B <= maxlen; B++) {
            CD[len][B] = malloc(sizeof(int) * (1u << len));
            chain_bfs(len, B, CD[len][B]);
        }
}

/* 森: 頂点 0..n-1，par[v]（-1 は成分の根），alive マスク（除いた頂点は無い） */
typedef struct {
    int n;
    int par[MAXN];
    uint32_t alive;
} Forest;

/* X の領域と順序から L_B(X) を計算する（全 B を一度に．out[B]） */
static int reg_sz[MAXN], reg_up[MAXN], reg_k, reg_cov;
static int ext_used, ext_pos[MAXN];
static int best[MAXN + 1];
static int cur_order[MAXN];

static void ext_dfs(int depth, int cum, uint32_t mask) {
    if (depth == reg_k) {
        for (int B = 0; B <= MAXN; B++) {
            if (reg_cov == 0) { best[B] = 0; continue; }
            if (B > reg_cov) { /* 予算は長さで頭打ち */
                int d = CD[reg_cov][reg_cov][mask];
                if (mutant ? d > best[B] : d < best[B]) best[B] = d;
                continue;
            }
            int d = CD[reg_cov][B][mask];
            if (mutant) { if (d < INF && (best[B] == INF || d > best[B])) best[B] = d; }
            else if (d < best[B]) best[B] = d;
        }
        return;
    }
    for (int i = 0; i < reg_k; i++) {
        if (ext_used >> i & 1) continue;
        /* i を置けるのは，i の下の領域（reg_up[j]==i）がすべて置かれているとき */
        int ok = 1;
        for (int j = 0; j < reg_k; j++)
            if (reg_up[j] == i && !(ext_used >> j & 1)) { ok = 0; break; }
        if (!ok) continue;
        ext_used |= 1 << i;
        int c2 = cum + reg_sz[i];
        ext_dfs(depth + 1, c2, mask | (1u << (c2 - 1)));
        ext_used &= ~(1 << i);
    }
}

static void Lall(const Forest *F, uint32_t X, int *out) {
    int n = F->n;
    /* 深さ順 */
    int order[MAXN], depth[MAXN], no = 0;
    for (int v = 0; v < n; v++) {
        if (!(F->alive >> v & 1)) { depth[v] = -1; continue; }
        int d = 0, u = v;
        while (F->par[u] >= 0) { u = F->par[u]; d++; }
        depth[v] = d;
    }
    for (int d = 0; d < n; d++)
        for (int v = 0; v < n; v++)
            if (depth[v] == d) order[no++] = v;
    int reg[MAXN], idx[MAXN];
    reg_k = 0;
    for (int v = 0; v < n; v++) idx[v] = -1;
    for (int v = 0; v < n; v++)
        if ((X >> v & 1) && (F->alive >> v & 1)) idx[v] = reg_k++;
    for (int i = 0; i < reg_k; i++) { reg_sz[i] = 0; reg_up[i] = -1; }
    for (int t = 0; t < no; t++) {
        int v = order[t];
        int p = F->par[v];
        int above = p < 0 ? -1 : reg[p]; /* 親の領域（-1 = 覆われない） */
        if (idx[v] >= 0) {
            reg[v] = v;
            reg_up[idx[v]] = above < 0 ? -1 : idx[above];
        } else reg[v] = above;
        if (reg[v] >= 0) reg_sz[idx[reg[v]]]++;
    }
    reg_cov = 0;
    for (int i = 0; i < reg_k; i++) reg_cov += reg_sz[i];
    for (int B = 0; B <= MAXN; B++) best[B] = mutant ? -1 : INF;
    ext_used = 0;
    ext_dfs(0, 0, 0);
    for (int B = 0; B <= MAXN; B++) out[B] = best[B] < 0 ? INF : best[B];
}

static int32_t *fdist[MAXN + 1];

static void forest_bfs(const Forest *F, int B, int32_t *dist) {
    int n = F->n;
    uint32_t need[MAXN];
    memset(need, 0, sizeof need);
    for (int v = 0; v < n; v++)
        if (F->par[v] >= 0 && (F->alive >> v & 1)) need[F->par[v]] |= 1u << v;
    uint32_t N = 1u << n;
    for (uint32_t i = 0; i < N; i++) dist[i] = INF;
    uint32_t *q = malloc(sizeof(uint32_t) * N);
    uint32_t h = 0, t = 0;
    dist[0] = 0;
    q[t++] = 0;
    while (h < t) {
        uint32_t x = q[h++];
        int pc = __builtin_popcount(x);
        for (int v = 0; v < n; v++) {
            uint32_t bit = 1u << v;
            if (!(F->alive & bit)) continue;
            if ((x & need[v]) != need[v]) continue;
            if (!(x & bit) && pc + 1 > B) continue;
            uint32_t y = x ^ bit;
            if (dist[y] == INF) { dist[y] = dist[x] + 1; q[t++] = y; }
        }
    }
    free(q);
}

int main(void) {
    const char *mo = getenv("ARR_MODE");
    int do_gcc = !mo || strcmp(mo, "ineq") != 0;
    int do_ineq = !mo || strcmp(mo, "gcc") != 0;
    const char *mu = getenv("ARR_MUTANT");
    mutant = mu && atoi(mu) == 1;
    const char *fe = getenv("ARR_FEAS");
    feas = !fe || atoi(fe) != 0;
    chain_init(MAXN - 1);
    long id;
    int Nt;
    long gpts = 0, gviol = 0, geq = 0, ipts = 0, iviol = 0, ieq = 0;
    int *Ltab = NULL;
    while (scanf("%ld %d", &id, &Nt) == 2) {
        int par[MAXN + 1];
        for (int i = 1; i < Nt; i++)
            if (scanf("%d", &par[i]) != 1) return 2;
        int n = Nt - 1;
        if (n < 1) continue;
        if (n > MAXN - 1) { fprintf(stderr, "n too big\n"); return 2; }
        Forest F;
        F.n = n;
        F.alive = (1u << n) - 1;
        uint32_t chm[MAXN];
        memset(chm, 0, sizeof chm);
        for (int i = 1; i < Nt; i++) {
            F.par[i - 1] = par[i] - 1;
            if (par[i] > 0) chm[par[i] - 1] |= 1u << (i - 1);
        }
        uint32_t N = 1u << n;
        Ltab = realloc(Ltab, sizeof(int) * N * (MAXN + 1));
        for (uint32_t X = 0; X < N; X++) Lall(&F, X, Ltab + (size_t)X * (MAXN + 1));
        for (int B = 1; B <= n; B++) {
            if (!fdist[B]) fdist[B] = malloc(sizeof(int32_t) * (1u << (MAXN - 1)));
            forest_bfs(&F, B, fdist[B]);
        }
        if (do_gcc) {
            for (int B = 1; B <= n; B++) {
                for (uint32_t X = 1; X < N; X++) {
                    int d = fdist[B][X];
                    if (d >= INF) continue;
                    int L = Ltab[(size_t)X * (MAXN + 1) + B];
                    gpts++;
                    if (d < L) {
                        gviol++;
                        if (gviol <= 10) printf("GCC-arr VIOL id=%ld B=%d X=%x d=%d L=%d\n", id, B, X, d, L);
                    } else if (d == L) geq++;
                }
            }
        }
        if (do_ineq) {
            int Lq[MAXN + 1];
            for (uint32_t C = 1; C < N; C++) {
                int k = __builtin_popcount(C);
                Forest G = F; /* Φ/C */
                G.alive = F.alive & ~C;
                for (int v = 0; v < n; v++)
                    if ((G.alive >> v & 1) && F.par[v] >= 0 && (C >> F.par[v] & 1)) G.par[v] = -1;
                for (int c = 0; c < n; c++) {
                    if (!(C >> c & 1)) continue;
                    uint32_t base = (C & ~(1u << c)) | chm[c];
                    uint32_t freeb = (N - 1) & ~base & ~(1u << c);
                    for (uint32_t sub = freeb;; sub = (sub - 1) & freeb) {
                        uint32_t P = base | sub;
                        int pc = __builtin_popcount(P);
                        int Bmin = pc + 1 > k ? pc + 1 : k;
                        if (Bmin <= n) {
                            Lall(&G, P & ~C, Lq);
                            static int32_t gd[MAXN + 1][1 << (MAXN - 1)];
                            static uint32_t gC = 0xffffffff; static long gid = -1;
                            if (gC != C || gid != id) { for (int b = 0; b <= n; b++) forest_bfs(&G, b, gd[b]); gC = C; gid = id; }
                            for (int B = Bmin; B <= n; B++) {
                                int pre = Ltab[(size_t)P * (MAXN + 1) + B];
                                int post = Lq[B - k];
                                if (pre >= INF || post >= INF) continue;
                                if (feas && (fdist[B][P] >= INF || gd[B - k][P & ~C] >= INF)) continue;
                                int tgt = Ltab[(size_t)C * (MAXN + 1) + B];
                                ipts++;
                                long lhs = 1L + pre + post;
                                if (lhs < tgt) {
                                    iviol++;
                                    if (iviol <= 10)
                                        printf("INEQ-arr VIOL id=%ld n=%d B=%d C=%x c=%d P=%x pre=%d post=%d tgt=%d\n",
                                               id, n, B, C, c, P, pre, post, tgt);
                                } else if (lhs == tgt) ieq++;
                            }
                        }
                        if (sub == 0) break;
                    }
                }
            }
        }
    }
    printf("TOTAL GCC-arr points=%ld viol=%ld eq=%ld | INEQ-arr points=%ld viol=%ld eq=%ld\n",
           gpts, gviol, geq, ipts, iviol, ieq);
    return (gviol || iviol) ? 1 : 0;
}
