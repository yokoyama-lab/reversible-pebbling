/* GCC の帰納法の一段（不等式 INEQ）を，森の全数で確かめる.
 *
 * 記号: 森 Φ（頂点数 n），盤 X ⊆ V(Φ) の「領域」= 各 x ∈ X について，祖先（自身を含む）のうち
 * X に入る最も近いものが x である頂点の集合（X の下に無い頂点は数えない）．
 * Ψ_B(X) = Σ_i F_c(m_i, B-i+1)，m_1 >= m_2 >= ... は X の領域の頂点数（予算 <= 0 の項は ∞）．
 *
 * GCC: d_B(∅,C) >= Ψ_B(C)．
 * 分解（最後に「最終的に置かれる」C の元 c で切る．紙の補題）:
 *   d_B(∅,C) = 1 + min_{c,P} [ d_B(∅,P) + d_{B-k}^{Φ/C}(∅, P∖C) ]，
 *   c ∈ C，c ∉ P，P ⊇ (C∖{c}) ∪ ch(c)，|P| <= B-1，k = |C|，Φ/C は C の頂点を除いた森．
 * INEQ: 上の条件を満たすすべての (C,c,P,B) で
 *   1 + Ψ_B(P) + Ψ_{B-k}^{Φ/C}(P∖C) >= Ψ_B(C)    （左の 2 項が有限のとき）
 * INEQ が成り立てば，GCC は最短手数についての帰納法で従う．
 *
 * Ψ^{Φ/C}(P∖C) の領域: p ∈ P∖C の Φ での P-領域から c を除いたもの（c ∉ P なので c は
 * ある P-領域に入るか，どこにも入らない．C の他の元は P に入るので領域の根）．
 *
 * 入力: p5/fm の木の形式（根 0 を除いた森を調べる）．
 * 環境変数 INEQ_MUTANT=1 で後半の予算を B-k+1 にする（緩めた変異．破れが減る＝検出力の確認は逆向きなので，
 *   INEQ_MUTANT=2 で後半の項を落とす変異（破れが出るべき）を用いる）．
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXN 16
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

static int cmpdesc(const void *a, const void *b) { return *(const int *)b - *(const int *)a; }

static long psi(int *ms, int nm, int B) {
    qsort(ms, nm, sizeof(int), cmpdesc);
    long s = 0;
    for (int i = 0; i < nm; i++) {
        if (ms[i] == 0) continue; /* 空の領域（c だけだった領域を除いた後）は寄与 0 */
        int b = B - i;
        if (b <= 0) return INF;
        long f = FC[ms[i]][b];
        if (f >= INF) return INF;
        s += f;
    }
    return s;
}

static int n, fpar[MAXN], order[MAXN];
static uint32_t chm[MAXN];

/* X の領域の代表を reg[] に入れる（-1 は覆われない） */
static void regions(uint32_t X, int *reg) {
    for (int t = 0; t < n; t++) {
        int v = order[t];
        if (X >> v & 1) reg[v] = v;
        else reg[v] = fpar[v] < 0 ? -1 : reg[fpar[v]];
    }
}

int main(void) {
    const char *mu = getenv("INEQ_MUTANT");
    int mutant = mu ? atoi(mu) : 0;
    const char *pb = getenv("INEQ_P"); int pmode = pb ? atoi(pb) : 0;
    fc_init();
    long id;
    int Nt;
    long pts = 0, viol = 0, eq = 0;
    while (scanf("%ld %d", &id, &Nt) == 2) {
        int par[MAXN + 1];
        for (int i = 1; i < Nt; i++)
            if (scanf("%d", &par[i]) != 1) return 2;
        n = Nt - 1;
        if (n < 1) continue;
        if (n > MAXN) return 2;
        memset(chm, 0, sizeof chm);
        for (int i = 1; i < Nt; i++) {
            fpar[i - 1] = par[i] - 1;
            if (par[i] > 0) chm[par[i] - 1] |= 1u << (i - 1);
        }
        int depth[MAXN];
        for (int v = 0; v < n; v++) {
            int d = 0, u = v;
            while (fpar[u] >= 0) { u = fpar[u]; d++; }
            depth[v] = d;
        }
        int no = 0;
        for (int d = 0; d < n; d++)
            for (int v = 0; v < n; v++)
                if (depth[v] == d) order[no++] = v;
        uint32_t N = 1u << n;
        int reg[MAXN], sz[MAXN], ms[MAXN];
        for (uint32_t C = 1; C < N; C++) {
            int k = __builtin_popcount(C);
            regions(C, reg);
            memset(sz, 0, sizeof sz);
            for (int v = 0; v < n; v++) if (reg[v] >= 0) sz[reg[v]]++;
            int nmC = 0;
            for (int v = 0; v < n; v++) if (C >> v & 1) ms[nmC++] = sz[v];
            int msC[MAXN];
            for (int c = 0; c < n; c++) {
                if (!(C >> c & 1)) continue;
                uint32_t base = (C & ~(1u << c)) | chm[c];
                uint32_t freeb = (N - 1) & ~base & ~(1u << c);
                /* P = base ∪ sub, sub ⊆ freeb */
                for (uint32_t sub = freeb;; sub = (sub - 1) & freeb) {
                    uint32_t P = base | sub;
                    if (pmode == 1 && sub) { if (sub == 0) break; goto next; }
                    if (pmode == 2) { int bad = 0; for (int v = 0; v < n; v++) if (P >> v & 1) { int u = fpar[v]; while (u >= 0) { if (P >> u & 1) bad = 1; u = fpar[u]; } } if (bad) goto next; }
                    int pc = __builtin_popcount(P);
                    int Bmin = pc + 1;
                    if (Bmin < k) Bmin = k;
                    int regP[MAXN], szP[MAXN], szQ[MAXN];
                    regions(P, regP);
                    memset(szP, 0, sizeof szP);
                    memset(szQ, 0, sizeof szQ);
                    for (int v = 0; v < n; v++)
                        if (regP[v] >= 0) {
                            szP[regP[v]]++;
                            if (v != c) szQ[regP[v]]++;
                        }
                    for (int B = Bmin; B <= n; B++) {
                        int a[MAXN], na = 0, q[MAXN], nq = 0;
                        for (int v = 0; v < n; v++) if (P >> v & 1) a[na++] = szP[v];
                        for (int v = 0; v < n; v++) if ((P >> v & 1) && !(C >> v & 1)) q[nq++] = szQ[v];
                        long pre = psi(a, na, B);
                        long post = mutant == 2 ? 0 : psi(q, nq, B - k + (mutant == 1));
                        if (pre >= INF || post >= INF) continue;
                        memcpy(msC, ms, sizeof(int) * nmC);
                        long tgt = psi(msC, nmC, B);
                        pts++;
                        long lhs = 1 + pre + post;
                        if (lhs < tgt) {
                            viol++;
                            if (viol <= 10) {
                                printf("VIOL id=%ld n=%d B=%d C=%x c=%d P=%x pre=%ld post=%ld tgt=%ld\n",
                                       id, n, B, C, c, P, pre, post, tgt);
                            }
                        } else if (lhs == tgt) eq++;
                    }
                next:
                    if (sub == 0) break;
                }
            }
        }
    }
    printf("TOTAL points=%ld viol=%ld eq=%ld\n", pts, viol, eq);
    return viol ? 1 : 0;
}
