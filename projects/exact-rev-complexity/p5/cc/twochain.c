/* 2 本の鎖の併合の補題 2CM の検査（twochain.py の C 版．相ごとの多始点 BFS で速くした）.
 *
 * 相 j = 0..J-1 の予算 β_j，境目 j（相 j の終わり）が「頂が要る」かどうか chk_j．初めと終わりは空．
 *   two   : 長さ a と b の独立な 2 本の鎖．境目で両方の頂が要る．
 *   merged: 長さ a+b の 1 本（A の底が B の頂を要る）．境目で A の頂だけが要る．
 *   merged2: 逆の順（B が上）．
 * 2CM: OPT_merged <= OPT_two（と OPT_merged2 <= OPT_two）．
 *
 * 使い方:
 *   ./twochain exh L J            a+b = 2..L，相の数 2..J，予算 0..a+b の全列，境目の全部分集合
 *   ./twochain rand L J T seed    a+b <= L，相の数 <= J，T 回の無作為な試行（予算は 0..a+b で一様）
 * 環境変数 TC_MUTANT=1: 併合側の予算を 1 減らす（破れが出るべき）．
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXL 12
#define INF  (1 << 28)

static int L;
static uint32_t need[MAXL];
static uint32_t tops;

static void setup(int kind, int a, int b) {
    L = a + b;
    memset(need, 0, sizeof need);
    if (kind == 0) { /* two: 0..a-1 が A（0 が頂），a..a+b-1 が B（a が頂） */
        for (int i = 0; i < a; i++) need[i] = (i + 1 < a) ? (1u << (i + 1)) : 0;
        for (int i = 0; i < b; i++) need[a + i] = (i + 1 < b) ? (1u << (a + i + 1)) : 0;
        tops = 1u | (1u << a);
    } else { /* merged: 0..L-1 が 1 本（0 が頂） */
        for (int i = 0; i < L; i++) need[i] = (i + 1 < L) ? (1u << (i + 1)) : 0;
        tops = 1u;
    }
}

static int D[1 << MAXL], E[1 << MAXL];

/* 二分ヒープ（距離, 状態） */
static int hk[1 << (MAXL + 4)];
static uint32_t hv[1 << (MAXL + 4)];
static int hn;
static void hpush(int k, uint32_t v) {
    int i = hn++;
    while (i > 0) {
        int p = (i - 1) / 2;
        if (hk[p] <= k) break;
        hk[i] = hk[p]; hv[i] = hv[p]; i = p;
    }
    hk[i] = k; hv[i] = v;
}
static void hpop(int *k, uint32_t *v) {
    *k = hk[0]; *v = hv[0];
    int lk = hk[--hn]; uint32_t lv = hv[hn];
    int i = 0;
    for (;;) {
        int c = 2 * i + 1;
        if (c >= hn) break;
        if (c + 1 < hn && hk[c + 1] < hk[c]) c++;
        if (hk[c] >= lk) break;
        hk[i] = hk[c]; hv[i] = hv[c]; i = c;
    }
    hk[i] = lk; hv[i] = lv;
}

/* 予算 B の下で，状態ごとの初期距離 D から全状態への最短距離 E（重み 1 のダイクストラ） */
static void phase(int B) {
    int N = 1 << L;
    hn = 0;
    for (int x = 0; x < N; x++) {
        E[x] = (D[x] < INF && __builtin_popcount(x) <= B) ? D[x] : INF;
        if (E[x] < INF) hpush(E[x], x);
    }
    while (hn > 0) {
        int k; uint32_t x;
        hpop(&k, &x);
        if (k != E[x]) continue;
        int pc = __builtin_popcount(x);
        for (int v = 0; v < L; v++) {
            if ((x & need[v]) != need[v]) continue;
            if (!(x >> v & 1) && pc + 1 > B) continue;
            uint32_t y = x ^ (1u << v);
            if (k + 1 < E[y]) { E[y] = k + 1; hpush(k + 1, y); }
        }
    }
}

static int opt(int kind, int a, int b, const int *bud, const int *chk, int J, int dec) {
    if (kind == 2) { setup(1, b, a); } else setup(kind, a, b);
    int N = 1 << L;
    for (int x = 0; x < N; x++) D[x] = INF;
    D[0] = 0;
    for (int j = 0; j < J; j++) {
        int B = bud[j] - dec;
        if (B < 0) B = 0;
        phase(B);
        if (j < J - 1 && chk[j])
            for (int x = 0; x < N; x++) if ((x & tops) != tops) E[x] = INF;
        memcpy(D, E, sizeof(int) * N);
    }
    return D[0];
}

static long tot = 0, bad = 0, bad2 = 0, mutdet = 0;
static int mutant = 0;

static void test(int a, int b, const int *bud, const int *chk, int J) {
    int o2 = opt(0, a, b, bud, chk, J, 0);
    if (o2 >= INF) return;
    tot++;
    int om = opt(1, a, b, bud, chk, J, mutant);
    int om2 = opt(2, a, b, bud, chk, J, mutant);
    if (om > o2) {
        bad++;
        if (bad <= 5) {
            printf("VIOL a=%d b=%d two=%d merged=%d bud=", a, b, o2, om);
            for (int j = 0; j < J; j++) printf("%d%s", bud[j], j < J - 1 ? (chk[j] ? "|" : ",") : "\n");
        }
    }
    if (om2 > o2) bad2++;
    if (!mutant) {
        int mm = opt(1, a, b, bud, chk, J, 1);
        if (mm > o2) mutdet++;
    }
}

/* 2 本の鎖の空間で x から y への最短路（予算 B）を path[] に書く．長さを返す（無ければ -1） */
static int bfs_path(int a, int b, uint32_t x, uint32_t y, int B, uint32_t *path) {
    setup(0, a, b);
    int N = 1 << L;
    static int par_[1 << MAXL];
    static uint32_t q[1 << MAXL];
    for (int i = 0; i < N; i++) par_[i] = -2;
    if (__builtin_popcount(x) > B || __builtin_popcount(y) > B) return -1;
    int h = 0, t = 0;
    q[t++] = x; par_[x] = -1;
    while (h < t) {
        uint32_t z = q[h++];
        if (z == y) break;
        int pc = __builtin_popcount(z);
        for (int v = 0; v < L; v++) {
            if ((z & need[v]) != need[v]) continue;
            if (!(z >> v & 1) && pc + 1 > B) continue;
            uint32_t w = z ^ (1u << v);
            if (par_[w] == -2) { par_[w] = z; q[t++] = w; }
        }
    }
    if (par_[y] == -2) return -1;
    int len = 0;
    for (uint32_t z = y; z != x; z = par_[z]) path[len++] = z;
    /* 逆順を正順に */
    for (int i = 0; i < len / 2; i++) { uint32_t tmp = path[i]; path[i] = path[len - 1 - i]; path[len - 1 - i] = tmp; }
    return len;
}

int main(int argc, char **argv) {
    const char *mu = getenv("TC_MUTANT");
    mutant = mu && atoi(mu) == 1;
    if (argc < 2) return 2;
    static int bud[4096], chk[4096];
    if (!strcmp(argv[1], "exh")) {
        int Lmax = atoi(argv[2]), Jmax = atoi(argv[3]);
        for (int LL = 2; LL <= Lmax; LL++)
            for (int a = 1; a < LL; a++) {
                int b = LL - a;
                for (int J = 2; J <= Jmax; J++) {
                    long nb = 1;
                    for (int j = 0; j < J; j++) nb *= (LL + 1);
                    for (long code = 0; code < nb; code++) {
                        long c = code;
                        for (int j = 0; j < J; j++) { bud[j] = c % (LL + 1); c /= (LL + 1); }
                        for (int cm = 1; cm < (1 << (J - 1)); cm++) {
                            for (int j = 0; j < J - 1; j++) chk[j] = cm >> j & 1;
                            test(a, b, bud, chk, J);
                        }
                    }
                }
            }
    } else if (!strcmp(argv[1], "walk")) {
        /* 2 本の鎖の手順を，無作為な境目の盤（両方の頂を含む）を最短路でつないで作り，
         * 1 手ごとに相を切って予算をその手の盤の大きさの最大にする（いちばんきつい予算の列）． */
        int Lmax = atoi(argv[2]), m = atoi(argv[3]);
        long T = atol(argv[4]);
        srand(atoi(argv[5]));
        static uint32_t path[1 << MAXL], seq[4096];
        int bud2[4096], chk2[4096];
        for (long t = 0; t < T; t++) {
            int LL = 2 + rand() % (Lmax - 1);
            int a = 1 + rand() % (LL - 1), b = LL - a;
            int nseq = 0;
            uint32_t cur = 0;
            seq[nseq++] = 0;
            memset(chk2, 0, sizeof chk2);
            int ok = 1;
            int mm = 1 + rand() % m;
            for (int i = 0; i <= mm && ok; i++) {
                uint32_t target;
                if (i < mm) {
                    target = (rand() & ((1u << LL) - 1)) | 1u | (1u << a);
                } else target = 0;
                int B = __builtin_popcount(cur) > __builtin_popcount(target) ? __builtin_popcount(cur) : __builtin_popcount(target);
                B += rand() % 3;
                if (B > LL) B = LL;
                int len = -1;
                for (; B <= LL && len < 0; B++) len = bfs_path(a, b, cur, target, B, path);
                if (len < 0 || nseq + len >= 4000) { ok = 0; break; }
                for (int k = 0; k < len; k++) seq[nseq++] = path[k];
                cur = target;
                chk2[nseq - 1] = (i < mm); /* 印: この盤で境目 */
            }
            if (!ok) continue;
            /* 相 = 1 手ごと: 相 j は seq[j] -> seq[j+1]，予算 = 2 つの盤の大きさの最大 */
            int J = nseq - 1;
            if (J < 2 || J > 4000) continue;
            int cm[4096];
            for (int j = 0; j < nseq; j++) cm[j] = 0;
            /* 境目の印を付け直す（上で chk2 に入れたのは seq の添字） */
            for (int j = 0; j < nseq; j++) cm[j] = 0;
            {
                /* もう一度なぞって境目の添字を集める代わりに，両方の頂を含む盤のうち印のあるものを使う */
            }
            for (int j = 0; j < J; j++) {
                int p1 = __builtin_popcount(seq[j]), p2 = __builtin_popcount(seq[j + 1]);
                bud2[j] = p1 > p2 ? p1 : p2;
            }
            for (int j = 0; j < J - 1; j++) chk[j] = 0;
            int any = 0;
            for (int j = 0; j < J - 1; j++) {
                uint32_t z = seq[j + 1];
                if (chk2[j + 1] && (z & 1u) && (z >> a & 1)) { chk2[j + 1] = 0; any = 1; cm[j] = 1; }
            }
            if (!any) continue;
            static int bb[4096], cc[4096];
            for (int j = 0; j < J; j++) bb[j] = bud2[j];
            for (int j = 0; j < J - 1; j++) cc[j] = cm[j];
            test(a, b, bb, cc, J);
        }
    } else {
        int Lmax = atoi(argv[2]), Jmax = atoi(argv[3]);
        long T = atol(argv[4]);
        srand(atoi(argv[5]));
        for (long t = 0; t < T; t++) {
            int LL = 2 + rand() % (Lmax - 1);
            int a = 1 + rand() % (LL - 1), b = LL - a;
            int J = 2 + rand() % (Jmax - 1);
            int B = rand() % (LL + 1);
            for (int j = 0; j < J; j++) {
                /* 予算は ±1 の歩みと一様の混合 */
                if (rand() % 4 == 0) B = rand() % (LL + 1);
                else { B += (rand() % 3) - 1; if (B < 0) B = 0; if (B > LL) B = LL; }
                bud[j] = B;
            }
            int any = 0;
            for (int j = 0; j < J - 1; j++) { chk[j] = (rand() % 3 == 0); any |= chk[j]; }
            if (!any) chk[rand() % (J - 1)] = 1;
            test(a, b, bud, chk, J);
        }
    }
    printf("finite=%ld viol(A over B)=%ld viol(B over A)=%ld mutant_detected=%ld%s\n", tot, bad, bad2, mutdet,
           mutant ? " [MUTANT RUN]" : "");
    return (bad || bad2) ? 1 : 0;
}
