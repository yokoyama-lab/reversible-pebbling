// h=4 (n=15), 上限 c．前向き BFS（空から）と後ろ向き BFS（根だけペブル・幽霊なしへ）で最短手順の DAG を作り，
// 最短手順を乱択で N 本出す（各手で最短 DAG 上の後続を一様に選ぶ）．規則は QL（ghost は無条件）．
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, cap; static uint32_t pw[32], N;
static int dig(uint32_t s, int i) { return (s / pw[i]) % 3; }
static int npb(uint32_t s) { int c = 0; for (int i = 0; i < n; i++) c += dig(s, i) == 1; return c; }
static int ready(uint32_t s, int v) { int l = 2 * v + 1; return l >= n || (dig(s, l) == 1 && dig(s, l + 1) == 1); }
// 前向きの後続: 戻り値の数，out に (状態, 手の種類 0..3, v)
static int succ(uint32_t s, uint32_t *o, int *op, int *vv) {
    int k = 0, np = npb(s);
    for (int v = 0; v < n; v++) {
        int d = dig(s, v), r = ready(s, v);
        if (d == 0 && r && np + 1 <= cap) { o[k] = s + pw[v]; op[k] = 0; vv[k++] = v; }
        if (d == 2 && r && np + 1 <= cap) { o[k] = s - pw[v]; op[k] = 1; vv[k++] = v; }
        if (d == 1 && r) { o[k] = s - pw[v]; op[k] = 2; vv[k++] = v; }
        if (d == 1) { o[k] = s + pw[v]; op[k] = 3; vv[k++] = v; }
    }
    return k;
}
int main(int argc, char **argv) {
    int h = atoi(argv[1]); cap = atoi(argv[2]); int NP = atoi(argv[3]); unsigned seed = atoi(argv[4]); int extra = argc > 5 ? atoi(argv[5]) : 0;
    n = (1 << h) - 1; pw[0] = 1; for (int i = 1; i <= n; i++) pw[i] = pw[i - 1] * 3; N = pw[n];
    uint8_t *d0 = malloc(N), *d1 = malloc(N); memset(d0, 255, N); memset(d1, 255, N);
    uint32_t *q = malloc((size_t)N * 4); size_t hd = 0, tl = 0;
    uint32_t o[128]; int op[128], vv[128];
    d0[0] = 0; q[tl++] = 0;
    while (hd < tl) { uint32_t s = q[hd++]; int k = succ(s, o, op, vv);
        for (int j = 0; j < k; j++) if (d0[o[j]] == 255) { d0[o[j]] = d0[s] + 1; q[tl++] = o[j]; } }
    // 後ろ向き: 前向き後続を全状態で列挙して逆辺を辿る代わりに，逆操作を直接生成
    hd = tl = 0; d1[1] = 0; q[tl++] = 1;  // 根 = 桁 0 がペブル
    while (hd < tl) { uint32_t s = q[hd++]; int np = npb(s);
        for (int v = 0; v < n; v++) { int d = dig(s, v), r = ready(s, v); uint32_t p[2]; int kk = 0;
            if (d == 1 && r && np <= cap) { p[kk++] = s - pw[v]; p[kk++] = s + pw[v]; }   // pebble / unghost で来た
            if (d == 0 && r && np + 1 <= cap) p[kk++] = s + pw[v];                         // unpebble で来た
            if (d == 2 && np + 1 <= cap) p[kk++] = s - pw[v];                              // ghost で来た
            for (int j = 0; j < kk; j++) if (d1[p[j]] == 255) { d1[p[j]] = d1[s] + 1; q[tl++] = p[j]; } } }
    int T = d0[1]; fprintf(stderr, "h=%d cap=%d T=%d d1[0]=%d\n", h, cap, T, d1[0]);
    const char *nm[4] = {"pebble", "unghost", "unpebble", "ghost"};
    srand(seed);
    for (int t = 0; t < NP; t++) {
        uint32_t s = 0; printf("#path %d\n", t);
        int L = T + extra;
        for (int step = 0; step < L; step++) {
            int k = succ(s, o, op, vv), m = 0; int idx[128]; int r = L - step;
            for (int j = 0; j < k; j++) if (extra ? (d1[o[j]] != 255 && d1[o[j]] <= r - 1) : (d0[o[j]] == d0[s] + 1 && d1[o[j]] + 1 == d1[s])) idx[m++] = j;
            int j = idx[rand() % m]; printf("%s %d\n", nm[op[j]], vv[j]); s = o[j];
        }
        if (s != 1) { fprintf(stderr, "bad end\n"); return 1; }
    }
    return 0;
}
