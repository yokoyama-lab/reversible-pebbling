// 完全二分木 T_k（ヒープ順），上限 c で，全状態から「空」への最短手数を逆向き BFS で求め，
// 根がペブルかつペブル数 <= m の状態の最小値 C(k,c,m) を m ごとに出す．規則は QL（ghost は無条件）．
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int k = atoi(argv[1]), c = atoi(argv[2]), n = (1 << k) - 1;
    uint32_t pw[20]; pw[0] = 1; for (int i = 1; i <= n; i++) pw[i] = pw[i - 1] * 3;
    uint32_t N = pw[n];
    uint8_t *d = malloc(N); memset(d, 255, N);
    uint32_t *q = malloc((size_t)N * 4); size_t h = 0, t = 0;
    d[0] = 0; q[t++] = 0;
    int st[20];
    while (h < t) {
        uint32_t s = q[h++], x = s; int np = 0;
        for (int i = 0; i < n; i++) { st[i] = x % 3; x /= 3; np += st[i] == 1; }
        for (int v = 0; v < n; v++) {
            int l = 2 * v + 1, ready = l >= n || (st[l] == 1 && st[l + 1] == 1);
            uint32_t p[2]; int kk = 0;
            if (st[v] == 0) { if (ready) p[kk++] = s + pw[v]; }                       // unpebble で来た
            else if (st[v] == 1) { if (ready && np <= c) { p[kk++] = s - pw[v]; p[kk++] = s + pw[v]; } } // pebble / unghost で来た
            else { p[kk++] = s - pw[v]; }                                              // ghost で来た
            for (int j = 0; j < kk; j++) {
                uint32_t y = p[j]; int yp = 0; uint32_t z = y;
                for (int i = 0; i < n; i++) { yp += z % 3 == 1; z /= 3; }
                if (yp > c) continue;
                if (d[y] == 255) { d[y] = d[s] + 1; q[t++] = y; }
            }
        }
    }
    int best[21]; for (int m = 0; m <= 20; m++) best[m] = 999;
    for (uint32_t s = 0; s < N; s++) {
        if (s % 3 != 1 || d[s] == 255) continue;
        uint32_t x = s; int np = 0; for (int i = 0; i < n; i++) { np += x % 3 == 1; x /= 3; }
        if (d[s] < best[np]) best[np] = d[s];
    }
    int run = 999; printf("k=%d c=%d C(m=1..%d):", k, c, c);
    for (int m = 1; m <= c; m++) { if (best[m] < run) run = best[m]; printf(" %d", run); }
    printf("\n");
    return 0;
}
