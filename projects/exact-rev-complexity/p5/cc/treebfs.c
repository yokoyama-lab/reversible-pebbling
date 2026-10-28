/* 根付き木の M(T,S)（∅ → {根}，盤の大きさ ≤ S，頂点 v の手は v の子がすべて盤にあるとき合法）を BFS で。
   入力: n S root の後に parent[0..n-1]（根は -1）。 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    int n, S, root; if (scanf("%d %d %d", &n, &S, &root) != 3) return 2;
    int par[32]; unsigned need[32]; memset(need, 0, sizeof need);
    for (int i = 0; i < n; i++) { scanf("%d", &par[i]); if (par[i] >= 0) need[par[i]] |= 1u << i; }
    unsigned N = 1u << n; int *d = malloc(sizeof(int) * N); unsigned *q = malloc(sizeof(unsigned) * N);
    for (unsigned i = 0; i < N; i++) d[i] = -1;
    unsigned h = 0, t = 0; d[0] = 0; q[t++] = 0; unsigned goal = 1u << root;
    while (h < t) {
        unsigned x = q[h++]; if (x == goal) { printf("%d\n", d[x]); return 0; }
        for (int v = 0; v < n; v++) {
            if ((x & need[v]) != need[v]) continue;
            unsigned y = x ^ (1u << v);
            if (__builtin_popcount(y) > S || d[y] >= 0) continue;
            d[y] = d[x] + 1; q[t++] = y;
        }
    }
    printf("-1\n"); return 0;
}
