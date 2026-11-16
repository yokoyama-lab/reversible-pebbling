/* kmrv_weighted.py の bfs と同じゲームの全数探索（全手数，Ghost も 1）．状態 = 各位置 {空,ペブル,ゴースト} の 3 進数 × 旗（L に置いたか）．
   使い方: wbfs L s c mode   （mode 0 = 往復, 1 = touch-and-go）．出力: 最小の全手数（解なしは -1）． */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    int L = atoi(argv[1]), s = atoi(argv[2]), c = atoi(argv[3]), mode = atoi(argv[4]);
    uint64_t N = 1; for (int i = 0; i < L; i++) N *= 3;
    uint64_t pw[32]; pw[0] = 1; for (int i = 1; i <= L; i++) pw[i] = pw[i - 1] * 3;
    uint16_t *dist = malloc(sizeof(uint16_t) * N * 2);
    uint32_t *q = malloc(sizeof(uint32_t) * N * 2);
    if (!dist || !q) { fprintf(stderr, "oom\n"); return 2; }
    memset(dist, 0xff, sizeof(uint16_t) * N * 2);
    uint64_t head = 0, tail = 0; dist[0] = 0; q[tail++] = 0;
    int cell[32];
    while (head < tail) {
        uint32_t id = q[head++]; uint64_t st = id >> 1; int f = id & 1; uint16_t d = dist[id];
        if (f && st == 0) { printf("%d\n", d); return 0; }
        uint64_t x = st; int cnt = 0;
        for (int i = 0; i < L; i++) { cell[i] = x % 3; x /= 3; if (cell[i] == 1) cnt++; }
        for (int i = 0; i < L; i++) {
            int prev = (i == 0) || cell[i - 1] == 1; int w = ((i + 1) % 3 == 1) ? c : 0;
            /* Pebble */
            if (cell[i] != 1 && prev && cnt + 1 + w <= s) {
                uint64_t ns; int nf = f;
                if (mode == 1 && i == L - 1) { ns = st - (uint64_t)cell[i] * pw[i]; nf = 1; }
                else { ns = st + (uint64_t)(1 - cell[i]) * pw[i]; if (i == L - 1) nf = 1; }
                uint32_t nid = (uint32_t)((ns << 1) | nf);
                if (dist[nid] == 0xffff) { dist[nid] = d + 1; q[tail++] = nid; }
            }
            if (cell[i] == 1) {
                /* Unpebble */
                if (prev && cnt + w <= s) {
                    uint64_t ns = st - pw[i]; uint32_t nid = (uint32_t)((ns << 1) | f);
                    if (dist[nid] == 0xffff) { dist[nid] = d + 1; q[tail++] = nid; }
                }
                /* Ghost */
                { uint64_t ns = st + pw[i]; uint32_t nid = (uint32_t)((ns << 1) | f);
                  if (dist[nid] == 0xffff) { dist[nid] = d + 1; q[tail++] = nid; } }
            }
        }
    }
    printf("-1\n"); return 0;
}
