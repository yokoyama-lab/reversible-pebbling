/* 鎖の森 P（各鎖の頂上に石がある盤 X）と 1 本の鎖 Q（長さは P の合計）を，すべての予算の歩みで比べる．
   φ_sort(X): X の各石から下へ次の石の手前（または鎖の終わり）までを区間とし，区間の長さを短い順に上から積んだ Q の盤．
   検査: (1) すべての歩みで R_Q(φ_sort(X)) ≤ R_P(X)．(2) P の側で，区間の長さの多重集合が同じ X どうしの R_P が常に等しいか．
   使い方: forest_cmp "3,4" [cap] [rev]（P の鎖の長さ．鎖 i の頂点は連番，鎖の頂上が番号の小さい側）．Q の頂点 v_0 が頂上． */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define INF 30000
typedef int16_t V;
static int L, N, BMAX, nc, len[16], start[16];
static int pc[1 << 14], needP[16], needQ[16];
static void relax(V *E, const int *need, int B) {
  int ch = 1;
  while (ch) {
    ch = 0;
    for (int x = 0; x < N; x++) {
      if (E[x] >= INF) continue;
      for (int v = 0; v < L; v++) {
        if ((x & need[v]) != need[v]) continue;
        int y = x ^ (1 << v);
        if (pc[y] > B) continue;
        if (E[x] + 1 < E[y]) { E[y] = E[x] + 1; ch = 1; }
      }
    }
  }
}
static int SZ; static V *store; static int nst, cap; static int *htab; static int hsz;
static uint64_t hashst(const V *s) { uint64_t h = 1469598103934665603ULL; const unsigned char *p = (const unsigned char *)s; for (int i = 0; i < SZ * 2; i++) { h ^= p[i]; h *= 1099511628211ULL; } return h; }
static int insert(const V *s) {
  uint64_t h = hashst(s); int i = h & (hsz - 1);
  while (htab[i] >= 0) { if (!memcmp(store + (size_t)htab[i] * SZ, s, SZ * 2)) return 0; i = (i + 1) & (hsz - 1); }
  if (nst >= cap) return -1;
  memcpy(store + (size_t)nst * SZ, s, SZ * 2); htab[i] = nst++; return 1;
}
static int REV = 0; /* 変異: 1 なら長い順（検出力の確認用） */
static int MODE = 0; /* 0: φ_sort で 1 本へ，1: swap1，2: isort（1, 2 は Q を P と同じ森にする） */
static int cmpint(const void *p, const void *q) { int d = *(const int *)p - *(const int *)q; return REV ? -d : d; }
int main(int argc, char **argv) {
  char buf[256]; strncpy(buf, argv[1], 255);
  for (char *t = strtok(buf, ","); t; t = strtok(NULL, ",")) len[nc++] = atoi(t);
  cap = argc > 2 ? atoi(argv[2]) : 0; REV = argc > 3 && !strcmp(argv[3], "rev");
  if (argc > 3 && !strcmp(argv[3], "swap1")) MODE = 1;
  if (argc > 3 && !strcmp(argv[3], "isort")) MODE = 2;
  L = 0; for (int i = 0; i < nc; i++) { start[i] = L; L += len[i]; }
  N = 1 << L; BMAX = L; SZ = 2 * N + 1; if (!cap) cap = 4 * N;
  for (int x = 0; x < N; x++) pc[x] = __builtin_popcount(x);
  for (int i = 0; i < nc; i++) for (int j = 0; j < len[i]; j++) { int v = start[i] + j; needP[v] = j + 1 < len[i] ? 1 << (v + 1) : 0; }
  for (int v = 0; v < L; v++) needQ[v] = v + 1 < L ? 1 << (v + 1) : 0;
  if (MODE) for (int v = 0; v < L; v++) needQ[v] = needP[v];
  int topmask = 0; for (int i = 0; i < nc; i++) topmask |= 1 << start[i];
  /* X ごとに φ_sort(X) と多重集合の鍵 */
  int *phi = malloc(sizeof(int) * N); long *key = malloc(sizeof(long) * N);
  for (int x = 0; x < N; x++) {
    phi[x] = -1; if ((x & topmask) != topmask) continue;
    int seg[32], ns = 0;
    for (int i = 0; i < nc; i++) {
      int prev = -1;
      for (int j = 0; j < len[i]; j++) if (x >> (start[i] + j) & 1) { if (prev >= 0) seg[ns++] = j - prev; prev = j; }
      seg[ns++] = len[i] - prev;
    }
    long k = 0;
    if (MODE == 0) {
      qsort(seg, ns, sizeof(int), cmpint);
      int y = 0, p = 0;
      for (int i = 0; i < ns; i++) { y |= 1 << p; p += seg[i]; k = k * 17 + seg[i]; }
      phi[x] = y;
    } else {
      /* 鎖ごとに区間を取り直し，MODE 1 は全体で最初の逆転を 1 つ，MODE 2 は各鎖を短い順に */
      int y = 0, done = 0, q = 0;
      for (int i = 0; i < nc; i++) {
        int sg[32], m = 0, prev = -1;
        for (int j = 0; j < len[i]; j++) if (x >> (start[i] + j) & 1) { if (prev >= 0) sg[m++] = j - prev; prev = j; }
        sg[m++] = len[i] - prev;
        if (MODE == 2) qsort(sg, m, sizeof(int), cmpint);
        else if (!done) for (int r = 0; r + 1 < m; r++) if (sg[r] > sg[r + 1]) { int tmp = sg[r]; sg[r] = sg[r + 1]; sg[r + 1] = tmp; done = 1; break; }
        int p = 0; for (int r = 0; r < m; r++) { y |= 1 << (start[i] + p); p += sg[r]; k = k * 17 + sg[r]; }
        q += m;
      }
      (void)q; phi[x] = y;
    }
    key[x] = k;
  }
  /* 多重集合の代表: 同じ鍵の最初の X */
  int *rep = malloc(sizeof(int) * N);
  for (int x = 0; x < N; x++) { rep[x] = -1; if (phi[x] < 0) continue; for (int z = 0; z < x; z++) if (phi[z] >= 0 && key[z] == key[x]) { rep[x] = z; break; } }
  store = malloc((size_t)cap * SZ * sizeof(V)); hsz = 1; while (hsz < 2 * cap) hsz <<= 1;
  htab = malloc(sizeof(int) * hsz); memset(htab, -1, sizeof(int) * hsz);
  char *viol = calloc(N, 1), *neq = calloc(N, 1), *tight = calloc(N, 1);
  V *s = malloc(SZ * sizeof(V)), *t = malloc(SZ * sizeof(V));
  for (int b0 = 0; b0 <= BMAX; b0++) {
    for (int i = 0; i < 2 * N; i++) s[i] = INF; s[0] = 0; s[N] = 0; s[2 * N] = b0;
    relax(s, needP, b0); relax(s + N, needQ, b0); insert(s);
  }
  int head = 0, full = 0;
  while (head < nst) {
    memcpy(s, store + (size_t)head++ * SZ, SZ * sizeof(V));
    int beta = s[2 * N];
    for (int x = 0; x < N; x++) {
      if (phi[x] < 0 || s[x] >= INF) continue;
      if (s[N + phi[x]] > s[x]) viol[x] = 1;
      if (s[N + phi[x]] == s[x]) tight[x] = 1;
    }
    for (int x = 0; x < N; x++) if (rep[x] >= 0 && s[x] != s[rep[x]]) neq[x] = 1;
    for (int d = -1; d <= 1; d += 2) {
      int nb = beta + d; if (nb < 0 || nb > BMAX) continue;
      int lim = beta < nb ? beta : nb;
      for (int i = 0; i < 2 * N; i++) t[i] = pc[i % N] <= lim ? s[i] : INF;
      t[2 * N] = nb;
      relax(t, needP, nb); relax(t + N, needQ, nb);
      int m = INF; for (int x = 0; x < N; x++) if (t[x] < m) m = t[x];
      if (m >= INF) continue;
      for (int i = 0; i < 2 * N; i++) if (t[i] < INF) t[i] -= m;
      if (insert(t) < 0) { full = 1; break; }
    }
    if (full) break;
  }
  int nx = 0, nv = 0, nn = 0, nt = 0;
  for (int x = 0; x < N; x++) if (phi[x] >= 0) { nx++; nv += viol[x]; nt += tight[x]; if (rep[x] >= 0) nn += neq[x]; }
  printf("P=%s L=%d states=%d %s X=%d viol=%d tight_somewhere=%d multiset_neq=%d\n", argv[1], L, nst, full ? "CAP" : "closed", nx, nv, nt, nn);
  for (int x = 0; x < N; x++) if (viol[x]) printf("  viol x=%d phi=%d\n", x, phi[x]);
  return 0;
}
