/* 2 つの鎖の森 P，Q（長さの合計は同じ）と写像 x -> y（標準入力の "x y" の行）について，すべての予算の歩みで R_Q(y) ≤ R_P(x) かを調べる．
   使い方: pair_cmp "2,4" "1,5" < map.txt．出力: 1 行目に要約，以後 違反した x y．状態の閉包は forest_cmp.c と同じ． */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define INF 30000
typedef int16_t V;
static int L, N, BMAX;
static int pc[1 << 14], needP[16], needQ[16];
static void mkneed(char *arg, int *need, int *tot) {
  char buf[256]; strncpy(buf, arg, 255); buf[255] = 0; int st = 0;
  for (char *t = strtok(buf, ","); t; t = strtok(NULL, ",")) { int n = atoi(t); for (int j = 0; j < n; j++) need[st + j] = j + 1 < n ? 1 << (st + j + 1) : 0; st += n; }
  *tot = st;
}
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

int main(int argc, char **argv) {
  int LQ; mkneed(argv[1], needP, &L); mkneed(argv[2], needQ, &LQ);
  if (L != LQ) { fprintf(stderr, "length mismatch\n"); return 2; }
  N = 1 << L; BMAX = L; SZ = 2 * N + 1; cap = 4 * N;
  for (int x = 0; x < N; x++) pc[x] = __builtin_popcount(x);
  int *phi = malloc(sizeof(int) * N); for (int x = 0; x < N; x++) phi[x] = -1;
  int x, y, nx = 0; while (scanf("%d %d", &x, &y) == 2) { phi[x] = y; nx++; }
  store = malloc((size_t)cap * SZ * sizeof(V)); hsz = 1; while (hsz < 2 * cap) hsz <<= 1;
  htab = malloc(sizeof(int) * hsz); memset(htab, -1, sizeof(int) * hsz);
  char *viol = calloc(N, 1);
  V *s = malloc(SZ * sizeof(V)), *t = malloc(SZ * sizeof(V));
  for (int b0 = 0; b0 <= BMAX; b0++) {
    for (int i = 0; i < 2 * N; i++) s[i] = INF;
    s[0] = 0; s[N] = 0; s[2 * N] = b0;
    relax(s, needP, b0); relax(s + N, needQ, b0); insert(s);
  }
  int head = 0, full = 0;
  while (head < nst) {
    memcpy(s, store + (size_t)head++ * SZ, SZ * sizeof(V));
    int beta = s[2 * N];
    for (int x = 0; x < N; x++) if (phi[x] >= 0 && s[x] < INF && s[N + phi[x]] > s[x]) viol[x] = 1;
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
  int nv = 0; for (int x = 0; x < N; x++) nv += viol[x];
  printf("P=%s Q=%s states=%d %s maps=%d viol=%d\n", argv[1], argv[2], nst, full ? "CAP" : "closed", nx, nv);
  for (int x = 0; x < N; x++) if (viol[x]) printf("%d %d\n", x, phi[x]);
  return 0;
}
