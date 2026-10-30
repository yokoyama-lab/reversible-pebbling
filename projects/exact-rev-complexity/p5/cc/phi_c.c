/* phi_search.py の C 版（同じ意味．機械可読の出力）．
   境目 1 つの 2CM の写像 φ の候補: 2 本の盤 X ∋ A0,B0 ごとに，すべての予算の歩みで R'(Y) ≤ R(X) となる 1 本の盤 Y ∋ A0（|Y| ≤ |X|）の集合．
   使い方: phi_c a b [cap]．出力: 1 行目に "a b states closed|CAP"，以後 "X: y1 y2 ..."（ビット i は 1 本の頂点 v_i，2 本では i<a が A_i，i>=a が B_{i-a}）． */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define INF 30000
typedef int16_t V;
static int a, b, L, N, BMAX;
static int pc[1 << 12], need2[16], needM[16];
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
/* 状態: D2[N], DM[N], beta */
static int SZ;
static V *store; static int nst, cap;
static int *htab; static int hsz;
static uint64_t hashst(const V *s) { uint64_t h = 1469598103934665603ULL; const unsigned char *p = (const unsigned char *)s; for (int i = 0; i < SZ * 2; i++) { h ^= p[i]; h *= 1099511628211ULL; } return h; }
static int insert(const V *s) {
  uint64_t h = hashst(s); int i = h & (hsz - 1);
  while (htab[i] >= 0) { if (!memcmp(store + (size_t)htab[i] * SZ, s, SZ * 2)) return 0; i = (i + 1) & (hsz - 1); }
  if (nst >= cap) return -1;
  memcpy(store + (size_t)nst * SZ, s, SZ * 2); htab[i] = nst++; return 1;
}
int main(int argc, char **argv) {
  a = atoi(argv[1]); b = atoi(argv[2]); cap = argc > 3 ? atoi(argv[3]) : 200000;
  L = a + b; N = 1 << L; BMAX = L; SZ = 2 * N + 1;
  for (int x = 0; x < N; x++) pc[x] = __builtin_popcount(x);
  for (int i = 0; i < L; i++) {
    need2[i] = i < a ? (i + 1 < a ? 1 << (i + 1) : 0) : (i + 1 < L ? 1 << (i + 1) : 0);
    needM[i] = i + 1 < L ? 1 << (i + 1) : 0;
  }
  store = malloc((size_t)cap * SZ * sizeof(V)); hsz = 1; while (hsz < 2 * cap) hsz <<= 1;
  htab = malloc(sizeof(int) * hsz); memset(htab, -1, sizeof(int) * hsz);
  /* cand[x] は Y のビット集合（N ビット） */
  int W = (N + 63) / 64; uint64_t *cand = calloc((size_t)N * W, 8);
  for (int x = 0; x < N; x++) if ((x & 1) && (x >> a & 1))
    for (int y = 0; y < N; y++) if ((y & 1) && pc[y] <= pc[x]) cand[(size_t)x * W + y / 64] |= 1ULL << (y % 64);
  V *s = malloc(SZ * sizeof(V)), *t = malloc(SZ * sizeof(V));
  for (int b0 = 0; b0 <= BMAX; b0++) {
    for (int i = 0; i < 2 * N; i++) s[i] = INF; s[0] = 0; s[N] = 0; s[2 * N] = b0;
    relax(s, need2, b0); relax(s + N, needM, b0); insert(s);
  }
  int head = 0, full = 0;
  while (head < nst) {
    V *cur = store + (size_t)head++ * SZ; memcpy(s, cur, SZ * sizeof(V));
    int beta = s[2 * N];
    for (int x = 0; x < N; x++) {
      if (!((x & 1) && (x >> a & 1)) || s[x] >= INF) continue;
      for (int y = 0; y < N; y++) if (s[N + y] > s[x]) cand[(size_t)x * W + y / 64] &= ~(1ULL << (y % 64));
    }
    for (int d = -1; d <= 1; d += 2) {
      int nb = beta + d; if (nb < 0 || nb > BMAX) continue;
      int lim = beta < nb ? beta : nb;
      for (int i = 0; i < 2 * N; i++) t[i] = pc[i % N] <= lim ? s[i] : INF;
      t[2 * N] = nb;
      relax(t, need2, nb); relax(t + N, needM, nb);
      int m = INF; for (int x = 0; x < N; x++) if (t[x] < m) m = t[x];
      if (m >= INF) continue;
      for (int i = 0; i < 2 * N; i++) if (t[i] < INF) t[i] -= m;
      if (insert(t) < 0) { full = 1; break; }
    }
    if (full) break;
  }
  printf("%d %d %d %s\n", a, b, nst, full ? "CAP" : "closed");
  for (int x = 0; x < N; x++) if ((x & 1) && (x >> a & 1)) {
    printf("%d:", x);
    for (int y = 0; y < N; y++) if (cand[(size_t)x * W + y / 64] >> (y % 64) & 1) printf(" %d", y);
    printf("\n");
  }
  return 0;
}
