#!/usr/bin/env python3
"""SKETCH 第 2 回 D・E の計算（置き回数の深さ別平均，J_u 内の子の置き直し，同じ深さの隣接 J の互いに素）．
⚠ 批判者の第 2 回レビュー: E の H2 は兄弟対が構造上必ず重なるだけ（兄弟以外はほぼ互いに素），H1 は区間の取り方の誤り．
   D の平均置き回数は (T+1)/(2n) の恒等式．このスクリプトは記録のために残す（結論は SKETCH の訂正を見よ）．
使い方: python3 stats.py <手順ファイル（"op v" 行．# 行と T= 行は無視）> <h>
"""
import collections
import sys

mv = [ln.split() for ln in open(sys.argv[1]) if ln.strip() and not ln.startswith(("#", "T="))]
h = int(sys.argv[2])
n = 2 ** h - 1
cnt = collections.Counter(int(v) for o, v in mv if o in ("pebble", "unghost"))


def depth(v):
    return (v + 1).bit_length() - 1


by = collections.defaultdict(list)
for v in range(n):
    by[depth(v)].append(cnt[v])
print(f"手数 {len(mv)} 平均置き回数 {sum(cnt.values()) / n:.2f} 深さ別",
      {d: round(sum(x) / len(x), 2) for d, x in sorted(by.items())})
place = {v: [] for v in range(n)}
rem = {v: [] for v in range(n)}
for t, (o, v) in enumerate(mv):
    (place if o in ("pebble", "unghost") else rem)[int(v)].append(t)
J = {u: (place[u][-1], rem[u][-1]) for u in range(1, n) if 2 * u + 1 < n}
rep = collections.defaultdict(list)
for u, (a, b) in J.items():
    rep[depth(u)].append(sum(1 for c in (2 * u + 1, 2 * u + 2) if any(a < t < b for t in place[c])))
print("J_u 内で置き直された子の数", dict(sorted(rep.items())))
