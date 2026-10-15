#!/usr/bin/env python3
"""枝刈り（ftree.lb_space）が F と F2 の値を変えないことの回帰検査.

枝刈りなしの値を別プロセス（PRUNE=False）で計算して比べる．
使い方: python3 test_prune.py 12 [maxdeg]
"""
import subprocess
import sys

N = int(sys.argv[1])
MAXDEG = sys.argv[2] if len(sys.argv) > 2 else "None"
code = r'''
import sys
import ftree as ft
ft.PRUNE = %s
import cross_fast as cf
if ft.PRUNE:
    for k in range(2, 6):
        ft.pmin_cbt(k)
by = ft.enumerate_trees(%d, %s)
out = []
for n in sorted(by):
    for g in by[n]:
        out.append(ft.canon(g) + " " + " ".join(str(ft.F(g, S)) + "/" + str(cf.F2(g, S)) for S in range(1, n + 1)))
print("\n".join(out))
'''
a = subprocess.run([sys.executable, "-c", code % ("True", N, MAXDEG)], capture_output=True, text=True, check=True).stdout
b = subprocess.run([sys.executable, "-c", code % ("False", N, MAXDEG)], capture_output=True, text=True, check=True).stdout
la, lb = sorted(a.splitlines()), sorted(b.splitlines())  # 形の番号は intern の順に依存するので形の文字列で揃える
assert len(la) == len(lb)
diff = sum(1 for x, y in zip(la, lb) if x != y)
print(f"trees n<={N}: {len(la)}, rows differing between pruned and unpruned F/F2: {diff}")
sys.exit(1 if diff else 0)
