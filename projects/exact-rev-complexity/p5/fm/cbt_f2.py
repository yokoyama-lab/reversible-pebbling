#!/usr/bin/env python3
"""完全二分木 T_h で F と F2（交差型を足した構成）を S = p_min .. p_min+extra で比べる.

使い方: python3 cbt_f2.py h extra
F2 < F なら M <= F2 < F で，原稿の表の F*(h) は厳密値ではない（上界が下がる）．
"""
import sys
import time

import cross_fast as cf
import ftree as ft

h, extra = int(sys.argv[1]), int(sys.argv[2])
t = time.time()
p = ft.pmin_cbt(h)
g = ft.cbt(h)
print(f"h={h} p_min(F)={p} PMIN_F={dict(sorted(ft.PMIN_F.items()))} ({time.time() - t:.1f}s)", flush=True)
for S in range(p, p + extra + 1):
    t = time.time()
    f = ft.F(g, S)
    f2 = cf.F2(g, S)
    print(f"S={S} F={f} F2={f2} {'F2<F' if f2 < f else 'F2=F'} ({time.time() - t:.1f}s)", flush=True)
print("DONE", flush=True)
