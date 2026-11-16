#!/usr/bin/env python3
"""ゲームでの鎖比較 CC: M(G,S) >= Fc(|G|,S) を，全数探索の M の表で確かめる.

入力: 行ごとに「tid n M(S=1) ... M(S=n)」（-1 は到達不能）．p5/fm の bfs_m の出力形式．
CC は G の形によらず |G| と S だけで右辺が決まるので，形の情報は要らない．

使い方: python3 cc_check.py <m ファイル>...
"""

from __future__ import annotations

import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from chain import Row  # noqa: E402


def main(paths):
    tot_pts = tot_viol = 0
    for p in paths:
        pts = viol = eq = trees = 0
        nmin = nmax = None
        tight = None  # 有限の点での M / Fc の最小
        with open(p) as f:
            for line in f:
                if line.startswith("#") or not line.strip():
                    continue
                xs = list(map(int, line.split()))
                n, ms = xs[1], xs[2:]
                assert len(ms) == n, (p, xs[0], n, len(ms))
                trees += 1
                nmin = n if nmin is None else min(nmin, n)
                nmax = n if nmax is None else max(nmax, n)
                for S, m in enumerate(ms, start=1):
                    c = Row.Fc(n, S)
                    pts += 1
                    if m < 0:
                        continue  # M = inf は CC を満たす
                    if m < c:
                        viol += 1
                        if viol <= 5:
                            print(f"  破れ: tid={xs[0]} n={n} S={S} M={m} Fc={c}")
                    if m == c:
                        eq += 1
                    r = m / c
                    if n >= 4 and S < n and (tight is None or r < tight[0]):
                        tight = (round(r, 4), xs[0], n, S, m, c)
        print(f"{p}: 木 {trees}（n={nmin}..{nmax}），(木,S) {pts} 点，破れ {viol}，等号 {eq}，"
              f"S<n での M/Fc 最小 {tight}")
        tot_pts += pts
        tot_viol += viol
    print(f"合計 {tot_pts} 点，破れ {tot_viol}")
    return tot_viol


if __name__ == "__main__":
    sys.exit(1 if main(sys.argv[1:]) else 0)
