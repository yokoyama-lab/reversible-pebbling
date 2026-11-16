#!/usr/bin/env python3
"""p5/lb の回帰テスト（pytest 不要: python3 test_lb.py）.

検査するもの:
  T1 鎖: 再帰 Fc_dp ＝ 鎖のゲームの全数探索（n<=8）＝ 計数関数による Row.Fc（S<=10）
  T2 木: 自作の F が完全二分木の最小空間で 1,5,17,53,155,429（h<=6）を再現し，
         M=F を BFS で（頂点数 <=8 の全形・全 S）確かめる
  T3 補題 A（再帰の比較）: すべての木 G・すべての S で F(G,S) >= Fc(|G|,S)（頂点数 <= 11）
     変異（右辺を Fc(|G|+1,S) にする）が破れを出すこと（検出力）
  T4 ゲームでの比較: M(G,S) >= Fc(|G|,S)（頂点数 <= 9 の全形・全 S，BFS）
  T5 下界の値: Fc(2^h-1, p_h) <= M*(h)（h<=7．M* は全数探索の既知値）
  T6 写像の証明書 out/psi_T4_S6.txt（lip_sat.py --space 6 の解）を check_map.py で検査し，
     1 点を壊した写しが落ちること（検出力）
"""

from __future__ import annotations

import sys
import time

sys.path.insert(0, __file__.rsplit("/", 1)[0])

from chain import INF, Fc_dp, Row, chain_bfs  # noqa: E402
import tree_f as T  # noqa: E402

MSTAR = {1: 1, 2: 5, 3: 17, 4: 53, 5: 155, 6: 429, 7: 1001}
PMIN = {1: 1, 2: 3, 3: 5, 4: 6, 5: 7, 6: 8, 7: 10, 8: 11, 9: 12, 10: 13, 11: 14, 12: 15}
FSTAR = {8: 2789, 9: 7649, 10: 20995, 11: 56881, 12: 154125}  # 原稿 表 1（再帰 F の値）

FAILS = []


def check(name, cond, detail=""):
    print(f"[{'ok' if cond else 'NG'}] {name} {detail}")
    if not cond:
        FAILS.append(name)


def t1():
    ok = all(Fc_dp(n, S) == chain_bfs(n, S) for n in range(1, 9) for S in range(1, 10))
    check("T1a 鎖: 再帰 = ゲームの全数探索 (n<=8, S<=9)", ok)
    ok = all(Fc_dp(n, S) == Row.Fc(n, S) for S in range(1, 11) for n in range(0, 2 ** (S - 1) + 2))
    check("T1b 鎖: 再帰 = 計数関数 (S<=10, 全 n)", ok)
    fp = [Row.Fc(2 ** (p - 1), p) for p in range(1, 10)]
    check("T1c f_p = 1,3,9,25,71,193,531,1431,3835", fp == [1, 3, 9, 25, 71, 193, 531, 1431, 3835], str(fp))


def t2():
    vals = {h: T.F(T.Bt(h), PMIN[h]) for h in range(1, 7)}
    pm = {h: T.pmin(T.Bt(h)) for h in range(1, 7)}
    check("T2a F(T_h,p_min) = M*(h) (h<=6)", all(vals[h] == MSTAR[h] for h in vals), str(vals))
    check("T2b p_min(T_h) (h<=6)", all(pm[h] == PMIN[h] for h in pm), str(pm))
    shapes = T.all_rooted_trees(8)
    bad = [(g, S) for g in shapes for S in range(1, T.size(g) + 1) if T.F(g, S) != T.bfs_M(g, S)]
    check("T2c M = F（頂点数<=8 の全形・全 S）", not bad, f"{len(shapes)} 形, 不一致 {len(bad)}")


def t3():
    shapes = T.all_rooted_trees(11)
    pts = viol = eq = 0
    for g in shapes:
        n = T.size(g)
        for S in range(1, n + 2):
            f = T.F(g, S)
            c = Row.Fc(n, S)
            pts += 1
            if f < c:
                viol += 1
            if f == c and f < INF:
                eq += 1
    check("T3a 補題 A: F(G,S) >= Fc(|G|,S)（頂点数<=11 の全形・全 S）", viol == 0,
          f"{len(shapes)} 形, {pts} 点, 破れ {viol}, 等号（有限）{eq}")
    mut = sum(1 for g in shapes for S in range(1, T.size(g) + 2) if T.F(g, S) < Row.Fc(T.size(g) + 1, S))
    check("T3b 変異 Fc(|G|+1,S) は破れを出す（検出力）", mut > 0, f"破れ {mut} 点")


def t4():
    shapes = T.all_rooted_trees(9)
    pts = viol = 0
    for g in shapes:
        n = T.size(g)
        for S in range(1, n + 1):
            m = T.bfs_M(g, S)
            pts += 1
            if m < Row.Fc(n, S):
                viol += 1
    check("T4 ゲーム: M(G,S) >= Fc(|G|,S)（頂点数<=9 の全形・全 S，BFS）", viol == 0, f"{pts} 点, 破れ {viol}")


def t5():
    rows = []
    ok = True
    for h in range(1, 13):
        n = 2 ** h - 1
        lb = Row.Fc(n, PMIN[h])
        ref = MSTAR.get(h, FSTAR.get(h))
        rows.append((h, lb, ref))
        ok &= lb <= ref
    check("T5 Fc(2^h-1,p_h) <= M*(h) (h<=7) かつ <= F*(h) (h<=12)", ok, str(rows))


def t6():
    import os
    import subprocess
    import tempfile
    here = __file__.rsplit("/", 1)[0]
    t4 = "(((()())(()()))((()())(()())))"
    cert = os.path.join(here, "out", "psi_T4_S6.txt")
    chk = os.path.join(here, "check_map.py")
    r = subprocess.run([sys.executable, chk, t4, cert, "--space", "6"], capture_output=True, text=True)
    check("T6a T_4・S=6 の写像の証明書が条件を満たす", r.returncode == 0, r.stdout.strip().splitlines()[-1] if r.stdout else r.stderr[-200:])
    lines = [ln for ln in open(cert).read().split("\n") if ln]
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        for ln in lines:
            A, Z = map(int, ln.split())
            if A == 1 << 3:  # 葉 1 個の配置の像を {セル 2} に替える（鎖の手として不正）
                Z = 1 << 1
            f.write(f"{A} {Z}\n")
        mut = f.name
    try:
        r2 = subprocess.run([sys.executable, chk, t4, mut, "--space", "6"], capture_output=True, text=True)
    finally:
        os.unlink(mut)
    check("T6b 1 点を壊した写しは落ちる（検出力）", r2.returncode == 1)


if __name__ == "__main__":
    t0 = time.time()
    for t in (t1, t2, t3, t4, t5, t6):
        t()
    print(f"{'全通過' if not FAILS else '失敗: ' + ', '.join(FAILS)}（{time.time() - t0:.0f}s）")
    sys.exit(1 if FAILS else 0)
