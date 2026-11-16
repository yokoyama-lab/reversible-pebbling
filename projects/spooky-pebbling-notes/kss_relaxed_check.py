#!/usr/bin/env python3
"""KSS の緩和漸化式 (1) を、定理E の包絡および厳密値 T_UG と突き合わせる（2026-09-18）。

    python3 kss_relaxed_check.py

KSS（arXiv:2110.08973v3 §4、Cor 4.12 の直後）は厳密な漸化式の T_UP(k,s) を
T_UG(k,s)-1 に置き換えた**緩和**

    T(1,s)=2,  T(n,s)=inf (s<2 かつ s<n),
    T(n,s)=min_{1<=k<n} [2k-2 + T(k,s) + T(n-k,s-1)]                     ... (1)

だけを解析し、Ω(mn) を得ている（陽な定数は Lemma 4.23 の証明中の mn-2 のみ）。
このファイルは novelty-check（`paper-ieice/NOVELTY.md` §5）の裏づけとして 2 つを測る。

検定1: (1) の厳密解は定理E の包絡 max_m (2mn - c_m(s)) と一致するか
       （c_1=0, c_m(1)=2(m-1), c_m(s)=c_{m-1}(s)+c_m(s-1)+2。`SlopeE.lean`）
検定2: (1) が厳密値 T_UG(n,s)（`closed2.py`）と一致するのはどの n までか。B4(s)-1 か

⚠ どちらも**有界の数値照合（層3）**であって証明ではない。
⚠ 「出たらおかしい値」: T(n,s) > T_UG(n,s) が 1 点でも出たら (1) の実装が誤り（緩和は下界）。
"""
from __future__ import annotations

import sys
from functools import lru_cache
from math import comb

import closed2

sys.setrecursionlimit(100000)
INF = float("inf")


def relaxed(N: int, S: int):
    T = [[INF] * (S + 1) for _ in range(N + 1)]
    for s in range(1, S + 1):
        T[1][s] = 2
    for n in range(2, N + 1):
        for s in range(2, S + 1):
            T[n][s] = min(2 * k - 2 + T[k][s] + T[n - k][s - 1] for k in range(1, n))
    return T


def make_c(step: int):
    @lru_cache(maxsize=None)
    def c(m: int, s: int) -> int:
        if m == 1:
            return 0
        if s == 1:
            return 2 * (m - 1)
        return c(m - 1, s) + c(m, s - 1) + step
    return c


def main() -> int:
    bad = 0
    # --- 検定1 ---
    N, S = 300, 8
    T = relaxed(N, S)
    for label, step in (("本番（+2）", 2), ("対照（+2→+1 の変異）", 1)):
        c = make_c(step)
        pts = mism = 0
        for s in range(2, S + 1):
            for n in range(1, N + 1):
                if T[n][s] == INF:
                    continue
                pts += 1
                # s=2 は傾きが n ごとに上がるので m は n+1 まで見る
                if T[n][s] != max(2 * m * n - c(m, s) for m in range(1, n + 2)):
                    mism += 1
        print(f"検定1 {label}: 比較 {pts} 点 / 不一致 {mism} 点")
        if step == 2 and mism:
            bad += 1
        if step == 1 and not mism:
            print("  ⚠ 変異が通った＝検定が効いていない"); bad += 1
    for s in (3, 4, 5):
        bps = [n for n in range(2, N) if T[n + 1][s] != INF
               and T[n + 1][s] - T[n][s] != T[n][s] - T[n - 1][s]][:5]
        print(f"  s={s}: (1) の傾きの変わり目 {bps} / C(m+s-1,s-1) {[comb(m+s-1, s-1) for m in range(1, 6)]}")

    # --- 検定2 ---
    N2, S2 = 140, 7
    T2 = relaxed(N2, S2)
    print("検定2  s | (1)=T_UG となる最大の n | B4(s)-1 | 一致域内の不一致 | 域外の T_UG-(1) の最小")
    for s in range(2, S2 + 1):
        last, inner = 0, 0
        for n in range(1, N2 + 1):
            ex = closed2.T_UG(n, s)
            if ex == INF:
                continue
            if T2[n][s] > ex:
                print(f"  ⚠ 出たらおかしい値: T({n},{s})={T2[n][s]} > T_UG={ex}"); bad += 1
            if ex == T2[n][s]:
                last = n
        inner = sum(1 for n in range(1, last + 1)
                    if closed2.T_UG(n, s) != INF and closed2.T_UG(n, s) != T2[n][s])
        after = [closed2.T_UG(n, s) - T2[n][s] for n in range(last + 1, N2 + 1)]
        b4 = comb(s + 2, 3) - s + 2
        ok = "✔" if last == b4 - 1 and inner == 0 else "✗"
        if ok == "✗":
            bad += 1
        print(f"       {s} | {last:4d} | {b4 - 1:4d} | {inner} | {min(after) if after else '-'}  {ok}")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
