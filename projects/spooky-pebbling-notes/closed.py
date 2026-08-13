#!/usr/bin/env python3
"""鎖の厳密値を**漸化式だけ**で計算する（全数探索なしで n を大きく取る）。

KSS（arXiv:2110.08973v3）は線グラフについて厳密漸化式を 2 本持っている:

- **Cor 4.7**  T_P(n,s)  = min_{k in [1,n)} [ 2k-1 + T_UP(k,s-1) + T_P(n-k,s-1) ]
- **Cor 4.12** T_UG(n,s) = min_{k in [1,n]} [ 2k-1 + T_UP(k,s)   + T_UG(n-k,s-1) ]

**しかしこの 2 本は閉じていない。** どちらも T_UP を参照するのに、T_UP を決める式が無く、
KSS が与えるのは Thm 4.11 の `T_UG(n,s) = T_UP(n,s) ± 1` だけ（Lemma 4.9/4.10 から出るのは
両側の不等式のみ）。KSS は下界 Ω(mn) を出すのが目的なのでこれで足りるが、**厳密値は出せない**。

ここでは実測から得た次の規則で閉じる:

    T_UP(n,s) = T_UG(n,s) + delta(n,s),   delta = +1 if n >= theta(s) else -1
    theta(s) = s(s+1)/2                                    ← 層3（実測に基づく予想）

`--verify` で全数探索（`kss.py`）の値と突き合わせる。**この規則が破れたら閉形式も無効**。
"""
from __future__ import annotations

import argparse
import sys
from functools import lru_cache

INF = float("inf")


def theta(s: int) -> int:
    """delta の符号が反転する n（実測: s=2,3,4 で 3,6,10）。"""
    return s * (s + 1) // 2


def delta(n: int, s: int) -> int:
    return 1 if n >= theta(s) else -1


@lru_cache(maxsize=None)
def T_UG(n: int, s: int) -> float:
    """KSS Cor 4.12。k=n の項は 2n-1+T_UP(n,s) >= T_UG(n,s)+2n-2 で n>=2 では
    けっして最小にならないので、自己参照を避けるため k in [1,n-1] に絞る。"""
    if n == 0:
        return 0
    if s >= 1 and n == 1:
        return 2
    if s < 2 and s < n:
        return INF
    return min((2 * k - 1 + T_UP(k, s) + T_UG(n - k, s - 1)
                for k in range(1, n)), default=INF)


@lru_cache(maxsize=None)
def T_UP(n: int, s: int) -> float:
    """こちらの規則（層3）。基底は全数探索と一致することを確認済み。"""
    if n == 0:
        return 0
    if s >= 1 and n == 1:
        return 1
    if s < 2 and s < n:
        return INF
    v = T_UG(n, s)
    return INF if v == INF else v + delta(n, s)


@lru_cache(maxsize=None)
def T_P(n: int, s: int) -> float:
    """KSS Cor 4.7。"""
    if s >= 1 and n == 1:
        return 1
    if s < 3 and s < n:
        return INF
    return min((2 * k - 1 + T_UP(k, s - 1) + T_P(n - k, s - 1)
                for k in range(1, n)), default=INF)


def verify(nmax: int, smax: int) -> int:
    """全数探索の値と突き合わせる（`kss.py` の BFS が正）。"""
    import kss as bfs

    bad = []
    checked = 0
    for s in range(1, smax + 1):
        for n in range(1, nmax + 1):
            for name, mine, theirs in (
                ("T_P", T_P(n, s), bfs.T_P(n, s)),
                ("T_UP", T_UP(n, s), bfs.T_UP(n, s)),
                ("T_UG", T_UG(n, s), bfs.T_UG(n, s)),
            ):
                t = INF if theirs is None else theirs
                checked += 1
                if mine != t:
                    bad.append(f"{name}({n},{s}): 漸化式={mine} 全数探索={t}")
    print(f"突き合わせた点: {checked}")
    if bad:
        print(f"NG {len(bad)} 件:")
        for b in bad[:25]:
            print("  -", b)
        return 1
    print(f"すべて一致（n<={nmax}, s<={smax}）")
    return 0


def fit(n_from: int, n_to: int, s: int) -> None:
    """閉形式の当てはめ（差分が定数になるまで階差を取る）。"""
    xs = list(range(n_from, n_to + 1))
    ys = [T_P(n, s) for n in xs]
    if any(y == INF for y in ys):
        print(f"s={s}: 範囲内に到達不能な n がある")
        return
    print(f"s={s}: n={n_from}..{n_to} → {[int(y) for y in ys[:12]]}"
          + (" …" if len(ys) > 12 else ""))
    d, order = [int(y) for y in ys], 0
    while len(set(d)) > 1 and order < 6:
        d = [b - a for a, b in zip(d, d[1:])]
        order += 1
    if len(set(d)) == 1 and len(d) >= 3:
        print(f"    {order} 階差分が定数 {d[0]} → {order} 次多項式")
    else:
        loc = [(ys[i + 1] - ys[i]) for i in range(len(ys) - 1)]
        print(f"    多項式でない。局所差分の末尾: {[int(x) for x in loc[-5:]]}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verify", nargs=2, type=int, metavar=("NMAX", "SMAX"))
    ap.add_argument("--table", nargs=2, type=int, metavar=("NMAX", "SMAX"))
    ap.add_argument("--fit", nargs=3, type=int, metavar=("FROM", "TO", "S"))
    args = ap.parse_args()
    sys.setrecursionlimit(100000)

    if args.verify:
        return verify(*args.verify)
    if args.table:
        nmax, smax = args.table
        print(f"{'n':>4} " + "".join(f"{'P' + str(s):>10}" for s in range(3, smax + 1)))
        for n in range(1, nmax + 1):
            print(f"{n:>4} " + "".join(
                f"{'-' if T_P(n, s) == INF else int(T_P(n, s)):>10}"
                for s in range(3, smax + 1)))
        return 0
    if args.fit:
        fit(*args.fit)
        return 0
    ap.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
