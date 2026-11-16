#!/usr/bin/env python3
"""KSS（Kornerup–Sadun–Soloveichik, Quantum 9:1636, 2025）の構造定理を全数探索で検証する。

    python3 test_kss.py            # 既定 n<=10, s<=4（数十秒）
    python3 test_kss.py 11 5       # 範囲を指定

検証するもの（すべて一次資料の逐語。arXiv:2110.08973v3）:

- **Cor 4.7**: T_P(n,s) = min_{k in [1,n)} [ 2k-1 + T_UP(k,s-1) + T_P(n-k,s-1) ]
  （n>1、o.w. の枝。基底は n=1 で 1、s<3 かつ s<n で ∞）
- **Cor 4.12**: T_UG(n,s) = min_{k in [1,n]} [ 2k-1 + T_UP(k,s) + T_UG(n-k,s-1) ]
  （n>1。基底は n=1 で 2）
- **Thm 4.11 前半**: T_P(n+1,s+1) = T_UG(n,s) + 1
- **Thm 4.11 後半**: |T_UG(n,s) - T_UP(n,s)| <= 1（Lemma 4.9/4.10 から出るのはこれだけ）

3 量（T_P・T_UP・T_UG）はすべて**独立に全数探索**で出す。KSS の式の右辺と左辺が
一致すれば、その構造定理は探索範囲内で確認されたことになる。
"""
from __future__ import annotations

import sys

import kss

INF = float("inf")


def main(nmax: int = 10, smax: int = 4) -> int:
    fails: list[str] = []
    checked = {"cor47": 0, "cor412": 0, "thm411a": 0, "thm411b": 0}

    P = {(n, s): kss.T_P(n, s) for n in range(1, nmax + 1) for s in range(1, smax + 2)}
    UP = {(n, s): kss.T_UP(n, s) for n in range(1, nmax + 1) for s in range(1, smax + 2)}
    UG = {(n, s): kss.T_UG(n, s) for n in range(1, nmax + 1) for s in range(1, smax + 2)}

    def val(d, n, s):
        return d.get((n, s), INF) if d.get((n, s)) is not None else INF

    # --- Cor 4.7 ---
    for n in range(2, nmax + 1):
        for s in range(1, smax + 1):
            lhs = val(P, n, s)
            rhs = min((2 * k - 1 + val(UP, k, s - 1) + val(P, n - k, s - 1)
                       for k in range(1, n)), default=INF)
            checked["cor47"] += 1
            if lhs != rhs:
                fails.append(f"Cor 4.7 破れ: T_P({n},{s})={lhs} だが右辺={rhs}")

    # --- Cor 4.12 ---
    for n in range(2, nmax + 1):
        for s in range(1, smax + 1):
            lhs = val(UG, n, s)
            rhs = min((2 * k - 1 + val(UP, k, s) + val(UG, n - k, s - 1)
                       for k in range(1, n + 1)), default=INF)
            checked["cor412"] += 1
            if lhs != rhs:
                fails.append(f"Cor 4.12 破れ: T_UG({n},{s})={lhs} だが右辺={rhs}")

    # --- Thm 4.11 前半 ---
    for n in range(1, nmax):
        for s in range(1, smax + 1):
            lhs, rhs = val(P, n + 1, s + 1), val(UG, n, s)
            checked["thm411a"] += 1
            if lhs != INF or rhs != INF:
                if lhs != rhs + 1:
                    fails.append(f"Thm 4.11 前半の破れ: T_P({n+1},{s+1})={lhs}, "
                                 f"T_UG({n},{s})+1={rhs + 1}")

    # --- Thm 4.11 後半（±1 の幅しか出ない） ---
    diffs: dict[int, int] = {}
    for n in range(1, nmax + 1):
        for s in range(1, smax + 1):
            a, b = val(UG, n, s), val(UP, n, s)
            if a == INF or b == INF:
                continue
            checked["thm411b"] += 1
            d = a - b
            diffs[d] = diffs.get(d, 0) + 1
            if abs(d) > 1:
                fails.append(f"Thm 4.11 後半の破れ: T_UG({n},{s})-T_UP({n},{s})={d}")

    # --- 既存の測定との整合（README 表B） ---
    known = {4: 9, 5: 17, 6: 27, 7: 39, 8: 53, 9: 69, 10: 87}
    for n, t in known.items():
        if n <= nmax and val(P, n, 3) != t:
            fails.append(f"表B と不一致: T_P({n},3)={val(P, n, 3)} だが README は {t}")

    print(f"検証した組: {checked}")
    print(f"T_UG - T_UP の分布: {dict(sorted(diffs.items()))}")
    if fails:
        print(f"\nNG {len(fails)} 件:")
        for f in fails[:20]:
            print("  -", f)
        return 1
    print(f"\nすべて通過（n<={nmax}, s<={smax}）")
    return 0


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[1:]]
    raise SystemExit(main(*a) if a else main())
