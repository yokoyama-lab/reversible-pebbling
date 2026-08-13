#!/usr/bin/env python3
"""$T_{UG}(n,s)$ の増分の折れ目 $B(m,s)$ を出し、$\\theta$ をそこへ帰着させる。

    python3 breakpoints.py            # s=3..8 で検定

## 何が分かったか

$T_{UG}(n,s)$ の $n$ 方向の増分は $2,4,6,8,\\dots$ と**階段状に上がる**。
$B(m,s)$ を「増分が $2m$ になる最初の $n$」とすると、実測で

| | 値 | 意味 |
|---|---|---|
| $B(1,s)$ | $2$ | |
| $B(2,s)$ | $s+1$ | ペブルが足りるうちは 1 頂点あたり 2 手（置いて外す）。$n>s$ でゴーストが要る |
| $B(3,s)$ | $s(s+1)/2 + 1$ | |

そして **$\\theta(s) + 1 = B(3,s)$ が $s=3..8$ で成立する**。すなわち

> **符号の反転は「1 頂点あたりのコストが 4 から 6 へ上がる点」で起きる。**
> $\\theta(s) = B(3,s) - 1$ であり、$\\theta(s)=s(s+1)/2$ の証明は
> **$B(3,s) = s(s+1)/2+1$ の証明に帰着する**。

これは元の予想より扱いやすい。$B$ は $T_{UG}$ だけの量なので、KSS Cor 4.12
（$T_{UG}$ の厳密漸化式）がそのまま使え、$T_{UP}$ の未決部分を経由しない。

## KSS の閾値とは一致しない

KSS Thm 3.6 / 4.13 の閾値 $\\binom{m+s-2}{s-2}+1$ は**漸近レート $O(mn)$ の切り替わり**で、
ここでいう**厳密な増分の折れ目**とは別物（$s=5, m=3$ で 21 対 16）。両者を混同しないこと。
"""
from __future__ import annotations

import math

import closed


def breakpoints(s: int, nmax: int) -> dict[int, int]:
    """増分が 2m になる最初の n を m ごとに返す。"""
    vals = [closed.T_UG(n, s) for n in range(1, nmax + 1)]
    first: dict[int, int] = {}
    prev = None
    for n in range(2, nmax + 1):
        d = int(vals[n - 1] - vals[n - 2])
        if d != prev:
            first.setdefault(d, n)
            prev = d
    return {d // 2: n for d, n in first.items() if d % 2 == 0}


def check_lemma3(smax: int, fails: list[str]) -> None:
    """補題3（証明済み）: $n \\le s$ なら $T_{UG}(n,s) = 2n$、ゆえに $B(2,s)=s+1$。

    - 上界: $v_1..v_{n-1}$ を置き（$n-1$ 手）、unghost $v_n$・unpebble $v_n$（2 手）、
      $v_{n-1}..v_1$ を外す（$n-1$ 手）。計 $2n$。ペブルは高々 $n \\le s$ 個
    - 下界: どの $v_i$ も少なくとも 1 回ペブルされ（$v_n$ の unghost に $v_{n-1}$ が要り、
      帰納法で $v_1$ まで下りる）、どれも空で終わるので少なくとも 1 回外される。$\\ge 2n$
    """
    n_ok = 0
    for s in range(2, smax + 1):
        for n in range(1, s + 1):
            got = closed.T_UG(n, s)
            n_ok += 1
            if got != 2 * n:
                fails.append(f"補題3 破れ: T_UG({n},{s})={got}（2n={2 * n} のはず）")
    print(f"補題3（n<=s で T_UG=2n）: {n_ok} 点を検定")


def main() -> int:
    fails: list[str] = []
    check_lemma3(8, fails)
    print(f"{'s':>2} {'theta':>6} {'B(1)':>5} {'B(2)':>5} {'B(3)':>6} "
          f"{'s+1':>5} {'s(s+1)/2+1':>11} {'theta+1=B(3)':>13} {'KSS C(m+s-2,s-2)+1 (m=3)':>26}")
    for s in range(3, 9):
        nmax = min(400, 8 * s * s)
        b = breakpoints(s, nmax)
        th = closed.theta(s)
        b1, b2, b3 = b.get(1), b.get(2), b.get(3)
        kss3 = math.comb(3 + s - 2, s - 2) + 1
        ok = (b3 == th + 1)
        print(f"{s:>2} {th:>6} {str(b1):>5} {str(b2):>5} {str(b3):>6} "
              f"{s + 1:>5} {s * (s + 1) // 2 + 1:>11} {'一致' if ok else '不一致':>13} {kss3:>26}")
        if b1 != 2:
            fails.append(f"s={s}: B(1)={b1}（2 のはず）")
        if b2 != s + 1:
            fails.append(f"s={s}: B(2)={b2}（s+1={s + 1} のはず）")
        if b3 != s * (s + 1) // 2 + 1:
            fails.append(f"s={s}: B(3)={b3}（s(s+1)/2+1={s * (s + 1) // 2 + 1} のはず）")
        if not ok:
            fails.append(f"s={s}: theta+1={th + 1} と B(3)={b3} が違う")

    print("\n【帰着】theta(s) = B(3,s) - 1。theta の証明は "
          "「1 頂点あたりのコストが 4→6 になる n が s(s+1)/2+1 である」ことの証明に帰着する。")
    print("【注意】KSS の閾値 C(m+s-2,s-2)+1 は漸近レートの切り替わりで、"
          "厳密な折れ目とは別物（右端の列を比較）。")
    if fails:
        print(f"\nNG {len(fails)} 件:")
        for f in fails:
            print("  -", f)
        return 1
    print("\nすべて成立（s=3..8）")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
