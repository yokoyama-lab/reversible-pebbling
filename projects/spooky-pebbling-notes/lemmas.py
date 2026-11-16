#!/usr/bin/env python3
"""KSS の未決部分を埋める補題の候補を、全数探索の値で検定する。

    python3 lemmas.py 11 5     # n<=11, s<=5 で全候補を検定

## 補題1（パリティ）— 証明済み・DAG 一般

各頂点の状態に $\\varphi(E)=0,\\ \\varphi(P)=1,\\ \\varphi(G)=0$ を割り当てる。
4 つの操作はいずれも**作用した頂点の $\\varphi$ を反転させる**:

| 操作 | 状態変化 | $\\varphi$ |
|---|---|---|
| pebble | E→P | 0→1 |
| unpebble | P→E | 1→0 |
| ghost | P→G | 1→0 |
| unghost | G→P | 0→1 |

したがって任意の妥当な spooky pebbling について
$$T \\equiv \\sum_v \\varphi(\\text{final}(v)) - \\varphi(\\text{init}(v)) \\pmod 2.$$

系: $T_P$ と $T_{UP}$ は**奇数**、$T_{UG}$ は**偶数**。ゆえに $T_{UG}\\neq T_{UP}$ で、
KSS Thm 4.11 の $|T_{UG}-T_{UP}|\\le 1$ と合わせて **$|T_{UG}-T_{UP}| = 1$ が厳密に成り立つ**。
KSS はここまで言っていない（$\\pm1$ は Lemma 4.9/4.10 の両側不等式のまま）。

## 補題2（前半コスト）— 証明済み。`prefix.py` が検定する

$F(m,s)$（空から「$v_m$ にペブル」までの最短手数）$= m\\ (m\\le s)$, $2m-s\\ (m>s)$、$s\\ge2$。

## 反証済みの候補（行き止まりの記録。テストは赤にしない）

- **候補 A**: $T_{UP}(n,s) = \\min(1 + T_{UG}(n,s),\\ T_P(n-1,s-1) + 1 + T_{UP}(n-1,s))$
- **候補 B**: $T_{UG}(n,s) = T_P(n-1,s) + 2 + T_{UP}(n-1,s)$

**どちらも反証された**（最小の反例 $T_{UP}(3,3)=5$ に対し候補 A の右辺は 7）。
理由: $T_P(m,\\cdot)$ は「$v_m$ **だけ**にペブルが残る」状態を終点にするので、分解の
中間状態としては**過剰に掃除している**。実際の最適手順は $v_1$ などをペブルのまま
残して後でまとめて外す。中間状態を $T_P$ で表すこの型の分解は成立しない。

**正しい分解に要るもの**: 中間状態の「ゴースト配置」まで持つ量。それは KSS Cor 4.12 の
$k$ 分解そのもので、$\\theta$ の証明はそこへ帰着する（未決）。
"""
from __future__ import annotations

import sys

import kss

INF = float("inf")


def v(f, n: int, s: int) -> float:
    if n <= 0 or s <= 0:
        return 0 if n == 0 else INF
    x = f(n, s)
    return INF if x is None else x


def main(nmax: int = 11, smax: int = 5) -> int:
    P = lambda n, s: v(kss.T_P, n, s)        # noqa: E731
    UP = lambda n, s: v(kss.T_UP, n, s)      # noqa: E731
    UG = lambda n, s: v(kss.T_UG, n, s)      # noqa: E731

    fails: list[str] = []
    counts = {"parity": 0, "diff1": 0, "A": 0, "B": 0}

    print("値を全数探索で用意中…", flush=True)
    vals = {(n, s): (P(n, s), UP(n, s), UG(n, s))
            for n in range(1, nmax + 1) for s in range(1, smax + 1)}

    # --- 補題1: パリティ ---
    for (n, s), (p, up, ug) in vals.items():
        for name, x, want in (("T_P", p, 1), ("T_UP", up, 1), ("T_UG", ug, 0)):
            if x == INF:
                continue
            counts["parity"] += 1
            if x % 2 != want:
                fails.append(f"パリティ破れ: {name}({n},{s})={x}（{'奇' if want else '偶'}のはず）")

    # --- 補題1の系: |T_UG - T_UP| = 1 ---
    for (n, s), (_, up, ug) in vals.items():
        if up == INF or ug == INF:
            continue
        counts["diff1"] += 1
        if abs(ug - up) != 1:
            fails.append(f"|T_UG-T_UP|=1 の破れ: ({n},{s}) で {ug - up}")

    # --- 反証済みの候補（記録用。ここは fails に入れない） ---
    refuted = []
    for n in range(2, nmax + 1):
        for s in range(1, smax + 1):
            counts["A"] += 1
            if UP(n, s) != min(1 + UG(n, s), P(n - 1, s - 1) + 1 + UP(n - 1, s)):
                refuted.append(("A", n, s, UP(n, s),
                                min(1 + UG(n, s), P(n - 1, s - 1) + 1 + UP(n - 1, s))))
            counts["B"] += 1
            if UG(n, s) != P(n - 1, s) + 2 + UP(n - 1, s):
                refuted.append(("B", n, s, UG(n, s), P(n - 1, s) + 2 + UP(n - 1, s)))

    print(f"検定した組: {counts}")
    for tag in ("A", "B"):
        first = next((r for r in refuted if r[0] == tag), None)
        if first:
            _, n, s, lhs, rhs = first
            print(f"候補{tag}: 反証済み（最小の反例 n={n}, s={s}: 実測={lhs} 右辺={rhs}）")
        else:
            print(f"⚠ 候補{tag} が反例を出さなかった。反証の記録と矛盾するので調べること")
            fails.append(f"候補{tag} の反証が再現しない")

    if fails:
        print(f"\nNG {len(fails)} 件（先頭 15 件）:")
        for f in fails[:15]:
            print("  -", f)
        return 1
    print(f"\n証明済みの補題はすべて成立（n<={nmax}, s<={smax}）")
    return 0


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[1:]]
    raise SystemExit(main(*a) if a else main())
