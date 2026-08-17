#!/usr/bin/env python3
"""【実測】鎖は根つき木の中で極値か。**向きが $s$ で反転する。**

    python3 tree_extremal.py            # n<=8, s=3..6
    python3 tree_extremal.py 7 5        # n<=7, s<=5

## 何が分かったか（2026-08-18）

台帳の未解決問題「鎖が極値グラフか」に、**根つき木の範囲で答えが出た**。
頂点数 $n$ を固定し、根（出次数 0）にペブルを置く $T_P$ を全数比較すると:

| $s$ | 鎖の位置 |
|---|---|
| $3$ | **最大**（最も高い）。鎖は最も深いので、上限 3 では最も損をする |
| $\\ge4$ | **最小**（最も安い）。同点の木が多数 |

例（$n=7$）: $s=3$ で 鎖 39・最小 29（深さ 4 の平衡木）・最大 39。
$s=4$ で 鎖 19・最小 19・最大 23。

$s=3$ では**深さが小さいほど安い**（$n=7$: 深さ4→29、5→31、6→39、7→39）。
上限 3 で到達可能な木は入次数 $\\le2$ のものだけなので候補が少ない（$n=8$ で 64 本）。

## 形式化への含意

`decomp_ge` の依存で**鎖の構造を使っているのは 4 補題だけ**:

| 補題 | 鎖の使い方 | 一般 DAG へ |
|---|---|---|
| `Ghost.Dom_ready` | `ready` はペブルの位置だけで決まる | **そのまま** |
| `Count.pred_pebbled` | `v_i` を置くには `v_{i-1}` がペブル | **そのまま**（親を 1 つ取ればよい） |
| `Decomp.two_pebbles_of_clear` | 同上 | **そのまま**（入次数 $\\ge1$ があればよい） |
| `Project.ready_shift` | 頭/尻尾の添字ずらし | **ここだけ鎖が本質** |

すなわち障害は **$k$ の取り方でも数え上げでもなく「頭/尻尾の分割」**。分割が成り立つのは
「1 頂点を取り除くと下と上に分かれる」＝**関節点**があるときで、鎖は全頂点がそれ。
木は分岐するので単一頂点では分かれない。**KSS の分解は本質的に直列構造の道具**である。
（README の「木への一般化が近い」は楽観的すぎた。訂正した。）
"""
from __future__ import annotations

import itertools
import sys

import spooky


def trees(n: int):
    """頂点 n-1 を根とする根つき木を全列挙（親は自分より大きい添字）。"""
    for par in itertools.product(*[range(v + 1, n) for v in range(n - 1)]):
        inn: list[list[int]] = [[] for _ in range(n)]
        for v, p in enumerate(par):
            inn[p].append(v)
        yield inn


def depth(inn: list[list[int]], root: int) -> int:
    return 1 + max((depth(inn, c) for c in inn[root]), default=0)


def main() -> int:
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    smax = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    fails: list[str] = []
    print("鎖は極値か（根つき木・全数）")
    print(f"{'n':>2} {'s':>2} | {'鎖':>5} {'最小':>5} {'最大':>5} {'到達可能':>8} | 判定")
    for n in range(4, nmax + 1):
        for s in range(3, smax + 1):
            tc = spooky.min_time(spooky.chain(n), s)
            vs = [t for inn in trees(n) if (t := spooky.min_time(inn, s)) is not None]
            if not vs or tc is None:
                continue
            lo, hi = min(vs), max(vs)
            j = []
            if tc == lo:
                j.append("鎖=最小")
            if tc == hi:
                j.append("鎖=最大")
            if not j:
                j.append("どちらでもない")
                fails.append(f"n={n} s={s}: 鎖 {tc} が [{lo},{hi}] の内点")
            print(f"{n:>2} {s:>2} | {tc:>5} {lo:>5} {hi:>5} {len(vs):>8} | {' / '.join(j)}")
            # 主張の検定
            if s == 3 and n >= 5 and tc != hi:
                fails.append(f"n={n} s=3: 鎖が最大でない（{tc} != {hi}）")
            if s >= 4 and tc != lo:
                fails.append(f"n={n} s={s}: 鎖が最小でない（{tc} != {lo}）")

    print("\ns=3 での深さと T_P の関係（深いほど高い）:")
    for n in (6, 7, 8):
        by = {}
        for inn in trees(n):
            t = spooky.min_time(inn, 3)
            if t is None:
                continue
            d = depth(inn, n - 1)
            by.setdefault(d, set()).add(t)
        print(f"  n={n}: " + "  ".join(f"深さ{d}→{sorted(v)}" for d, v in sorted(by.items())))

    if fails:
        print(f"\nNG {len(fails)} 件:")
        for f in fails[:10]:
            print("  -", f)
        return 1
    print("\nすべて成立。s=3 で鎖は最大、s>=4 で鎖は最小。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
