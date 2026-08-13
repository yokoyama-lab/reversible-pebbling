#!/usr/bin/env python3
"""$T_{UP}$ 分解の $\\ge$ 方向の骨格を、実際の最適手順の上で検査する。

    python3 structure_check.py 10 4     # n<=10, s<=4

## 示したいこと（KSS Lemma 4.1 の unpebbling 版）

$$T_{UP}(n,s) \\ \\ge\\ \\min_{k}\\ \\bigl[\\,2k-1 + T_{UP}(n-k,s-1) + T_{UP}(k,s)\\,\\bigr]$$

## 骨格（KSS §4 を写したもの）

**補題3'（KSS Lemma 4.3 の写し。無条件）** 任意の妥当な手順で
$\\mathrm{Last}(v_n) < \\mathrm{Last}(v_{n-1}) < \\cdots < \\mathrm{Last}(v_1)$。
理由: $t=\\mathrm{Last}(v_i)$ の直後の $v_i$ への手は unpebble でなければならない
（ghost にすると $G_\\tau=\\emptyset$ のため後で unghost＝再ペブルが要り $\\mathrm{Last}$ に反する）。
unpebble は $v_{i-1}\\in P_t$ を要求するので $\\mathrm{Last}(v_{i-1})>t$。
**KSS は $i\\in[2,n-1]$ で述べているが、unpebbling では $v_n$ も空で終わるので $i=n$ まで延びる。**

**$k$ の定義** $t^\\ast = \\mathrm{Last}(v_n)$、$k = \\min\\{i : v_i \\in P_{t^\\ast}\\}$。
（$v_{n-1}\\in P_{t^\\ast}$ なので空でない。）

**段(i)** $t^\\ast$ までに $v_1..v_k$ 上で使う手は $\\ge 2k-1$。
$v_k$ を置くには $v_{k-1}$ が要り、帰納で $v_1$ まで下りるので各 $v_i\\ (i\\le k)$ は
少なくとも 1 回置かれる（$k$ 手）。$k$ の最小性から $i<k$ の $v_i$ は $P_{t^\\ast}$ に
無いので、少なくとも 1 回外されている（$k-1$ 手）。

**段(ii)** $v_{k+1}..v_n$ 上の手を順序を保って取り出すと、長さ $n-k$ の鎖の妥当な
unpebbling になる（$v_{k+1}$ の前提は孤立鎖では常に成立するので a fortiori）。
そのペブル数は $\\le s-1$（$v_k$ が枠を 1 つ占める。KSS の $P^\\bot$ 交換論法で、
$k$ を最大に取れば「尻尾が $s$ 個使う瞬間には頭が空」という場合を排除できる）。

**段(iii)** $v_1..v_k$ 上の手は「$v_k$ に単独ペブルを作る掃き」＋「頭の unpebbling」で、
後者は上限 $s$（尻尾が片付いた後は他に何も持たない）。

**この実行が検査するもの**: 実際の最適手順について 補題3'・段(i)・段(ii) のペブル上限・
そして 3 つの手数の和が漸化式の値に一致すること。
"""
from __future__ import annotations

import sys

import closed2
import kss
from spooky import EMPTY, GHOST, PEBBLE
from witness_up import shortest_path

INF = float("inf")


def simulate(n: int, seq: list[str]) -> list[tuple[tuple[int, ...], str, int]]:
    """各手の直前の状態と (操作名, 頂点) を返す。"""
    st = [EMPTY] * (n + 1)
    st[n] = PEBBLE
    out = []
    for op in seq:
        name, rest = op.split("(v")
        v = int(rest.rstrip(")"))
        out.append((tuple(st), name, v))
        st[v] = {"pebble": PEBBLE, "unpebble": EMPTY, "ghost": GHOST, "unghost": PEBBLE}[name]
    return out


def check_one(n: int, s: int, fails: list[str]) -> None:
    seq = shortest_path(n, s, 3 ** (n - 1) * PEBBLE, 0)
    if seq is None:
        return
    trace = simulate(n, seq)

    # 補題3': Last が右から左へ狭義単調
    last = {}
    for i, (st, name, v) in enumerate(trace):
        if st[v] == PEBBLE:
            last[v] = i
    for v in range(2, n + 1):
        if v in last and (v - 1) in last and not last[v] < last[v - 1]:
            fails.append(f"補題3' 破れ: n={n} s={s} で Last(v{v})={last[v]} "
                         f">= Last(v{v - 1})={last[v - 1]}")

    # k の定義
    tstar = last[n]
    st_star = trace[tstar][0]
    peb = [i for i in range(1, n + 1) if st_star[i] == PEBBLE]
    k = min(i for i in peb if i < n) if any(i < n for i in peb) else None
    if k is None:
        fails.append(f"k が定まらない: n={n} s={s}")
        return

    head = [1 for (_, _, v) in trace if v <= k]
    tail = [1 for (_, _, v) in trace if v > k]
    before = [1 for i, (_, _, v) in enumerate(trace) if v <= k and i <= tstar]

    # 段(i): t* までの頭の手数 >= 2k-1
    if len(before) < 2 * k - 1:
        fails.append(f"段(i) 破れ: n={n} s={s} k={k} で {len(before)} < {2 * k - 1}")

    # 段(ii): 尻尾のペブル上限 <= s-1
    mx = 0
    for st, _, _ in trace:
        mx = max(mx, sum(1 for i in range(k + 1, n + 1) if st[i] == PEBBLE))
    if mx > s - 1:
        fails.append(f"段(ii) 破れ: n={n} s={s} k={k} で尻尾が {mx} 個（<= {s - 1} のはず）")

    # 手数の分解が漸化式の項に一致するか
    tup = lambda a, b: (INF if closed2.T_UP(a, b) == INF else closed2.T_UP(a, b))  # noqa: E731
    want_tail = tup(n - k, s - 1)
    want_head = 2 * k - 1 + tup(k, s)
    if len(tail) != want_tail:
        fails.append(f"尻尾の手数: n={n} s={s} k={k} で {len(tail)} != T_UP({n - k},{s - 1})={want_tail}")
    if len(head) != want_head:
        fails.append(f"頭の手数: n={n} s={s} k={k} で {len(head)} != 2k-1+T_UP({k},{s})={want_head}")
    total = 2 * k - 1 + want_tail + tup(k, s)
    if len(seq) != total:
        fails.append(f"合計: n={n} s={s} k={k} で {len(seq)} != {total}")


def main(nmax: int = 10, smax: int = 4) -> int:
    fails: list[str] = []
    checked = 0
    for s in range(3, smax + 1):
        for n in range(2, nmax + 1):
            if kss.T_UP(n, s) is None:
                continue
            checked += 1
            check_one(n, s, fails)
    print(f"最適手順を調べた組: {checked}（n<={nmax}, s=3..{smax}）")
    if fails:
        print(f"\n観測された不一致 {len(fails)} 件（先頭 12）:")
        for f in fails[:12]:
            print("  -", f)
        print("\n注意: BFS は最短路の 1 本を任意に返すので、不一致は反証ではない")
        print("（主張は『この形の最適手順が存在する』）。ただし全件一致なら骨格の裏づけになる。")
        return 1
    print("\n補題3'・段(i)・段(ii) の上限・手数の分解が、全件で成立した。")
    print("=> T_UP 分解の >= 方向の骨格は、実際の最適手順の上で裏づけられた。")
    return 0


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[1:]]
    raise SystemExit(main(*a) if a else main())
