#!/usr/bin/env python3
"""前半コスト F(m,s) — 空から「v_m にペブルがある状態」への最短手数を確定する。

    python3 prefix.py 13 6

θ の前後で最適手順が変えるのは**前半だけ**である（`witness_up.py` で確認）:

- $T_{UP}(n,s)$: $v_n$ がペブルを保持するので、前半の鎖 $v_1..v_{n-1}$ の上限は $s-1$
- $T_{UG}(n,s)$: ゴーストは枠を食わないので上限は $s$。ただし unghost の瞬間だけ $s-1$

したがって「ペブル 1 個の価値」= $F(m,s-1) - F(m,s)$ が 1 手（unghost の追加コスト）を
上回るかどうかが符号を決める。

**補題（証明済み。$s\\ge2$、$s=1$ は $m\\ge2$ で到達不能）**:
$$F(m,s) = \\begin{cases} m & (m \\le s) \\\\ 2m-s & (m > s)\\end{cases}$$

- **上界**: $v_1,\\dots,v_s$ を順に置く（$s$ 手）。以後は「いちばん左のペブルをゴーストに
  する」→「次を置く」の 2 手ずつで 1 つ進む。よって $s + 2(m-s) = 2m-s$ 手。
- **下界**: $v_1,\\dots,v_m$ はいずれも**少なくとも 1 回ペブルされる**（$v_i$ を置くには
  $v_{i-1}$ がペブルでなければならず、帰納法で $v_1$ まで下りる）ので $m$ 手。さらに
  終状態でペブルは高々 $s$ 個なので、**少なくとも $m-s$ 個の頂点はペブルを外されている**
  （unpebble か ghost の 1 手）。この 2 種の手は互いに素なので $F \\ge m + (m-s)$。

この実行は上の補題を全数探索で確かめる（`m<=12, s=2..6` の 61 点）。
"""
from __future__ import annotations

import sys
from collections import deque

from spooky import EMPTY, GHOST, PEBBLE, chain


def _digits(code: int, n: int) -> list[int]:
    out = []
    for _ in range(n):
        out.append(code % 3)
        code //= 3
    return out


def F_bfs(m: int, s: int) -> int | None:
    """空 → 「v_m にペブル」（他の頂点の状態は問わない）の最短手数。"""
    in_nodes = chain(m)
    pw = [3 ** i for i in range(m)]
    goal_bit = pw[m - 1] * PEBBLE
    dist = {0: 0}
    q = deque([0])
    while q:
        code = q.popleft()
        d = dist[code]
        st = _digits(code, m)
        if st[m - 1] == PEBBLE:
            return d
        npeb = sum(1 for x in st if x == PEBBLE)
        ready = [all(st[u] == PEBBLE for u in in_nodes[v]) for v in range(m)]
        for v in range(m):
            cur = st[v]
            nxts = []
            if cur == EMPTY and ready[v] and npeb < s:
                nxts.append(code + pw[v] * PEBBLE)
            elif cur == PEBBLE:
                if ready[v]:
                    nxts.append(code - pw[v] * PEBBLE)
                nxts.append(code + pw[v])
            elif cur == GHOST and ready[v] and npeb < s:
                nxts.append(code - pw[v])
            for nxt in nxts:
                if nxt not in dist:
                    dist[nxt] = d + 1
                    q.append(nxt)
    _ = goal_bit
    return None


def formula(m: int, s: int) -> int | None:
    if s < 1 or (s == 1 and m >= 2):
        return None          # ペブル 1 個では v_2 を置けない（枠が空かない）
    return m if m <= s else 2 * m - s


def main(mmax: int = 12, smax: int = 6) -> int:
    fails = []
    n_ok = 0
    print(f"{'m':>3} " + "".join(f"{'s=' + str(s):>8}" for s in range(1, smax + 1)))
    for m in range(1, mmax + 1):
        row = f"{m:>3} "
        for s in range(1, smax + 1):
            got, want = F_bfs(m, s), formula(m, s)
            n_ok += 1
            mark = "" if got == want else f"!={want}"
            if got != want:
                fails.append(f"F({m},{s}): 全数探索={got} 予想={want}")
            row += f"{('-' if got is None else got)}{mark:>4}".rjust(8)
        print(row, flush=True)
    print(f"\n検定した組: {n_ok}")
    if fails:
        print(f"NG {len(fails)} 件:")
        for f in fails[:15]:
            print("  -", f)
        return 1
    print(f"F(m,s) = m (m<=s), 2m-s (m>s) が全点で成立（m<={mmax}, s<={smax}）")
    return 0


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[1:]]
    raise SystemExit(main(*a) if a else main())
