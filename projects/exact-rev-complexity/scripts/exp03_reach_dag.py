"""$\\mathrm{reach}_F(p,e)$ を**一般 DAG 族**へ広げる（候補3 の続き）。

    python3 scripts/exp03_reach_dag.py --selftest              # 鎖で既存実装と全一致するか
    python3 scripts/exp03_reach_dag.py --family cbt --pmax 8 --emax 6
    python3 scripts/exp03_reach_dag.py --family pyramid --pmax 8 --emax 6

## なぜ新しく書くのか

`scripts/exp03_reach.py` の `reachable(n, p, e)` は**鎖専用**である。ランク付け `_ranker` が
「頂点 $i$ の先行点は $i-1$」という鎖の構造を前提にしており、候補手も
「ペブルの近傍だけ」に絞っている。定理 B2 `reach(p,e)=(e+2)2^{p-2}` は
**鎖でしか成り立っていない**ので、他の族を見るには一般 DAG のエンジンが要る。

## モデル（`scripts/landauer.py` と同一。`mode="ops"` 相当）

- 状態 = (ペブルの載っている頂点集合, 使った不可逆消去の回数 $u$)。
- 頂点 $v$ の先行点が全てペブル済みか `free` なら、$v$ の toggle（置く／取る）ができる。
- 先行点が揃っていないのに取り除くのが**不可逆消去**で、$u$ を 1 増やす（$u \\le e$）。
- clean 到達 = 最後に **target だけ**が載っている状態。

## 実装上の要点（既存の鎖版との違い）

1. **消去回数について 0-1 BFS**。可逆手をコスト 0、消去をコスト 1 として
   `deque` の前後に振り分けると、各ペブル集合は**最小の $u$ で確定**する。
   $(mask, u)$ が到達可能なら $u' \\ge u$ からの到達先はその部分集合なので、
   集合ごとに最小 $u$ だけ持てばよい（鎖版は $u$ ごとに訪問表を持っていた）。
   訪問表が $e+1$ 分の 1 になり、状態も減る。
2. **祖先への制限**。target の祖先でない頂点は clean 最適戦略では一度も置かれない
   （置けば終端までに必ず除く必要があり、純損）。消去を許しても同じ。
3. **打ち切りは `UNKNOWN`**。`False`（到達不能）と区別する。
   `~/.claude/rules` の「打ち切り値を結果と読まない」を型で強制する。

## 検証

`tests/test_exp03_reach_dag.py`（**実装より先に書いた**）が 3 本の柱で押さえる:
鎖で `exp03_reach.reachable` と全一致 / 既知の厳密値 $2^{p-1}$・$(e+2)2^{p-2}$ の再現 /
独立第 2 実装 `landauer.landauer_profile` と一般 DAG でも一致。
"""

from __future__ import annotations

import argparse
import os
import sys
import time
from collections import deque
from math import comb, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from revpebble import (  # noqa: E402
    Dag,
    chain,
    complete_binary_tree,
    pyramid,
    restrict_to_ancestors,
)
from families import kary_tree  # noqa: E402

DATA = ROOT / "data"


class _Unknown:
    """打ち切りで決まらなかったことを表す番人。`True`/`False`/`None` のいずれとも別物。

    `bool()` を禁じてあるので `if not r:` のような取り違えは実行時に落ちる。
    """

    __slots__ = ()

    def __repr__(self) -> str:
        return "UNKNOWN"

    def __bool__(self) -> bool:  # noqa: D105
        raise TypeError("UNKNOWN を真偽値として使わないこと（打ち切り≠到達不能）")


UNKNOWN = _Unknown()


class _Unreachable:
    """`emax` 以内では到達不能。**`False` を返してはいけない**ので専用の番人にする。

    `min_erasures_dag` は成功時に**消去回数**（`0` を含む）を返す。ここで失敗を `False`
    にすると `False == 0` が真なので、「消去 0 回で到達可能」と「到達不能」が
    `r == 0` で区別できなくなる。実際にこれで判定を 1 度間違えた（2026-08-11）。
    `__bool__` も `__eq__` も封じてあるので、取り違えは実行時に落ちる。
    """

    __slots__ = ()

    def __repr__(self) -> str:
        return "UNREACHABLE"

    def __bool__(self) -> bool:  # noqa: D105
        raise TypeError("UNREACHABLE を真偽値として使わないこと")

    def __eq__(self, other: object) -> bool:  # noqa: D105
        if other is self:
            return True
        raise TypeError("UNREACHABLE を == で比べないこと（`is UNREACHABLE` を使う）")

    __hash__ = object.__hash__


UNREACHABLE = _Unreachable()

DEFAULT_STATE_CAP = 60_000_000
DEFAULT_MEM_CAP = 3_000_000_000  # bytes（<host> の実装メモリは 7GB）


# ---------------------------------------------------------------------------
# ランク付け（一般版）
# ---------------------------------------------------------------------------


def _make_ranker(m: int, p: int):
    """$\\{0,\\dots,m-1\\}$ の大きさ $\\le p$ の部分集合を colex 順で整数に写す。

    返り値 `(rank, total)`。`total` は訪問表に要るバイト数でもある。
    """
    p = min(p, m)
    tbl = [[comb(i, j) if j <= i else 0 for j in range(p + 2)] for i in range(m + 1)]
    off = [0] * (p + 2)
    for k in range(1, p + 2):
        off[k] = off[k - 1] + (comb(m, k - 1) if k - 1 <= m else 0)
    total = off[p + 1]

    def rank(mask: int) -> int:
        # 立っているビットだけを走る（O(popcount) = O(p)）。
        # ビット長に比例させると m=48 あたりで支配的になる。
        r = 0
        k = 0
        while mask:
            low = mask & -mask
            k += 1
            r += tbl[low.bit_length() - 1][k]
            mask ^= low
        return off[k] + r

    return rank, total


# ---------------------------------------------------------------------------
# 一般 DAG の到達可能性
# ---------------------------------------------------------------------------


def reachable_dag(
    dag: Dag,
    target: int,
    p: int,
    e: int,
    *,
    state_cap: int | None = DEFAULT_STATE_CAP,
    mem_cap: int | None = DEFAULT_MEM_CAP,
    restrict: bool = True,
    stats: dict | None = None,
):
    """`dag` の `target` に、ピーク `p`・不可逆消去 `e` 回以内で clean 到達できるか。

    返り値は `True` / `False` / `UNKNOWN`。**`UNKNOWN` は「到達不能」ではない。**
    """
    if p < 1:
        return False
    if e < 0:
        raise ValueError("e >= 0")
    if e + 1 > 254:
        raise ValueError("e が大きすぎる（訪問表が 1 バイトに収まらない）")
    if target in dag.free:
        return True

    if restrict:
        dag, target = restrict_to_ancestors(dag, target)

    movable = dag.pebbleable()
    if target not in movable:
        return True
    m = len(movable)
    local = {v: i for i, v in enumerate(movable)}
    # need[i]: movable[i] を toggle するのに載っている必要のあるローカル頂点のマスク
    need = [0] * m
    for i, v in enumerate(movable):
        msk = 0
        for u in dag.preds[v]:
            if u not in dag.free:
                msk |= 1 << local[u]
        need[i] = msk
    goal = 1 << local[target]

    # 候補手の構造的な絞り込み（健全）。頂点 i を toggle できるのは
    #   (a) i にペブルが載っている（取る・消す）か
    #   (b) i が ready（置く）
    # のときだけ。(b) は「先行点が全て free」（＝常に ready）か、
    # さもなくば「載っているどれかの後続」に限られる。したがって
    #   cand = always_mask | mask | ⋃_{w ∈ mask} succ_mask[w]
    # に含まれない頂点は、この状態では絶対に動かせない。
    always_mask = 0
    for i in range(m):
        if need[i] == 0:
            always_mask |= 1 << i
    succ_mask = [0] * m
    for j in range(m):
        nj = need[j]
        while nj:
            low = nj & -nj
            succ_mask[low.bit_length() - 1] |= 1 << j
            nj ^= low

    p_eff = min(p, m)
    rank, total = _make_ranker(m, p_eff)
    if mem_cap is not None and total > mem_cap:
        if stats is not None:
            stats["reason"] = f"mem_cap: 訪問表 {total:,} バイト > 上限 {mem_cap:,}"
            stats["table_bytes"] = total
        return UNKNOWN

    seen = bytearray(total)          # 0 = 未訪問、それ以外は (最小 u)+1
    r0 = rank(0)
    seen[r0] = 1
    dq: deque[tuple[int, int, int]] = deque([(0, 0, r0)])
    settled = 0

    while dq:
        mask, u, rk = dq.popleft()
        if seen[rk] != u + 1:
            continue                  # 後からより小さい u で来ているので古い
        if mask == goal:
            if stats is not None:
                stats["settled"] = settled
                stats["table_bytes"] = total
            return True
        settled += 1
        if state_cap is not None and settled > state_cap:
            if stats is not None:
                stats["reason"] = f"state_cap: 確定状態 {settled:,} > 上限 {state_cap:,}"
                stats["settled"] = settled
                stats["table_bytes"] = total
            return UNKNOWN
        npeb = mask.bit_count()
        cand = always_mask | mask
        mm = mask
        while mm:
            low = mm & -mm
            cand |= succ_mask[low.bit_length() - 1]
            mm ^= low
        while cand:
            bit = cand & -cand
            cand ^= bit
            i = bit.bit_length() - 1
            ready = (need[i] & ~mask) == 0
            if mask & bit:
                if ready:
                    nm, nu = mask ^ bit, u
                elif u < e:
                    nm, nu = mask ^ bit, u + 1
                else:
                    continue
            elif ready and npeb < p_eff:
                nm, nu = mask | bit, u
            else:
                continue
            r = rank(nm)
            cur = seen[r]
            if cur == 0 or nu + 1 < cur:
                seen[r] = nu + 1
                if nu == u:
                    dq.appendleft((nm, nu, r))
                else:
                    dq.append((nm, nu, r))

    if stats is not None:
        stats["settled"] = settled
        stats["table_bytes"] = total
    return False


def min_erasures_dag(
    dag: Dag,
    target: int,
    p: int,
    emax: int,
    *,
    state_cap: int | None = DEFAULT_STATE_CAP,
    mem_cap: int | None = DEFAULT_MEM_CAP,
):
    """clean 到達に**最低いくつの不可逆消去が要るか**を返す（`emax` 以内で探す）。

    `reachable_dag` の 0-1 BFS は各ペブル集合を**最小の $u$ で確定**するので、
    goal を確定した時点の $u$ がそのまま答えになる。追加の探索は要らない。

    返り値: 整数（最小消去回数。**`0` もありうる**）／`UNREACHABLE`（`emax` 以内では
    到達不能）／`UNKNOWN`（打ち切り）。**`False` は返さない**（`False == 0` と衝突するため）。

    **なぜこれを見るか**: `reach_F(p,e)` を $e$ について掃くと、族の梯子が粗いときに
    「$e$ を増やしても値が動かない」区間が広く出る。それが**飽和**なのか
    **もっと多くの消去が要るだけ**なのかは、掃いた範囲だけからは区別できない。
    最小消去回数を直接聞けば区別がつく（`~/.claude/rules` の
    「打ち切り値を結果と読まない」の別の顔）。
    """
    if p < 1:
        return UNREACHABLE
    if emax + 1 > 254:
        raise ValueError("emax が大きすぎる（訪問表が 1 バイトに収まらない）")
    if target in dag.free:
        return 0
    dag, target = restrict_to_ancestors(dag, target)
    movable = dag.pebbleable()
    if target not in movable:
        return 0
    m = len(movable)
    local = {v: i for i, v in enumerate(movable)}
    need = [0] * m
    for i, v in enumerate(movable):
        msk = 0
        for u in dag.preds[v]:
            if u not in dag.free:
                msk |= 1 << local[u]
        need[i] = msk
    goal = 1 << local[target]
    always_mask = 0
    for i in range(m):
        if need[i] == 0:
            always_mask |= 1 << i
    succ_mask = [0] * m
    for j in range(m):
        nj = need[j]
        while nj:
            low = nj & -nj
            succ_mask[low.bit_length() - 1] |= 1 << j
            nj ^= low

    p_eff = min(p, m)
    rank, total = _make_ranker(m, p_eff)
    if mem_cap is not None and total > mem_cap:
        return UNKNOWN
    seen = bytearray(total)
    r0 = rank(0)
    seen[r0] = 1
    dq: deque[tuple[int, int, int]] = deque([(0, 0, r0)])
    settled = 0
    while dq:
        mask, u, rk = dq.popleft()
        if seen[rk] != u + 1:
            continue
        if mask == goal:
            return u                     # 0-1 BFS なのでこれが最小
        settled += 1
        if state_cap is not None and settled > state_cap:
            return UNKNOWN
        npeb = mask.bit_count()
        cand = always_mask | mask
        mm = mask
        while mm:
            low = mm & -mm
            cand |= succ_mask[low.bit_length() - 1]
            mm ^= low
        while cand:
            bit = cand & -cand
            cand ^= bit
            i = bit.bit_length() - 1
            ready = (need[i] & ~mask) == 0
            if mask & bit:
                if ready:
                    nm, nu = mask ^ bit, u
                elif u < emax:
                    nm, nu = mask ^ bit, u + 1
                else:
                    continue
            elif ready and npeb < p_eff:
                nm, nu = mask | bit, u
            else:
                continue
            r = rank(nm)
            cur = seen[r]
            if cur == 0 or nu + 1 < cur:
                seen[r] = nu + 1
                if nu == u:
                    dq.appendleft((nm, nu, r))
                else:
                    dq.append((nm, nu, r))
    return UNREACHABLE


# ---------------------------------------------------------------------------
# 族ごとの reach_F(p, e)
# ---------------------------------------------------------------------------

def fib_chain(n: int) -> Dag:
    """帯幅 2 の鎖: 頂点 $i\\ge1$ の先行点は $\\{i-1, i-2\\}$（頂点 0 が free）。

    **なぜこの族を足したか**（本スクリプトでの追加。cbt / pyramid だけでは答えられない）:
    鎖の法則 $\\mathrm{reach}(p,e)=(e+2)2^{p-2}$ は「族の添字 = 頂点数」で、
    梯子が 1 頂点刻みだから $e$ の効き方が細かく見える。cbt(h) や pyramid(h) は
    $h$ を 1 増やすと頂点数が跳ぶので、**同じ形の問いにならない**（$e$ を増やしても
    高さが上がらない領域が広く、飽和して見える）。
    そこで「1 頂点刻みで、しかも鎖ではない」最小の族として、先行点を 2 つ持つ鎖を置く。
    これなら $\\mathrm{reach}$ を鎖と同じ単位（頂点数）で比べられる。
    """
    preds = [frozenset()]
    for i in range(1, n + 1):
        preds.append(frozenset({0}) if i == 1 else frozenset({i - 1, i - 2}))
    return Dag(n=n + 1, preds=tuple(preds), free=frozenset({0}), name=f"fib({n})")


def caterpillar(n: int) -> Dag:
    """毛虫木: 背骨 $s_0(\\mathrm{free})\\to s_1\\to\\cdots\\to s_n$ に、各段で新しい葉
    $\\ell_i(\\mathrm{free})$ を合流させる（$s_i$ の先行点 $=\\{s_{i-1},\\ell_i\\}$）。

    **狙い**: 分岐（次数2の合流）は毎段あるが、深さ方向は鎖と同じ 1 頂点刻みで
    一直線に伸びる。「分岐の存在」と「分岐の繰り返し（再帰的な木の分岐）」を
    分離するための境界の族: これが飽和するなら原因は「分岐の存在」そのもの、
    飽和しないなら「木のように分岐を繰り返すこと」が原因だと切り分けられる。
    退化的二分木（"left-deep binary tree"）とも呼ばれる形。
    """
    # 頂点番号: 0 = s_0（free）、その後 (leaf_i, s_i) の対を i=1..n の順に並べる。
    preds: list[frozenset[int]] = [frozenset()]
    free = {0}
    prev_spine = 0
    for i in range(1, n + 1):
        leaf = len(preds)
        preds.append(frozenset())
        free.add(leaf)
        spine = len(preds)
        preds.append(frozenset({prev_spine, leaf}))
        prev_spine = spine
    return Dag(n=len(preds), preds=tuple(preds), free=frozenset(free),
                name=f"caterpillar({n})")


def branch1(n: int) -> Dag:
    """分岐が1か所だけの DAG: free 根から長さ $n$ の前置鎖、そこで2本の長さ $n$ の
    枝に分かれ、両枝の先端が合流した頂点が終端。

    途中で分岐が繰り返される木（cbt・pyramid）と違い、**分岐点は厳密に1個**。
    caterpillar（毎段分岐）・cbt（毎段分岐が倍加）との中間に置く。
    """
    assert n >= 0
    preds: list[frozenset[int]] = [frozenset()]
    free = {0}
    prev = 0
    for _ in range(n):
        v = len(preds)
        preds.append(frozenset({prev}))
        prev = v
    branch_point = prev
    tip_a = branch_point
    for _ in range(max(n, 1)):
        v = len(preds)
        preds.append(frozenset({tip_a}))
        tip_a = v
    tip_b = branch_point
    for _ in range(max(n, 1)):
        v = len(preds)
        preds.append(frozenset({tip_b}))
        tip_b = v
    preds.append(frozenset({tip_a, tip_b}))
    return Dag(n=len(preds), preds=tuple(preds), free=frozenset(free), name=f"branch1({n})")


def make_unbalanced(skew: int):
    """完全二分木(skew=0)と caterpillar(skew=h相当)を補間する不均衡二分木の族。

    `unbalanced_skew{k}(h)`: 根から数えて上位 `skew` 段は「片方だけ再帰し、
    もう片方は常に新しい free 葉」（caterpillar 型の合流）。残りの下位
    `h-skew` 段は通常の完全二分木のまま。`skew=0` は cbt(h) と同じゲーム
    （番号は違うが署名は同じはず）、`skew` を大きくするほど深さ方向に偏る。
    """
    assert skew >= 0

    def fam(h: int) -> Dag:
        preds: list[frozenset[int]] = []
        free: set[int] = set()

        def build_balanced(level: int) -> int:
            # 通常の完全二分木を level 段ぶん再帰的に作り、根の番号を返す。
            if level == 0:
                v = len(preds)
                preds.append(frozenset())
                free.add(v)
                return v
            left = build_balanced(level - 1)
            right = build_balanced(level - 1)
            v = len(preds)
            preds.append(frozenset({left, right}))
            return v

        def build(level: int) -> int:
            if level == 0:
                v = len(preds)
                preds.append(frozenset())
                free.add(v)
                return v
            if level > h - skew:
                # 上位 skew 段: 片方は新しい free 葉、片方だけ再帰する。
                leaf = len(preds)
                preds.append(frozenset())
                free.add(leaf)
                left = build(level - 1)
                v = len(preds)
                preds.append(frozenset({left, leaf}))
                return v
            return build_balanced(level)

        build(h)  # 根は常に最後に追加される頂点（= n-1）。規約どおり付け替え不要。
        return Dag(n=len(preds), preds=tuple(preds), free=frozenset(free),
                    name=f"unbalanced{skew}({h})")

    fam.__name__ = f"unbalanced{skew}"
    return fam


def make_diamond(w: int):
    """幅 $w$ 固定の帯 DAG（打ち切りピラミッド）: 行 0 は free（$w$ 本）。
    行 $i\\ge1$ の頂点 $j$（$0\\le j<w$）の先行点は、境界を折り返さずに
    $\\{(i-1,j-1),(i-1,j)\\}$（$j=0$ は $(i-1,0)$ のみ）。

    `cylinder` と違い巻いていない（境界で合流が欠ける）ので、真の意味で
    「有限幅の菱形格子」。`pyramid` は幅が段ごとに増え続けるが、こちらは
    幅 $w$ で頭打ちにしたまま高さだけ伸ばせる。終端は最終行の $j=w-1$。
    """
    assert w >= 1

    def fam(h: int) -> Dag:
        preds: list[frozenset[int]] = [frozenset() for _ in range(w)]
        free = set(range(w))
        prev_row = list(range(w))
        for _ in range(h):
            row = []
            for j in range(w):
                v = len(preds)
                if j == 0:
                    ps = frozenset({prev_row[0]})
                else:
                    ps = frozenset({prev_row[j - 1], prev_row[j]})
                preds.append(ps)
                row.append(v)
            prev_row = row
        # 終端は最終行の j=w-1（規約どおり最大番号 n-1 と一致する）。
        return Dag(n=len(preds), preds=tuple(preds), free=frozenset(free),
                    name=f"diamond{w}({h})")

    fam.__name__ = f"diamond{w}"
    return fam


def make_growing_diamond(width_fn, tag: str):
    """幅が段ごとに `width_fn(i)` に沿って**緩やかに増える**帯 DAG。

    `diamond{w}`（幅固定）と `pyramid`（幅が1段ごとに+1で増える）の中間として、
    「必要な同時幅が族のパラメータとともに増える」という飽和仮説を検定するために足す。
    `width_fn` は非減少・各段で高々 +1 だけ増える前提（それ以外は未対応）。

    幅が +1 増える段では、新しい free の「入力チャンネル」を1本足し、
    最終列だけそのチャンネルと前段最終列の合流にする（境界の折り返しはしない）。
    """

    def fam(h: int) -> Dag:
        w0 = width_fn(0)
        preds: list[frozenset[int]] = [frozenset() for _ in range(w0)]
        free = set(range(w0))
        prev_row = list(range(w0))
        for i in range(1, h + 1):
            w = width_fn(i)
            row: list[int] = []
            if w == len(prev_row):
                for j in range(w):
                    v = len(preds)
                    ps = (frozenset({prev_row[0]}) if j == 0
                          else frozenset({prev_row[j - 1], prev_row[j]}))
                    preds.append(ps)
                    row.append(v)
            elif w == len(prev_row) + 1:
                new_free = len(preds)
                preds.append(frozenset())
                free.add(new_free)
                for j in range(w):
                    v = len(preds)
                    if j == 0:
                        ps = frozenset({prev_row[0]})
                    elif j < len(prev_row):
                        ps = frozenset({prev_row[j - 1], prev_row[j]})
                    else:
                        ps = frozenset({prev_row[j - 1], new_free})
                    preds.append(ps)
                    row.append(v)
            else:
                raise ValueError(
                    f"{tag}: 幅が1段で{len(prev_row)}→{w}に飛んだ（+1 まで対応、i={i}）"
                )
            prev_row = row
        return Dag(n=len(preds), preds=tuple(preds), free=frozenset(free),
                    name=f"{tag}({h})")

    fam.__name__ = tag
    return fam


FAMILIES = {
    "chain": chain,
    "cbt": complete_binary_tree,
    "pyramid": pyramid,
    "fib": fib_chain,
    "caterpillar": caterpillar,
    "branch1": branch1,
    "unbalanced1": make_unbalanced(1),
    "unbalanced2": make_unbalanced(2),
    "unbalanced3": make_unbalanced(3),
    "diamond3": make_diamond(3),
    "diamond4": make_diamond(4),
    "diamond5": make_diamond(5),
    "kary2": lambda h: kary_tree(2, h),
    "kary3": lambda h: kary_tree(3, h),
    "kary4": lambda h: kary_tree(4, h),
    # 幅が sqrt(高さ) で緩やかに増える帯。diamond{w}（幅固定・飽和しない予想）と
    # pyramid（幅が高さに比例・飽和する既知）の中間で「幅の増え方と e0 の増え方が
    # 対応するか」を見るために足した（指揮者 2026-08-11 依頼）。
    "diamond_sqrt": make_growing_diamond(lambda i: 1 + isqrt(i), "diamond_sqrt"),
}


def exact_reach_family(
    family,
    p: int,
    e: int,
    *,
    kmax: int = 64,
    kmin: int = 0,
    confirm_extra: int = 1,
    state_cap: int | None = DEFAULT_STATE_CAP,
    mem_cap: int | None = DEFAULT_MEM_CAP,
    verbose: bool = False,
    detail: dict | None = None,
    memo: dict | None = None,
):
    """`reach_F(p,e) = max{k : F(k) が p ペブル e 消去で clean 可解}` を厳密に求める。

    単調性（`F(k)` が解ければ `F(k-1)` も解ける）を**仮定せず**、最初の失敗の先を
    `confirm_extra` 個だけ追加で調べる。追加分が解けたら非単調なので大声で報告する。

    返り値: 整数（確定）／`UNKNOWN`（打ち切りに当たって決まらなかった）。
    `detail` を渡すと各 k の判定と打ち切り理由が入る。
    """
    rows: list[tuple[int, object, dict]] = []
    last_true: int | None = None
    stop_k: int | None = None
    for k in range(kmin, kmax + 1):
        g = family(k)
        tgt = g.n - 1
        key = (id(family), k, p, e)
        if memo is not None and key in memo:
            r, st = memo[key]
        else:
            st = {}
            t0 = time.perf_counter()
            r = reachable_dag(g, tgt, p, e, state_cap=state_cap, mem_cap=mem_cap, stats=st)
            st["seconds"] = time.perf_counter() - t0
            if memo is not None:
                memo[key] = (r, st)
        rows.append((k, r, st))
        if verbose:
            print(f"      k={k:>3} {g.name:>12} n={g.n:>5} -> {r}  "
                  f"({st.get('settled', 0):,} 状態, {st['seconds']:.2f}s)", flush=True)
        if r is UNKNOWN:
            stop_k = k
            break
        if r:
            last_true = k
        else:
            stop_k = k
            break
    if detail is not None:
        detail["rows"] = rows
        detail["stop_k"] = stop_k
    if stop_k is None:
        # kmax まで全部解けた。上限に当たっているので確定していない。
        if detail is not None:
            detail["reason"] = f"kmax={kmax} まで全て可解（上限を上げる必要）"
        return UNKNOWN
    if rows[-1][1] is UNKNOWN:
        if detail is not None:
            detail["reason"] = rows[-1][2].get("reason", "打ち切り")
        return UNKNOWN
    # 非単調性の見張り
    nonmono = []
    for j in range(1, confirm_extra + 1):
        k = stop_k + j
        if k > kmax:
            break
        g = family(k)
        key = (id(family), k, p, e)
        if memo is not None and key in memo:
            r, st = memo[key]
        else:
            st = {}
            r = reachable_dag(g, g.n - 1, p, e, state_cap=state_cap,
                              mem_cap=mem_cap, stats=st)
            if memo is not None:
                memo[key] = (r, st)
        rows.append((k, r, st))
        if r is not UNKNOWN and r:
            nonmono.append(k)
    if nonmono:
        print(f"  ⚠ 非単調: p={p} e={e} で k={stop_k} は不可解なのに {nonmono} が可解")
        if detail is not None:
            detail["nonmonotone"] = nonmono
    return last_true if last_true is not None else -1


# ---------------------------------------------------------------------------


def selftest() -> int:
    """鎖で既存実装と全一致するか（軽い版。本番は tests/test_exp03_reach_dag.py）。"""
    import exp03_reach as e3

    bad = 0
    checked = 0
    for p in range(1, 6):
        for e in range(0, 4):
            for n in range(1, 25):
                want = e3.reachable(n, p, e)
                got = reachable_dag(chain(n), n, p, e)
                if got != want:
                    print(f"  MISMATCH chain({n}) p={p} e={e}: 新={got} 既存={want}")
                    bad += 1
                checked += 1
    print(f"  鎖の照合: {checked} 点中 不一致 {bad} 件")
    for p in range(2, 6):
        for e in range(0, 5):
            pred = (e + 2) * 2 ** (p - 2)
            ok = (reachable_dag(chain(pred), pred, p, e) is True
                  and reachable_dag(chain(pred + 1), pred + 1, p, e) is False)
            if not ok:
                print(f"  MISMATCH 定理 B2: p={p} e={e} 予想={pred}")
                bad += 1
    print(f"  定理 B2 の再現: 不一致 {bad} 件（累計）")
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--family", choices=sorted(FAMILIES))
    ap.add_argument("--pmin", type=int, default=2)
    ap.add_argument("--pmax", type=int, default=8)
    ap.add_argument("--emin", type=int, default=0)
    ap.add_argument("--emax", type=int, default=6)
    ap.add_argument("--kmax", type=int, default=12)
    ap.add_argument("--state-cap", type=int, default=DEFAULT_STATE_CAP)
    ap.add_argument("--mem-cap", type=int, default=DEFAULT_MEM_CAP)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--out", type=str, default=None, help="CSV 出力先")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    if not args.family:
        print("--selftest か --family {chain,cbt,pyramid} を指定してください")
        return 1

    fam = FAMILIES[args.family]
    print(f"== reach_{args.family}(p,e)  kmax={args.kmax} "
          f"state_cap={args.state_cap:,} mem_cap={args.mem_cap:,} ==", flush=True)
    # 出力は **1 点確定するごとに追記して flush** する。
    # 以前は最後にまとめて 1 回書いていたので、時間切れ・OOM・Ctrl-C で
    # それまでの計算が丸ごと消えた（実際に <host> の pyramid が 1.5 時間走って
    # CSV が空のままだった）。長時間ジョブで「全部か無か」の出力にしてはいけない。
    out_fh = None
    if args.out:
        # 相対パスは**リポジトリルート基準**に直す。cwd がリポジトリ外だと
        # 存在しないディレクトリへ落ちて完走時に書けずに捨てることになる。
        out_path = Path(args.out)
        if not out_path.is_absolute():
            out_path = ROOT / out_path
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_fh = out_path.open("w", encoding="utf-8", buffering=1)
        out_fh.write("family,p,e,reach,status,reason\n")
        out_fh.flush()
        print(f"  追記先: {out_path}", flush=True)

    memo: dict = {}
    try:
        for p in range(args.pmin, args.pmax + 1):
            for e in range(args.emin, args.emax + 1):
                det: dict = {}
                t0 = time.perf_counter()
                r = exact_reach_family(fam, p, e, kmax=args.kmax,
                                       state_cap=args.state_cap, mem_cap=args.mem_cap,
                                       verbose=args.verbose, detail=det, memo=memo)
                dt = time.perf_counter() - t0
                if r is UNKNOWN:
                    status, val = "UNKNOWN", ""
                    reason = det.get("reason", "")
                else:
                    status, val = "exact", str(r)
                    reason = ""
                print(f"  p={p} e={e}: reach={val or 'UNKNOWN':>6}  [{status}] "
                      f"{dt:.1f}s  {reason}", flush=True)
                if out_fh is not None:
                    out_fh.write(f"{args.family},{p},{e},{val},{status},"
                                 f"\"{reason}\"\n")
                    out_fh.flush()
                    os.fsync(out_fh.fileno())
    finally:
        if out_fh is not None:
            out_fh.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
