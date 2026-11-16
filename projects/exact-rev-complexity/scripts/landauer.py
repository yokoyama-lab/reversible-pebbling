"""$e$-Landauer ペブリングゲームの厳密 BFS エンジン（候補3）。

## モデル

基本は `scripts/revpebble.py` の clean reversible pebbling game。そこへ
**不可逆消去**（先行点が揃っていない状態でペブルを取り除く操作）を有限予算で許す。

先行研究との関係（重要・`docs/idea03_landauer_interpolation.md` §2 を参照）:
Li–Tromp–Vitányi 1997/1998（Physica D 120:168–176, doi:10.1016/S0167-2789(98)00052-9）
の **m-erasure pebble game** が本質的に同じルールを既に定義している:

    「In at most m steps the player can remove a pebble from any node i > 1
      without node i - 1 being pebbled at the time.」

したがって定義そのものは新規ではない。本モジュールが新しく計算するのは
**手数（時間）を消去予算の関数として厳密に最小化した値** であり、LTV は
空間 vs 消去回数の漸近上界しか与えていない。

## 消去の数え方（2 変種を明示的に区別する）

- `mode="ops"`（LTV 準拠）: 不可逆消去は **1 手で 1 個のペブル** を消す操作。
  予算 $e$ は「不可逆消去の**回数**」を数える。1 回 = 1 手 = 1 ビット。
- `mode="bits"`: 追加で **一括消去**（現在ペブルの載っている任意の部分集合 $A$,
  $|A|\ge 2$ を同時に消す）を許す。時間コストは **1 手**、消去コストは
  **$|A|$ ビット**。予算 $e$ は「消去した**ビット数**」を数える。

Landauer 原理が課すコストはビット数（$|A| kT\ln 2$）なので `bits` の方が
物理的に忠実、`ops` は文献互換。$M^*_{\text{bits}} \le M^*_{\text{ops}}$ が常に成り立つ。

## 両端の整合性（テストで固定）

- $e=0$: 通常の可逆ペブリング（`revpebble.bfs` に一致）。
- $e$ 十分大: 標準ペブリング（取り除き自由）の clean 最小手数（`standard_bfs` に一致）。
"""

from __future__ import annotations

import sys
from collections import deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag, chain, complete_binary_tree, pyramid  # noqa: E402,F401

MODES = ("ops", "bits")


def _compile(dag: Dag) -> tuple[int, tuple[int, ...], tuple[int, ...]]:
    """(free のビットマスク, 頂点ごとの先行点マスク, 動かせる頂点) を返す。"""
    free_mask = 0
    for v in dag.free:
        free_mask |= 1 << v
    pred_mask = tuple(
        (lambda ps: sum(1 << u for u in ps))(dag.preds[v]) for v in range(dag.n)
    )
    movable = tuple(v for v in range(dag.n) if v not in dag.free)
    return free_mask, pred_mask, movable


def _subsets(mask: int):
    """mask の空でない部分集合を列挙する（mask 自身を含む）。"""
    sub = mask
    while sub:
        yield sub
        sub = (sub - 1) & mask


# ---------------------------------------------------------------------------
# 主実装: 1 回の BFS で e=0..emax の全プロファイルを得る
# ---------------------------------------------------------------------------


def landauer_profile(
    dag: Dag,
    target: int,
    p: int,
    emax: int,
    mode: str = "ops",
) -> list[int | None]:
    """$M^*(dag, target, p, e)$ を $e = 0..emax$ について一括で返す。

    状態 = (ペブル集合のビットマスク, 使用済み消去量)。全ての手のコストは 1 手なので
    素の BFS で最短手数が出る。返り値 `out[e]` は消去量 $\\le e$ での最小手数
    （到達不能なら None）。定義上 $e$ について単調非増加になる。
    """
    if mode not in MODES:
        raise ValueError(f"unknown mode: {mode}")
    free_mask, pred_mask, movable = _compile(dag)
    goal = 1 << target
    if target in dag.free:
        return [0] * (emax + 1)
    if p < 1:
        return [None] * (emax + 1)

    width = emax + 1
    best: list[int | None] = [None] * width  # best[used] = goal に着いた最短手数
    dist: dict[int, int] = {0: 0}  # key = state * width + used
    queue: deque[int] = deque([0])

    while queue:
        key = queue.popleft()
        d = dist[key]
        state, used = divmod(key, width)
        if state == goal:
            if best[used] is None:
                best[used] = d
            # goal から更に進んでも手数は増えるだけなので展開不要
            continue
        npeb = state.bit_count()
        for v in movable:
            bit = 1 << v
            ready = (pred_mask[v] & ~(state | free_mask)) == 0
            if bit & state:
                if ready:  # 可逆な取り除き
                    nk = (state ^ bit) * width + used
                    if nk not in dist:
                        dist[nk] = d + 1
                        queue.append(nk)
                elif used + 1 <= emax:  # 不可逆消去（1 ビット）
                    nk = (state ^ bit) * width + used + 1
                    if nk not in dist:
                        dist[nk] = d + 1
                        queue.append(nk)
            elif ready and npeb + 1 <= p:  # 置く
                nk = (state | bit) * width + used
                if nk not in dist:
                    dist[nk] = d + 1
                    queue.append(nk)
        if mode == "bits" and npeb >= 2:
            # 一括消去: 部分集合 A（|A|>=2）を同時に消す。1 手・|A| ビット。
            for sub in _subsets(state):
                k = sub.bit_count()
                if k < 2 or used + k > emax:
                    continue
                nk = (state ^ sub) * width + used + k
                if nk not in dist:
                    dist[nk] = d + 1
                    queue.append(nk)

    out: list[int | None] = []
    run: int | None = None
    for e in range(width):
        cand = best[e]
        if cand is not None and (run is None or cand < run):
            run = cand
        out.append(run)
    return out


# ---------------------------------------------------------------------------
# 二重実装: 予算 e ごとに独立した BFS を回す素朴版（照合用）
# ---------------------------------------------------------------------------


def landauer_bfs(
    dag: Dag,
    target: int,
    p: int,
    e: int,
    mode: str = "ops",
) -> int | None:
    """予算 $e$ 固定で $M^*$ を求める素朴 BFS（`landauer_profile` の照合用）。

    frozenset を使い、`landauer_profile` とは別の状態表現・別のループ構造で書く。
    """
    if mode not in MODES:
        raise ValueError(f"unknown mode: {mode}")
    if target in dag.free:
        return 0
    if p < 1:
        return None
    goal = frozenset({target})
    start: tuple[frozenset[int], int] = (frozenset(), 0)
    dist: dict[tuple[frozenset[int], int], int] = {start: 0}
    queue: deque[tuple[frozenset[int], int]] = deque([start])
    movable = dag.pebbleable()

    def ready(state: frozenset[int], v: int) -> bool:
        return all((u in dag.free) or (u in state) for u in dag.preds[v])

    while queue:
        cur = queue.popleft()
        state, used = cur
        d = dist[cur]
        if state == goal:
            return d
        nexts: list[tuple[frozenset[int], int]] = []
        for v in movable:
            if v in state:
                if ready(state, v):
                    nexts.append((state - {v}, used))
                elif used < e:
                    nexts.append((state - {v}, used + 1))
            elif ready(state, v) and len(state) < p:
                nexts.append((state | {v}, used))
        if mode == "bits" and len(state) >= 2:
            items = sorted(state)
            for code in range(1, 1 << len(items)):
                sub = {items[i] for i in range(len(items)) if code >> i & 1}
                if len(sub) < 2 or used + len(sub) > e:
                    continue
                nexts.append((state - sub, used + len(sub)))
        for nxt in nexts:
            if nxt not in dist:
                dist[nxt] = d + 1
                queue.append(nxt)
    return None


# ---------------------------------------------------------------------------
# 最適スケジュールの抽出（予想 A の証明の構造補題を実データで検査するため）
# ---------------------------------------------------------------------------


def landauer_schedule(
    dag: Dag,
    target: int,
    p: int,
    e: int,
) -> list[tuple[str, int]] | None:
    """予算 $e$ 以内の最適スケジュールを 1 本抽出する（`mode="ops"` のみ）。

    返り値は `("put"|"take"|"erase", 頂点)` の列（`erase` = 不可逆消去）。
    `data/exp03_results.md` の予想 A の証明で使う構造補題
    （$2n-1$ 手なら各点ちょうど 1 回 put/take・put は昇順・
    不可逆消去の回数 = 取り除き時刻列の上昇数）を実データで検査するのに使う。
    """
    free_mask, pred_mask, movable = _compile(dag)
    goal = 1 << target
    if target in dag.free:
        return []
    if p < 1:
        return None
    width = e + 1
    dist: dict[int, int] = {0: 0}
    parent: dict[int, tuple[int, str, int]] = {}
    queue: deque[int] = deque([0])
    end: int | None = None
    while queue:
        key = queue.popleft()
        d = dist[key]
        state, used = divmod(key, width)
        if state == goal:
            end = key
            break
        npeb = state.bit_count()
        for v in movable:
            bit = 1 << v
            ready = (pred_mask[v] & ~(state | free_mask)) == 0
            if bit & state:
                if ready:
                    nk, act = (state ^ bit) * width + used, "take"
                elif used + 1 <= e:
                    nk, act = (state ^ bit) * width + used + 1, "erase"
                else:
                    continue
            elif ready and npeb + 1 <= p:
                nk, act = (state | bit) * width + used, "put"
            else:
                continue
            if nk not in dist:
                dist[nk] = d + 1
                parent[nk] = (key, act, v)
                queue.append(nk)
    if end is None:
        return None
    seq: list[tuple[str, int]] = []
    cur = end
    while cur in parent:
        prev, act, v = parent[cur]
        seq.append((act, v))
        cur = prev
    seq.reverse()
    return seq


def analyse_chain_schedule(n: int, seq: list[tuple[str, int]]) -> dict:
    """鎖の最適スケジュールを予想 A の証明の言葉に翻訳する。

    返り値のキー:
      `moves` 手数, `rigid` 各点ちょうど 1 回 put / 1..n-1 が 1 回 take か,
      `puts_sorted` put が昇順か, `tau` 取り除き時刻の列 $\\tau(1..n-1)$,
      `ascents` $\\#\\{i\\in[2,n-1] : \\tau(i)>\\tau(i-1)\\}$,
      `erasures` 実際の `erase` の回数, `runs` $\\tau$ の極大下降連の長さのリスト。
    """
    puts = [v for a, v in seq if a == "put"]
    removes = [(t, v, a) for t, (a, v) in enumerate(seq) if a in ("take", "erase")]
    tau: dict[int, int] = {}
    for t, v, _a in removes:
        tau.setdefault(v, t)
    rigid = (
        sorted(puts) == list(range(1, n + 1))
        and len(puts) == n
        and sorted(v for _t, v, _a in removes) == list(range(1, n))
    )
    ascents = 0
    if rigid:
        ascents = sum(1 for i in range(2, n) if tau[i] > tau[i - 1])
    runs: list[int] = []
    if rigid and n >= 2:
        cur = 1
        for i in range(2, n):
            if tau[i] < tau[i - 1]:
                cur += 1
            else:
                runs.append(cur)
                cur = 1
        runs.append(cur)
    return {
        "moves": len(seq),
        "rigid": rigid,
        "puts_sorted": puts == sorted(puts),
        "tau": [tau.get(i) for i in range(1, n)],
        "ascents": ascents,
        "erasures": sum(1 for a, _v in seq if a == "erase"),
        "runs": runs,
    }


# ---------------------------------------------------------------------------
# 標準ペブリング（e = ∞ の極）
# ---------------------------------------------------------------------------


def standard_bfs(dag: Dag, target: int, p: int, *, bulk: bool = False) -> int | None:
    """標準（黒）ペブリングの clean 最小手数。取り除きは常に自由。

    置く: 先行点が全てペブル済み（または free）かつ同時数 $\\le p$。
    取る: いつでも自由。終端は目標頂点のみがペブル済みの clean 状態。

    `bulk=False` が $e=\\infty$ での `mode="ops"` の極、
    `bulk=True`（1 手で任意個のペブルを同時に取り除ける）が `mode="bits"` の極。
    一括消去は標準ペブリングより強い原始操作なので、両者を区別しないと
    上端の整合性テストが（実装ではなく期待値の側で）壊れる。
    """
    free_mask, pred_mask, movable = _compile(dag)
    goal = 1 << target
    if target in dag.free:
        return 0
    if p < 1:
        return None
    dist = {0: 0}
    queue = deque([0])
    while queue:
        state = queue.popleft()
        d = dist[state]
        if state == goal:
            return d
        npeb = state.bit_count()
        for v in movable:
            bit = 1 << v
            if bit & state:
                nxt = state ^ bit
            elif (pred_mask[v] & ~(state | free_mask)) == 0 and npeb + 1 <= p:
                nxt = state | bit
            else:
                continue
            if nxt not in dist:
                dist[nxt] = d + 1
                queue.append(nxt)
        if bulk and npeb >= 2:
            for sub in _subsets(state):
                if sub.bit_count() < 2:
                    continue
                nxt = state ^ sub
                if nxt not in dist:
                    dist[nxt] = d + 1
                    queue.append(nxt)
    return None


# ---------------------------------------------------------------------------
# 導出量
# ---------------------------------------------------------------------------


def saturation(profile: list[int | None]) -> int | None:
    """飽和点 $e^*$: これ以上 $e$ を増やしても手数が減らない最小の $e$。

    プロファイルの末尾値に初めて到達する添字。プロファイル全体が None なら None。
    末尾まで単調に減り続けている場合（= emax が足りない）も末尾添字を返すので、
    呼び出し側は `profile[-1] == profile[-2]` で飽和の確認をすること。
    """
    if profile[-1] is None:
        return None
    final = profile[-1]
    for e, val in enumerate(profile):
        if val == final:
            return e
    return None


def is_monotone(profile: list[int | None]) -> bool:
    """$e$ について単調非増加か（None は +∞ 扱い）。"""
    prev: int | None = None
    for val in profile:
        if val is None:
            if prev is not None:
                return False
        else:
            if prev is not None and val > prev:
                return False
            prev = val
    return True


def pmin_e(dag: Dag, target: int, e: int, pmax: int = 30, mode: str = "ops") -> int | None:
    """消去予算 $e$ の下で clean 到達できる最小ピーク $p$。"""
    for p in range(1, pmax + 1):
        if landauer_profile(dag, target, p, e, mode=mode)[e] is not None:
            return p
    return None


def reach_e(p: int, e: int, nmax: int = 64, mode: str = "ops") -> int:
    """ピーク $p$・消去予算 $e$ で clean 到達できる最大の鎖長。

    $e=0$ では既知の $\\mathrm{reach}(p)=2^{p-1}$（Královič 2001 Thm 3.1 の系）。
    LTV Lemma 1 は $p$ 本＋$m-1$ 回の消去で長さ $m 2^{p-2}$ を主張する（上界の構成）。
    """
    best = 0
    for n in range(1, nmax + 1):
        if landauer_profile(chain(n), n, p, e, mode=mode)[e] is None:
            break
        best = n
    return best


if __name__ == "__main__":  # 手動確認用
    print("chain(8) p=p_min=4, mode=ops, e=0..6:")
    print("  ", landauer_profile(chain(8), 8, 4, 6))
    print("standard_bfs chain(8) p=2..4:", [standard_bfs(chain(8), 8, p) for p in (2, 3, 4)])
