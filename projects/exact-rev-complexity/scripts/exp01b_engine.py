"""候補1 用の高速エンジン（`revpebble.py` は編集せずラップする）。

`revpebble.bfs` は状態を `frozenset` で持つため、頂点数が 15 を超えると
メモリと定数倍で行き詰まる。ここでは**同じモデル**を

  - 状態 = 頂点集合のビットマスク（int）
  - 遷移 = 前計算した (bit, need_mask) の組
  - 双方向 BFS（トグル規則より状態グラフは無向なので合法）

で書き直す。`tests/test_exp01b.py` が `revpebble.bfs` との完全一致を全 p で確認する。

重要な観測: 状態空間は $2^{|V|}$ ではなく **ピーク上限 p で切った $\\sum_{k\\le p}\\binom{n}{k}$**
に収まる。$p$ は $\\log$ オーダーなのでこれは劇的に小さい。
（`docs/idea01_trees_dags.md` §3 の「素朴 BFS は $|V|\\le24$ が限界」は
$2^{|V|}$ 見積りに基づく過小評価だった。）

新しい族 `spinal_tree`, `butterfly` もここに追加する（Královič が空間を与えている族）。
"""

from __future__ import annotations

import sys
from collections import deque
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag  # noqa: E402


# ---------------------------------------------------------------------------
# グラフ族（revpebble.py の chain/complete_binary_tree/pyramid の補完）
# ---------------------------------------------------------------------------


def spinal_tree(k: int) -> Dag:
    """spinal tree $S_k$: 長さ $k$ の背骨の各節点に葉が1枚付く。葉は free。

    $s_1$ は葉2枚を子に持ち、$s_i$ ($i\\ge2$) は $s_{i-1}$ と葉 $l_i$ を子に持つ。
    頂点数 $2k+1$、根は $s_k$（= 最大番号）。深さ $k$ だが幅は 2 で一定。
    """
    assert k >= 1
    preds: list[frozenset[int]] = [frozenset(), frozenset(), frozenset({0, 1})]
    leaves = [0, 1]
    spine = 2
    for _ in range(2, k + 1):
        leaf = len(preds)
        preds.append(frozenset())
        leaves.append(leaf)
        preds.append(frozenset({spine, leaf}))
        spine = len(preds) - 1
    return Dag(n=len(preds), preds=tuple(preds), free=frozenset(leaves), name=f"spinal({k})")


def butterfly(k: int) -> Dag:
    """バタフライ $BF_k$: $k+1$ 段 × $2^k$ 頂点。段 0 が free、終端は最終段の最終頂点。

    段 $i+1$ の頂点 $j$ は段 $i$ の $j$ と $j \\oplus 2^i$ を先行点に持つ
    （FFT のバタフライ。Královič が可逆ペブル空間を与えている族）。
    """
    assert k >= 1
    w = 2**k
    n = (k + 1) * w
    preds: list[frozenset[int]] = [frozenset() for _ in range(n)]
    for i in range(k):
        for j in range(w):
            v = (i + 1) * w + j
            preds[v] = frozenset({i * w + j, i * w + (j ^ (1 << i))})
    return Dag(n=n, preds=tuple(preds), free=frozenset(range(w)), name=f"butterfly({k})")


def all_pebbled(g: Dag) -> Dag:
    """free を空にした版（exp01 の "all-pebbled" 流儀）。"""
    from dataclasses import replace

    return replace(g, free=frozenset(), name=f"{g.name}*")


# ---------------------------------------------------------------------------
# コンパイル済み表現
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Compiled:
    """BFS 用に前計算した DAG。`moves[i] = (bit, need)`。"""

    moves: tuple[tuple[int, int], ...]
    n_move: int
    name: str

    @property
    def free_mask(self) -> int:
        return self._free

    _free: int = 0


def compile_dag(g: Dag) -> Compiled:
    free_mask = 0
    for v in g.free:
        free_mask |= 1 << v
    moves: list[tuple[int, int]] = []
    for v in g.pebbleable():
        need = 0
        for u in g.preds[v]:
            if u not in g.free:
                need |= 1 << u
        moves.append((1 << v, need))
    return Compiled(moves=tuple(moves), n_move=len(moves), name=g.name, _free=free_mask)


# ---------------------------------------------------------------------------
# 探索
# ---------------------------------------------------------------------------


def _expand(state: int, moves: tuple[tuple[int, int], ...], p: int, pc: int) -> list[int]:
    out: list[int] = []
    can_add = pc < p
    for bit, need in moves:
        if state & need != need:
            continue
        if state & bit:
            out.append(state ^ bit)
        elif can_add:
            out.append(state | bit)
    return out


def mstar_mask(g: Dag, goal: int, p: int, *, cap: int | None = None) -> int | None:
    """最小手数（終端が**頂点集合** `goal`（ビットマスク）の版）。到達不能なら None。

    双方向 BFS。`cap` を与えると訪問状態数がそれを超えた時点で
    `MemoryError` ではなく `RuntimeError` を投げる（暴走防止）。

    バタフライのように「全出力を同時にペブルした clean 状態」を終端に取る族のため、
    単一終端 `mstar` を一般化してある（`revpebble.bfs` は単一終端のみ）。
    """
    c = compile_dag(g)
    goal &= ~c.free_mask  # free 頂点は数えない
    if goal == 0:
        return 0
    if p < 1:
        return None
    if goal.bit_count() > p:
        return None
    moves = c.moves

    # 目標側の初期状態が合法か（need が満たされていなくても状態としては存在しうる）
    fwd_seen: dict[int, int] = {0: 0}
    bwd_seen: dict[int, int] = {goal: 0}
    fwd: list[int] = [0]
    bwd: list[int] = [goal]
    df = db = 0

    while fwd and bwd:
        # 小さい側を伸ばす
        if len(fwd) <= len(bwd):
            nxt: list[int] = []
            for s in fwd:
                pc = s.bit_count()
                for t in _expand(s, moves, p, pc):
                    if t not in fwd_seen:
                        fwd_seen[t] = df + 1
                        nxt.append(t)
            df += 1
            fwd = nxt
            for t in fwd:
                if t in bwd_seen:
                    return df + bwd_seen[t]
        else:
            nxt = []
            for s in bwd:
                pc = s.bit_count()
                for t in _expand(s, moves, p, pc):
                    if t not in bwd_seen:
                        bwd_seen[t] = db + 1
                        nxt.append(t)
            db += 1
            bwd = nxt
            for t in bwd:
                if t in fwd_seen:
                    return db + fwd_seen[t]
        if cap is not None and len(fwd_seen) + len(bwd_seen) > cap:
            raise RuntimeError(
                f"状態数が cap={cap} を超えた（{g.name}, p={p}）: 到達できなかった"
            )
    return None


def mstar(g: Dag, target: int, p: int, *, cap: int | None = None) -> int | None:
    """最小手数 $M^*(g,\\text{target},p)$（単一終端）。`revpebble.bfs` と一致する。"""
    return mstar_mask(g, 1 << target, p, cap=cap)


def bfs_dist(g: Dag, p: int, *, cap: int | None = None) -> dict[int, int]:
    """空状態からの単方向 BFS 距離表（スケジュール復元用）。"""
    c = compile_dag(g)
    dist = {0: 0}
    q = deque([0])
    while q:
        s = q.popleft()
        d = dist[s]
        pc = s.bit_count()
        for t in _expand(s, c.moves, p, pc):
            if t not in dist:
                dist[t] = d + 1
                q.append(t)
        if cap is not None and len(dist) > cap:
            raise RuntimeError(f"状態数が cap={cap} を超えた（{g.name}, p={p}）")
    return dist


# ---------------------------------------------------------------------------
# Královič 2004 の「complete computation」流儀（我々の clean-reach とは別物）
# ---------------------------------------------------------------------------
#
# Královič 2004 の定義（本文精読・2026-07-27）。**2 つの量を混同しないこと。**
#
#   R1/R2（§2, p.139） = 我々と同じ toggle 規則（先行点が全てペブル済みなら置ける・取れる）。
#
#   (A) **complete computation**（§2, p.139）= 最初と最後の配置が空で、かつ
#       **各頂点が途中のどこかでペブルされている**計算。最小空間 $S_{\\min}(G)$、最小時間 $T(G,s)$。
#
#   (B) **semicomplete computation**（Def 4.1, p.147）= 空から始まり、
#       最後の配置が $\\mathrm{Put}(E, \\mathrm{root}, 1)$ =
#       **「根だけがペブルされた配置」**である計算。最小空間 $S'_{\\min}(h)$。
#
# **(B) は我々の clean-reach と完全に同一である。** つまり
#
#     我々の $p_{\\min}(G)$ = 彼の $S'_{\\min}$ 、  我々の $M^*(G,p)$ = (B) の最小時間
#
# （我々の $M^*$ に対応する量は彼の論文には**表も式も無い**。彼は木・バタフライについて
#  空間のみを扱っている: §4 冒頭「we shall discuss the space complexity」。）
#
# 一方 (A) は別の量で、こちらが本モジュールの `smin_kralovic` / `tmin_kralovic`。
# 目標が唯一の sink である DAG（木・ピラミッド）では、根を置くには両方の子が同時に
# ペブル済みでなければならず、再帰的に全祖先が過去にペブルされている。全頂点が根の
# 祖先なので「全頂点がどこかでペブルされる」⟺「根がどこかでペブルされる」。
# さらに状態グラフが無向なので「空→根を含む配置→空」の最小長は片道の 2 倍。よって
#
#     S_min(G)（彼, (A)） = 「根を含む**何らかの**配置が空から到達可能な最小ピーク」
#     T(G,s)（彼, (A)）   = 2 × 「空から根を含む何らかの配置への最小手数」
#
# (A) は (B) より易しい（clean にする手間が要らない）。彼の Lem 4.2/4.3 が両者を結ぶ:
#     Lem 4.2: $S_{\\min}(h) \\le S'_{\\min}(h) \\le S_{\\min}(h)+1$
#     Lem 4.3: $S'_{\\min}(h+1) = S_{\\min}(h) + 2$
#
# `tests/test_exp01d_kralovic.py` が彼の Thm 3.1・Lem 4.2・Lem 4.3・Lem 4.10/4.11 と
# 先行プロジェクトの完全計算変種の値で、この読みを検証する。


def reach_target_dist(g: Dag, target: int, p: int, *, cap: int | None = None) -> int | None:
    """$\\varnothing$ から「target がペブル済みの**何らかの**配置」への最小手数。

    Královič の semicomplete computation の時間。clean である必要はない。到達不能なら None。
    """
    c = compile_dag(g)
    if (1 << target) & c.free_mask:
        return 0
    if p < 1:
        return None
    bit = 1 << target
    seen = {0}
    frontier = [0]
    d = 0
    while frontier:
        nxt: list[int] = []
        for s in frontier:
            pc = s.bit_count()
            for t in _expand(s, c.moves, p, pc):
                if t in seen:
                    continue
                if t & bit:
                    return d + 1
                seen.add(t)
                nxt.append(t)
        d += 1
        frontier = nxt
        if cap is not None and len(seen) > cap:
            raise RuntimeError(f"状態数が cap={cap} を超えた（{g.name}, p={p}）")
    return None


def smin_kralovic(g: Dag, target: int, pmax: int = 40) -> int | None:
    """Královič の $S_{\\min}(G)$（complete computation の最小空間）。

    上の同値性により「target を含む配置が空から到達可能な最小ピーク」。
    """
    for p in range(1, pmax + 1):
        if reach_target_dist(g, target, p) is not None:
            return p
    return None


def tmin_kralovic(g: Dag, target: int, p: int, *, cap: int | None = None) -> int | None:
    """Královič の $T(G,p)$（complete computation の最小時間）= 片道の最小手数の 2 倍。"""
    d = reach_target_dist(g, target, p, cap=cap)
    return None if d is None else 2 * d


def pmin_mask(g: Dag, goal: int, pmax: int = 40) -> int | None:
    """clean に頂点集合 `goal` へ到達できる最小ピーク。"""
    for p in range(1, pmax + 1):
        if mstar_mask(g, goal, p) is not None:
            return p
    return None


def pmin(g: Dag, target: int, pmax: int = 40) -> int | None:
    """clean に target へ到達できる最小ピーク。"""
    return pmin_mask(g, 1 << target, pmax)


def mstar_pmin(g: Dag, target: int) -> tuple[int | None, int | None]:
    p = pmin(g, target)
    if p is None:
        return (None, None)
    return (p, mstar(g, target, p))


def schedule_mask(g: Dag, goal: int, p: int) -> list[tuple[str, int]] | None:
    """最適スケジュールを1本復元する（("put"|"take", 頂点) の列）。

    距離表から後退復元する（親ポインタを持たないのでメモリが軽い）。
    """
    c = compile_dag(g)
    goal &= ~c.free_mask
    dist = bfs_dist(g, p)
    if goal not in dist:
        return None
    seq: list[tuple[str, int]] = []
    cur = goal
    while cur != 0:
        d = dist[cur]
        pc = cur.bit_count()
        for t in _expand(cur, c.moves, p, pc):
            if dist.get(t) == d - 1:
                bit = cur ^ t
                v = bit.bit_length() - 1
                seq.append(("put" if cur & bit else "take", v))
                cur = t
                break
        else:  # pragma: no cover
            raise AssertionError("距離表が不整合")
    seq.reverse()
    return seq


def schedule(g: Dag, target: int, p: int) -> list[tuple[str, int]] | None:
    return schedule_mask(g, 1 << target, p)


def verify_schedule_mask(g: Dag, goal: int, p: int, seq: list[tuple[str, int]]) -> None:
    """スケジュールがモデルの規則を満たすか独立に検証する（AssertionError で失敗）。"""
    want = {v for v in range(g.n) if (goal >> v) & 1 and v not in g.free}
    state: set[int] = set()
    for i, (kind, v) in enumerate(seq):
        assert v not in g.free, f"{i}: free 頂点 {v} を動かした"
        for u in g.preds[v]:
            assert (u in g.free) or (u in state), f"{i}: 先行点 {u} が未ペブル"
        if kind == "put":
            assert v not in state, f"{i}: 既にペブル済み {v}"
            state.add(v)
        else:
            assert v in state, f"{i}: ペブルされていない {v} を取った"
            state.discard(v)
        assert len(state) <= p, f"{i}: ピーク超過 {len(state)} > {p}"
    assert state == want, f"終状態が clean でない: {sorted(state)} != {sorted(want)}"


def verify_schedule(g: Dag, target: int, p: int, seq: list[tuple[str, int]]) -> None:
    verify_schedule_mask(g, 1 << target, p, seq)


if __name__ == "__main__":  # 手動確認
    import time

    for h in range(1, 7):
        g = all_pebbled(__import__("revpebble").pyramid(h))
        t0 = time.time()
        p, m = mstar_pmin(g, g.n - 1)
        print(f"{g.name}: V={g.n} p_min={p} M*={m}  ({time.time()-t0:.1f}s)")
