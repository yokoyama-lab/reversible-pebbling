"""消去予算つき可逆ペブリングの商木 BFS — reach_cbt(p, e) の判定。

## 目的（docs/25 §7.5 の決定点）

p=9 で e=0 の reach が 6 に落ちた（第 3 ジャンプ、§7）。標準ペブリング側の
飽和値は 8 なのでギャップは 2 段。**e=1 が 1 段買い戻すのか 2 段買い戻すのか**
（reach_cbt(9,1) ∈ {6,7,8} のどれか）が「消去はジャンプを何段消せるか」の
最初の判定点になる。

## 商の妥当性（消去があっても壊れない理由）

Aut(完全二分木) は「子根が揃っているか」という局所条件を保つので、
put / 可逆 take / erase のいずれも Aut 同変:
σC1 →(move) σC2 は同じ種別・同じ予算消費で成り立つ。したがって
**状態 (配置, 消去使用数 u) を (shape, u) に割った商は到達可能性を保存する**。
u はスカラータグであり、shape の正規化（子対のソート）とは独立。
危険は実装レベルにしかないので、__main__ は必ず landauer_bfs（検証済み・商なし）
との全点照合を先に走らせる。

## 遷移（treedp.QuotientTree.neighbors の消去つき拡張）

- 高さ 0（葉。子は free）: トグル常時可・コスト 0。**erase は発生しない**
- 高さ k の根: 子根が両方載っていればトグル（コスト 0）。
  根が載っていて子根が揃っていなければ **erase（コスト 1）**
- 部分木内の手はコストごと持ち上げる。同型な子対 (ci=cj) は片側だけ展開してよい
  （もう片側は商で同じ shape に落ちる。コストも同じ）

予算優越: 同じ shape へは小さい u で着くほど良い（残予算の継続集合が包含）。
visited は shape → 最小 u で持つ。

    .venv/bin/python scripts/treedp_erase.py            # 全点照合 → 決定計算 (m=6, p=9)
    .venv/bin/python scripts/treedp_erase.py --verify   # 照合のみ
"""

from __future__ import annotations

import sys
import time
from collections import deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from treedp import _SHIFT, QuotientTree  # noqa: E402


class QuotientTreeErase(QuotientTree):
    """QuotientTree に「消去つき近傍」を足したもの。"""

    def __init__(self, m: int) -> None:
        super().__init__(m)
        self._nbr_e: list[dict[int, tuple[tuple[int, int], ...]]] = [
            {} for _ in range(m + 1)
        ]

    def neighbors_erase(self, k: int, sid: int) -> tuple[tuple[int, int], ...]:
        """(次 shape, 消去コスト 0|1) の列。ピーク制約は課さない。"""
        if k == 0:
            return ((1 - sid, 0),)  # 子は free: トグル常時可逆
        cache = self._nbr_e[k]
        got = cache.get(sid)
        if got is not None:
            return got
        key = self._keys[k][sid]
        b = key & 1
        ci = (key >> 1) & ((1 << _SHIFT) - 1)
        cj = key >> (1 + _SHIFT)
        out: list[tuple[int, int]] = []
        both = self._rb[k - 1][ci] and self._rb[k - 1][cj]
        if both:
            out.append((self._mk(k, 1 - b, ci, cj), 0))  # 可逆トグル
        elif b:
            out.append((self._mk(k, 0, ci, cj), 1))  # 消去（子根不揃いで外す）
        for c2, cost in self.neighbors_erase(k - 1, ci):
            out.append((self._mk(k, b, c2, cj), cost))
        if cj != ci:
            for c2, cost in self.neighbors_erase(k - 1, cj):
                out.append((self._mk(k, b, ci, c2), cost))
        res = tuple(out)
        if k < self.m:
            cache[sid] = res
        return res


def reach_clean(
    qt: QuotientTreeErase, p: int, e: int, *, cap: int | None = None,
    progress: bool = False,
) -> bool:
    """空配置から clean（根のみ）へ、ピーク ≤ p・消去 ≤ e で到達できるか。

    返り値 False は**全探索完了**（queue 枯渇）を意味する。cap 超過は例外。
    """
    top = qt.m
    start = qt.empty_id()
    goal = qt.goal_id()
    best: dict[int, int] = {start: 0}  # shape -> 最小消去数
    queue: deque[tuple[int, int]] = deque([(start, 0)])
    fpc = qt.popcount
    t0 = time.time()
    n_pop = 0
    while queue:
        sid, u = queue.popleft()
        if best.get(sid, e + 1) < u:
            continue  # 支配された経路
        if sid == goal:
            return True
        n_pop += 1
        if progress and n_pop % 2_000_000 == 0:
            print(f"  … {n_pop/1e6:.0f}M pop, |visited|={len(best)/1e6:.1f}M, "
                  f"{time.time()-t0:.0f}s", flush=True)
        for nsid, cost in qt.neighbors_erase(top, sid):
            nu = u + cost
            if nu > e or fpc(top, nsid) > p:
                continue
            if best.get(nsid, e + 1) <= nu:
                continue
            best[nsid] = nu
            queue.append((nsid, nu))
        if cap is not None and len(best) > cap:
            raise RuntimeError(f"状態数が cap={cap} を超えた (m={qt.m}, p={p}, e={e})")
    return goal in best


# ---------------------------------------------------------------------------
# 検証: landauer_bfs（検証済み・商なし）との全点照合
# ---------------------------------------------------------------------------


def verify(max_m: int = 3, pmax: int = 8, emax: int = 3) -> int:
    from landauer import landauer_bfs
    from revpebble import complete_binary_tree

    n_ok = 0
    n_ng = 0
    for m in range(1, max_m + 1):
        g = complete_binary_tree(m + 1)  # 非 free 部分 = QuotientTree(m) = Bt(m+1)
        root = g.n - 1
        qt = QuotientTreeErase(m)
        for p in range(1, pmax + 1):
            for e in range(0, emax + 1):
                want = landauer_bfs(g, root, p, e) is not None
                got = reach_clean(qt, p, e)
                if want == got:
                    n_ok += 1
                else:
                    n_ng += 1
                    print(f"×: m={m} p={p} e={e}: landauer={want} quotient={got}")
    print(f"照合 {n_ok + n_ng} 点: 一致 {n_ok}・不一致 {n_ng}")
    return n_ng


if __name__ == "__main__":
    ng = verify()
    if ng:
        sys.exit("不一致あり。数値は使用禁止。ここで停止")
    if "--verify" in sys.argv:
        sys.exit(0)

    # e=0 の回帰: S̄min(2..6) = [3,5,6,7,8]（既知）と一致するか
    print("== e=0 回帰（S̄min との一致）")
    for m, smin_bar in ((1, 3), (2, 5), (3, 6), (4, 7), (5, 8)):
        qt = QuotientTreeErase(m)
        lo = reach_clean(qt, smin_bar - 1, 0)
        hi = reach_clean(qt, smin_bar, 0)
        ok = (not lo) and hi
        print(f"m={m}: p={smin_bar-1} 不可 / p={smin_bar} 可 → {'○' if ok else '**×**'}",
              flush=True)
        if not ok:
            sys.exit("e=0 回帰失敗。停止")

    # 決定計算: m=6 (Bt(7) = 我々の cbt(7)), p=9
    print("== 決定: reach_cbt(9, e) の e=0 / e=1（m=6, 127 頂点の商）")
    qt = QuotientTreeErase(6)
    for e in (0, 1):
        t0 = time.time()
        r = reach_clean(qt, 9, e, progress=True)
        dt = time.time() - t0
        print(f"m=6, p=9, e={e}: {'到達可能' if r else '到達不能（全探索完了）'} "
              f"({dt:.0f}s)", flush=True)
        if e == 0 and r:
            sys.exit("矛盾: e=0 で到達可能（S̄min(7)=10 と不整合）。実装を疑え")
        if e == 1:
            if r:
                print("→ reach_cbt(9, e=1) ≥ 7: **1 消去で 2 段のギャップのうち"
                      "少なくとも 1 段を買い戻せる**（7 か 8 かは Bt(8) の計算が別途必要）")
            else:
                print("→ reach_cbt(9, e=1) = 6: **1 消去では 1 段も買い戻せない**。"
                      "e=2 の検査が次の問い")
