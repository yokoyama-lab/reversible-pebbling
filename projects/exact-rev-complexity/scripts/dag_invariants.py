#!/usr/bin/env python3
"""DAG の構造不変量。**幅規則 `飽和 ⟺ p<=w` の `w` を一般 DAG へ広げるため。**

2026-08-11 に「飽和 ⟺ `p<=w`」（`w` は帯 DAG の幅）が `w=3..7`・`p<=7`・`e<=14` の
決着 13 行で外れ 0 だった（`data/e0_*.csv`、`docs/26_pebble_variants_ideas.md`）。
しかし **`w` は帯 DAG にしか定義されていない**。一般 DAG で飽和を予測する量は何かを
実測で決めるために、候補となる不変量をここで計算する。

**予想を立ててから測るのではなく、測ってから当てる**（今夜、順序を逆にして 4 回外した）。

計算するもの:

| 記号 | 意味 | 手段 |
|---|---|---|
| `maxlevel` | トポロジカル階層ごとの頂点数の最大 | 線形 |
| `antichain` | **最大反鎖の大きさ**（半順序の幅。Dilworth の幅） | CP-SAT で厳密 |
| `vrank` | **頂点ランキング数**（ordered coloring）。木では可逆ペブル数−1 と対応（Komarath–Sarma–Sawlani） | CP-SAT で厳密 |
| `strahler` | Strahler 数（木のみ） | 再帰 |
| `R` | **可逆ペブル数** = `e=0` で解ける最小 `p` | `reachable_dag` |
| `S` | **標準ペブル数** = `e` 十分大で解ける最小 `p` | `reachable_dag`（`e=emax`） |

`free` 頂点（常時可用）はペブルを消費しないので、**不変量は非 free 部分について計算する**。
"""
from __future__ import annotations

import sys
from functools import lru_cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp03_reach_dag import reachable_dag  # noqa: E402


def _nonfree(dag):
    """`free` を除いた頂点集合と、その上の先行関係。"""
    vs = [v for v in range(dag.n) if v not in dag.free]
    idx = {v: i for i, v in enumerate(vs)}
    preds = [frozenset(idx[u] for u in dag.preds[v] if u in idx) for v in vs]
    return vs, preds


def levels(preds):
    """トポロジカル階層（各頂点の最長先行鎖の長さ）。"""
    lv = [0] * len(preds)
    for i in range(len(preds)):
        lv[i] = 0 if not preds[i] else 1 + max(lv[u] for u in preds[i])
    return lv


def max_level_width(dag) -> int:
    _, preds = _nonfree(dag)
    if not preds:
        return 0
    lv = levels(preds)
    from collections import Counter
    return max(Counter(lv).values())


def _reach_closure(preds):
    """到達可能性（半順序）。`anc[i]` = i の真の先行点すべて。"""
    n = len(preds)
    anc = [set() for _ in range(n)]
    for i in range(n):
        for u in preds[i]:
            anc[i] |= {u} | anc[u]
    return anc


def max_antichain(dag) -> int:
    """最大反鎖の大きさ（半順序の幅）。**CP-SAT で厳密**。"""
    _, preds = _nonfree(dag)
    n = len(preds)
    if n == 0:
        return 0
    anc = _reach_closure(preds)
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    x = [m.NewBoolVar(f"x{i}") for i in range(n)]
    for i in range(n):
        for j in anc[i]:
            m.AddBoolOr([x[i].Not(), x[j].Not()])   # 比較可能な 2 点は同時に取れない
    m.Maximize(sum(x))
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = 120
    s.parameters.num_search_workers = 4
    r = s.Solve(m)
    if r not in (cp_model.OPTIMAL,):
        return -1                                   # **打ち切りは -1。値ではない**
    return int(s.ObjectiveValue())


def vertex_ranking(dag, ub: int = 16) -> int:
    """頂点ランキング数（ordered coloring）。無向化した上で厳密に。

    定義: 同じ色の 2 点を結ぶどの道にも、より大きい色の点がある。
    **CP-SAT で `k` を下から試す。** 打ち切りは -1。
    """
    _, preds = _nonfree(dag)
    n = len(preds)
    if n == 0:
        return 0
    adj = [set() for _ in range(n)]
    for i in range(n):
        for u in preds[i]:
            adj[i].add(u)
            adj[u].add(i)
    # 全点対の「色 c 以下だけを通る道」があるか、を素朴に判定する補助
    def ok(color) -> bool:
        for c in range(1, max(color) + 1):
            same = [i for i in range(n) if color[i] == c]
            if len(same) < 2:
                continue
            # c 未満の色の点だけを使って same の 2 点が繋がったら違反
            allowed = [i for i in range(n) if color[i] < c]
            seen = {}
            comp = 0
            for st in allowed:
                if st in seen:
                    continue
                comp += 1
                stack = [st]
                seen[st] = comp
                while stack:
                    v = stack.pop()
                    for w in adj[v]:
                        if color[w] < c and w not in seen:
                            seen[w] = comp
                            stack.append(w)
            for a in same:
                for b in same:
                    if a >= b:
                        continue
                    if any(seen.get(u) == seen.get(w) is not None
                           for u in adj[a] if color[u] < c
                           for w in adj[b] if color[w] < c):
                        return False
                    if b in adj[a]:
                        return False
        return True

    from ortools.sat.python import cp_model
    for k in range(1, ub + 1):
        m = cp_model.CpModel()
        col = [m.NewIntVar(1, k, f"c{i}") for i in range(n)]
        for i in range(n):
            for j in adj[i]:
                if i < j:
                    m.Add(col[i] != col[j])          # 必要条件（隣接は別色）
        s = cp_model.CpSolver()
        s.parameters.max_time_in_seconds = 60
        s.parameters.enumerate_all_solutions = True

        class Cb(cp_model.CpSolverSolutionCallback):
            def __init__(self):
                super().__init__()
                self.found = None
                self.tries = 0

            def on_solution_callback(self):
                self.tries += 1
                c = [self.Value(v) for v in col]
                if ok(c):
                    self.found = c
                    self.StopSearch()
                elif self.tries > 20000:
                    self.StopSearch()

        cb = Cb()
        s.Solve(m, cb)
        if cb.found is not None:
            return k
    return -1


def strahler(dag) -> int:
    """Strahler 数（木のみ意味を持つ）。合流があると -1。"""
    _, preds = _nonfree(dag)
    n = len(preds)
    if n == 0:
        return 0
    children = [[] for _ in range(n)]
    for i in range(n):
        for u in preds[i]:
            children[u].append(i)
    succ_cnt = [0] * n
    for i in range(n):
        for u in preds[i]:
            succ_cnt[u] += 1
    if any(len(preds[i]) > 1 for i in range(n)):
        return -1                                    # 合流あり = 木でない

    @lru_cache(maxsize=None)
    def s(v):
        cs = [s(c) for c in children[v]]
        if not cs:
            return 1
        mx = max(cs)
        return mx + 1 if cs.count(mx) >= 2 else mx
    roots = [i for i in range(n) if not preds[i]]
    return max(s(r) for r in roots) if roots else 0


def pebble_numbers(fam, k: int, pmax: int = 12, emax: int = 20,
                   **caps) -> tuple[int, int]:
    """`(R, S)` = (可逆ペブル数, 標準ペブル数)。届かなければ -1。

    `S` は `e=emax` での値。**`emax` で足りているかは呼ぶ側が確かめること**
    （`emax` を上げて変わらないことを見る）。
    """
    g = fam(k)
    t = g.n - 1
    R = S = -1
    for p in range(1, pmax + 1):
        if R < 0:
            r = reachable_dag(g, t, p, 0, **caps)
            if r is True:
                R = p
        if S < 0:
            r = reachable_dag(g, t, p, emax, **caps)
            if r is True:
                S = p
        if R > 0 and S > 0:
            break
    return R, S


if __name__ == "__main__":
    from revpebble import chain, complete_binary_tree, pyramid
    from exp03_reach_dag import FAMILIES
    print("=== 校正: 既知の値を再現するか ===")
    print("鎖 chain(8): 幅は 1 のはず")
    g = chain(8)
    print(f"  maxlevel={max_level_width(g)} antichain={max_antichain(g)} strahler={strahler(g)}")
    print("完全二分木 cbt(3): 反鎖は葉の数（非 free 部分）")
    g = complete_binary_tree(3)
    print(f"  maxlevel={max_level_width(g)} antichain={max_antichain(g)} strahler={strahler(g)}")
    print("ピラミッド pyramid(4)")
    g = pyramid(4)
    print(f"  maxlevel={max_level_width(g)} antichain={max_antichain(g)} strahler={strahler(g)}")
    for name in ("diamond3", "diamond5"):
        if name in FAMILIES:
            g = FAMILIES[name](6)
            print(f"{name}(6): maxlevel={max_level_width(g)} antichain={max_antichain(g)}"
                  f"  ← 幅 {name[-1]} と一致するはず")
