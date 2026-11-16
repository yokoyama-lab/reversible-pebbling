#!/usr/bin/env python3
r"""$M^*(T_h,P)$ の下界を「$t^*$ での駒数の結合制約」で締める。

## いまの下界がどこで緩いか

`treedp.lower_bound_mstar_phased` は

$$M^*(T_h,P)\;\ge\;2\bigl(g(P)+g(P-1)\bigr)+1$$

（$g(p)$ = 部分木で $\varnothing$ から「$a$ を含む何らかの配置」への最小手数、ピーク $\le p$）。
**部分木 $A$ と $B$ を独立に扱い、どちらにも全体の予算を許している。**
実際には、根が最後に置かれた時刻 $t^*$ において

$$x + y + 1 \;\le\; P \qquad (x=A の駒数,\; y=B の駒数,\; x,y\ge1)$$

が成り立つ。**この結合制約が使われていない。**

## 締め方

$g_p(x)$ を「ピーク $\le p$ で $\varnothing$ から *$a$ を含み駒数がちょうど $x$* の配置へ」の
最小手数とすると、$t^*$ で $A$ が $x$ 駒・$B$ が $y$ 駒なら

- $A$ の往路 $\ge g_P(x)$、復路 $\ge g_{P-1}(x)$（$t^*$ 以降は根が 1 本占める）
- $B$ も同様に $y$ で

$$M^*(T_h,P)\;\ge\;\min_{\substack{x,y\ge1\\ x+y\le P-1}}
   \bigl[g_P(x)+g_{P-1}(x)+g_P(y)+g_{P-1}(y)\bigr]+1 .$$

駒数を無視した版（$x$ を自由にした版）はこの min の下側なので、**必ず従来以上**になる。

## ⚠ 添字の流儀（`treedp.py` は 2 つ同居している）

- `realize_optimal(h, p)` の `h` は `revpebble.complete_binary_tree(h)` と同じ
- `QuotientTree(m)` / `first_root_pebbled_depth(m, p)` の `m` は **$T_{m+1}$** を指す
  （2026-09-04 に小さい木で校正して確定。`first_root_pebbled_depth(2,5)=9=g(T_3,5)`）

したがって $T_h$ の部分木を見るには `QuotientTree(h-2)` である。

実行: `python3 scripts/exp01b_lb_refine.py --calibrate`   （既知の M* を超えないか）
      `python3 scripts/exp01b_lb_refine.py --h 7 --peak 10`
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from treedp import QuotientTree  # noqa: E402

# 既知の厳密値（tests/test_exp01c_treedp.py::TRADEOFF に固定されているもの）
KNOWN_MSTAR = {(4, 6): 53, (5, 7): 155, (6, 8): 429, (6, 9): 339, (6, 10): 295}


def g_by_count(qt: QuotientTree, p: int, *, cap: int | None = None) -> dict[int, int]:
    """`{駒数 x: ピーク<=p で ∅ から「a を含み駒数 x」の配置への最小手数}`。

    1 回の BFS で全ての x をまとめて取る。**根に着いた配置も展開を続ける**
    （`first_root_pebbled_depth` は最初の 1 個で打ち切るが、こちらは全 x が要る）。
    """
    start = qt.empty_id()
    best: dict[int, int] = {}
    seen = {start}
    frontier = [start]
    d = 0
    if qt.root_pebbled(qt.m, start):
        best[qt.popcount(qt.m, start)] = 0
    while frontier:
        nxt = []
        for s in frontier:
            for t in qt.neighbors(qt.m, s):
                if t in seen:
                    continue
                pc = qt.popcount(qt.m, t)
                if pc > p:
                    continue
                seen.add(t)
                nxt.append(t)
                if qt.root_pebbled(qt.m, t) and pc not in best:
                    best[pc] = d + 1
        d += 1
        frontier = nxt
        if cap is not None and len(seen) > cap:
            raise RuntimeError(f"状態数が cap={cap} を超えた（m={qt.m}, p={p}）")
    return best


def refined_bound(h: int, P: int, *, cap: int | None = None,
                  verbose: bool = False) -> tuple[int | None, dict]:
    """(下界, 内訳)。到達できなければ (None, …)。"""
    qt = QuotientTree(h - 2)                     # ⚠ T_h の部分木 = T_{h-1} = QuotientTree(h-2)
    gP = g_by_count(qt, P, cap=cap)
    gQ = g_by_count(qt, P - 1, cap=cap)
    if verbose:
        print(f"  g_{P}(x) = {dict(sorted(gP.items()))}")
        print(f"  g_{P-1}(x) = {dict(sorted(gQ.items()))}")
    best = None
    arg = None
    for x in sorted(gP):
        for y in sorted(gP):
            if x < 1 or y < 1 or x + y > P - 1:
                continue
            if x not in gQ or y not in gQ:
                continue                          # 復路がピーク P-1 で届かない駒数は使えない
            v = gP[x] + gQ[x] + gP[y] + gQ[y] + 1
            if best is None or v < best:
                best, arg = v, (x, y)
    return best, {"gP": gP, "gQ": gQ, "arg": arg}


def old_bound(h: int, P: int, *, cap: int | None = None) -> int | None:
    """従来（駒数を無視した版）。比較用に同じ BFS から作る。"""
    qt = QuotientTree(h - 2)
    gP = g_by_count(qt, P, cap=cap)
    gQ = g_by_count(qt, P - 1, cap=cap)
    if not gP or not gQ:
        return None
    return 2 * (min(gP.values()) + min(gQ.values())) + 1


def calibrate(cap: int | None) -> int:
    """⚠ **下界が既知の $M^*$ を超えたら論法が誤り。** そこで止める。"""
    ok = True
    for (h, P), mstar in sorted(KNOWN_MSTAR.items()):
        t0 = time.time()
        try:
            new, info = refined_bound(h, P, cap=cap)
            old = old_bound(h, P, cap=cap)
        except RuntimeError as exc:
            print(f"  --   T_{h} p={P}: 打ち切り（{exc}）")
            continue
        if new is None or old is None:
            print(f"  --   T_{h} p={P}: 到達できず")
            continue
        sound = new <= mstar
        mono = new >= old
        mark = "ok  " if (sound and mono) else "NG  "
        if not (sound and mono):
            ok = False
        print(f"  {mark} T_{h} p={P}: 従来 {old} → 改良 {new}  "
              f"(既知 M*={mstar}, x,y={info['arg']}, {time.time()-t0:.1f}s)"
              + ("" if sound else "  ⚠ **既知の M* を超えた＝論法が誤り**")
              + ("" if mono else "  ⚠ 従来より弱い＝実装が誤り"))
    print("calibrate:", "全件成功" if ok else "**失敗あり。この下界を使ってはいけない**")
    return 0 if ok else 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int)
    ap.add_argument("--peak", type=int)
    ap.add_argument("--cap", type=int, default=25_000_000)
    ap.add_argument("--calibrate", action="store_true")
    a = ap.parse_args()
    if a.calibrate:
        return calibrate(a.cap)
    if not (a.h and a.peak):
        ap.error("--h と --peak が要る（または --calibrate）")
    t0 = time.time()
    new, info = refined_bound(a.h, a.peak, cap=a.cap, verbose=True)
    old = old_bound(a.h, a.peak, cap=a.cap)
    print(f"T_{a.h} p={a.peak}: 従来 {old} → 改良 {new}  "
          f"(x,y={info['arg']}, {time.time()-t0:.1f}s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
