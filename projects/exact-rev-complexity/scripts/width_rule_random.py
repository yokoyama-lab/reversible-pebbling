#!/usr/bin/env python3
"""飽和を予測する不変量を、ランダム DAG 族で**測って決める**（2026-08-11）。

## 経緯: 最初の主張は反証された

    ✗ 飽和 ⟺ p <= 最大反鎖の大きさ   ← **ランダム DAG で反証（2026-08-11 11:30）**

帯 DAG（`diamond3..7`・`w=3..7`・`p<=7`・`e<=14`）では決着 13 行で外れ 0 だったが、
**ランダム族では `p <= antichain` なのに階段になる個体が出た**:

    ac=16 p=5: [3 3 3 3 3 3 8 8 8 8 10 10 11]  ← 伸び続ける
    ac= 9 p=5: [2 3 3 3 3 11 11 11 12 13 13 13 13]

**帯 DAG 限定の観察は生きているが、`antichain` による一般化は成り立たない。**

## したがって本スクリプトの目的を変える

**規則を検定するのではなく、「どの不変量が飽和/階段を分けるか」を大規模に測る。**
予想を先に立てない（今夜それで 5 回外した）。記録する量を増やし、
**後で「どれが効くか」を機械的に判定できる形**でデータを貯める。

根拠は帯 DAG（`diamond3..7`）・木・鎖の実測（`data/e0_*.csv`）で、
`antichain` が帯の幅 `w` をちょうど再現することを `dag_invariants.py` で校正済み。
**構造を持った族だけで当たっていても意味が薄い。ランダム DAG が最も反証しやすい。**

## 設計

1. ランダム DAG を生成（層状 DAG。層数・層幅・辺密度を振る）
2. 各 `p` について `e=0..emax` の `reach` を計算（**ここでは「解けるか」の単調列**）
3. **飽和したか階段かを判定**（末尾フラット長で。**emax の端で伸びていたら「未決着」**）
4. `antichain` を計算し、**`p <= antichain` の予測と突き合わせる**
5. **外れた個体を必ず残す**（反例が最も価値がある）

## 厳守

- **打ち切りを結果と読まない。** `state_cap`/`mem_cap` に当たった点は `unknown`
- **端で伸びている行は「未決着」**。飽和と呼ばない（本日 2 度これで誤判定した）
- 1 個体ごとに追記（途中で殺されても残る）
- 乱数種を固定して**決定的に**（リポジトリ規約）
"""
from __future__ import annotations

import argparse
import csv
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from dag_invariants import max_antichain, max_level_width  # noqa: E402
from exp03_reach_dag import UNKNOWN, reachable_dag  # noqa: E402
from revpebble import Dag  # noqa: E402

DENSITIES = [0.0, 0.2, 0.4, 0.6]


def random_family(rng: random.Random, width: int, density: float, kmax: int):
    """**ランダムな「族」**を返す。`F(k)` = 最初の k 層だけを取った DAG。

    ⚠ **単一 DAG の可解性（0/1）では規則の検定にならない。**
    規則は族についての主張（`reach` = 解ける最大サイズ）なので、
    **同じ構造規則で層を伸ばせるもの**が要る。ここでは層ごとの幅と先行点の選び方を
    最初に一度だけ決め（`plan`）、それを k 層ぶん切り出す。
    """
    plan = []                                   # 各層: [先行点の相対添字の集合, ...]
    for _ in range(kmax):
        w = rng.randint(1, width)
        layer = []
        for _ in range(w):
            layer.append((rng.random(), density))
        plan.append(layer)

    def F(k: int) -> Dag:
        k = max(1, min(k, kmax))
        prev = [0]
        preds: list[frozenset[int]] = [frozenset()]
        nxt = 1
        r2 = random.Random(hash((tuple(len(x) for x in plan), k)) & 0xFFFFFFFF)
        for li in range(k):
            cur = []
            for (seed_v, d) in plan[li]:
                m = 1 + sum(1 for _ in range(len(prev) - 1)
                            if ((seed_v * 1000 + r2.random()) % 1.0) < d)
                ps = frozenset(sorted(prev)[:min(m, len(prev))])
                preds.append(ps)
                cur.append(nxt)
                nxt += 1
            prev = cur
        if len(prev) > 1:
            preds.append(frozenset(prev))
            nxt += 1
        return Dag(n=nxt, preds=tuple(preds), free=frozenset({0}),
                   name=f"randfam(W={width},d={density})[{k}]")
    return F


CAPPED = object()      # **kmax に張り付いた。値ではなく下界にすぎない**


def reach_of_family(F, p: int, e: int, kmax: int, **caps):
    """`F` について `p` ペブル・`e` 消去で解ける最大の `k`。

    ⚠ **`kmax` まで全部解けてしまったら値ではない**（族の限界ではなく、
    こちらが試した上限に届いただけ）。その場合は `CAPPED` を返す。
    2026-08-11: これを入れずに書いて「飽和」と誤判定した。打ち切りを結果と読む型。
    """
    best = 0
    for k in range(1, kmax + 1):
        g = F(k)
        r = reachable_dag(g, g.n - 1, p, e, **caps)
        if r is UNKNOWN:
            return UNKNOWN
        if r:
            best = k
        else:
            return best                          # 単調性: 解けなくなったら以降も解けない
    return CAPPED


def classify(vals: list, emax: int) -> str:
    """`飽和` / `階段` / `未決着` / `一定`。**端で伸びていたら未決着。**"""
    if any(v is UNKNOWN for v in vals):
        return "未決着(打ち切り)"
    if any(v is CAPPED for v in vals):
        return "未決着(kmax に張り付き)"      # **上限到達は飽和ではない**
    if len(vals) < 8:
        return "未決着(点不足)"
    if vals[-1] == vals[0]:
        return "一定"
    if max(vals) > max(vals[: max(1, len(vals) - 4)]):
        return "階段"                       # 末尾 4 点以内で最大が更新 = まだ伸びている
    k = 1
    while k < len(vals) and vals[-1 - k] == vals[-1]:
        k += 1
    return "飽和" if k >= 6 else "未決着(フラット長不足)"


def reach_at(g: Dag, p: int, e: int, **caps):
    """この DAG の目標に到達できるか（True/False/UNKNOWN）。"""
    return reachable_dag(g, g.n - 1, p, e, **caps)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=200, help="生成する DAG の個数")
    ap.add_argument("--seed", type=int, default=20260811)
    ap.add_argument("--emax", type=int, default=14)
    ap.add_argument("--pmax", type=int, default=8)
    ap.add_argument("--kmax", type=int, default=14, help="族の最大サイズ")
    ap.add_argument("--dens", type=str, default="0.0,0.2,0.4,0.6",
                    help="辺密度の候補。**高いほど反鎖が小さくなる**（p>反鎖 の側を検定できる）")
    ap.add_argument("--width", type=int, default=4)
    ap.add_argument("--mem-cap", type=int, default=6_000_000_000)
    ap.add_argument("--state-cap", type=int, default=40_000_000)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    caps = dict(mem_cap=a.mem_cap, state_cap=a.state_cap)
    global DENSITIES
    DENSITIES = [float(x) for x in a.dens.split(',')]

    rng = random.Random(a.seed)
    a.out.parent.mkdir(parents=True, exist_ok=True)
    rows: list[dict] = []
    hits = miss = 0
    for i in range(a.n):
        W = rng.randint(2, a.width)
        d = rng.choice(DENSITIES)
        F = random_family(rng, W, d, a.kmax)
        big = F(a.kmax)                          # 反鎖は**十分大きい代表**で測る
        ac = max_antichain(big)
        ml = max_level_width(big)
        if ac < 0:
            continue
        for p in range(2, a.pmax + 1):
            t0 = time.perf_counter()
            vals = []
            for e in range(a.emax + 1):
                v = reach_of_family(F, p, e, a.kmax, **caps)
                vals.append(v)
                if v is UNKNOWN:
                    break
            cls = classify(vals, a.emax)
            pred = "飽和" if p <= ac else "階段"
            ok = ""
            if cls in ("飽和", "階段"):
                ok = "hit" if cls == pred else "**MISS**"
                hits += (ok == "hit")
                miss += (ok != "hit")
            rows.append({"i": i, "n": big.n, "width": W, "density": d,
                         "antichain": ac, "maxlevel": ml, "p": p,
                         "p_minus_ac": p - ac, "p_over_ac": round(p / ac, 3) if ac else -1,
                         "reach_e0": (vals[0] if vals and vals[0] not in (UNKNOWN, CAPPED) else -1),
                         "vals": " ".join("?" if v is UNKNOWN else ("CAP" if v is CAPPED else str(v)) for v in vals),
                         "class": cls, "pred": pred, "ok": ok,
                         "sec": round(time.perf_counter() - t0, 2)})
            with a.out.open("w", newline="") as f:
                wr = csv.DictWriter(f, fieldnames=list(rows[0]))
                wr.writeheader()
                wr.writerows(rows)
        if (i + 1) % 5 == 0:
            print(f"  {i+1}/{a.n}  的中 {hits} / **外れ {miss}**", flush=True)
    print(f"完了: 的中 {hits} / **外れ {miss}**", flush=True)


if __name__ == "__main__":
    main()
