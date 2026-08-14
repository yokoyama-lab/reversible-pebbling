#!/usr/bin/env python3
"""最適解は**何区間**必要か — 2 区間で足りるかを検定する（2026-08-15）。

## なぜ問うか

`alt` 構成の `altMem`（Lean で機械証明済み）は、偶数深さの頂点について
**2 つの区間の論理和**になっている。実測でも h=4..8 の最適解はどれも最大 2 区間だった。

これが一般に成り立つなら、時間最適な可逆ペブリングのピークは
**2-区間グラフ（multiple-interval graph）の最大クリーク**である。

| 構造 | 最大クリーク |
|---|---|
| 1-区間（区間グラフ） | 多項式時間 |
| **2-区間** | **NP 困難**（Butman, Hermelin, Lewenstein, Rawitz 2010） |

困難性の相転移がここにあるので、`h <= 12` が易しく `h >= 13` で崩れる説明になりうる。

## 検定の仕方

各頂点の**立ち上がり**（`¬x[v][t] ∧ x[v][t+1]`）の個数が区間数に等しい
（`x[v][0]` は常に偽なので）。これを `<= k` に制限して `p_min` が変わるかを見る。

* 制限しても `p_min` が同じ → **k 区間で最適解が実現できる**
* 制限すると `p_min` が上がる → **k 区間では足りない**（k+1 が要る証拠）

⚠ 打ち切りは結果にしない。UNSAT / SAT が確定した点だけ使う。
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import q2_cnf  # noqa: E402


def pyramid(h: int):
    """ピラミッド $P_h$ の (親リスト, sink)。"""
    par: list[list[int]] = []
    idx: list[list[int]] = []
    for k in range(h):
        cur = []
        for i in range(h - k):
            cur.append(len(par))
            par.append([] if k == 0 else [idx[k - 1][i], idx[k - 1][i + 1]])
        idx.append(cur)
    return par, idx[-1][0]


def add_atmost_intervals(c, x, n: int, T: int, k: int) -> None:
    """各頂点の在区間の個数を `k` 以下に制限する（逐次計数器による at-most-k）。"""
    for v in range(n):
        # r[t] ⟺ 時刻 t→t+1 で立ち上がる
        r = []
        for t in range(T):
            rv = c.new()
            c.add(-rv, -x[v][t])          # r → ¬x[t]
            c.add(-rv, x[v][t + 1])       # r → x[t+1]
            c.add(rv, x[v][t], -x[v][t + 1])  # (¬x[t] ∧ x[t+1]) → r
            r.append(rv)
        m = len(r)
        if m <= k:
            continue
        # s[i][j] = 「先頭 i 個のうち j 個以上が真」（j = 1..k+1）
        s = [[c.new() for _ in range(k + 1)] for _ in range(m)]
        for i in range(m):
            c.add(-r[i], s[i][0])                       # r_i → s[i][1 個以上]
            if i > 0:
                for j in range(k + 1):
                    c.add(-s[i - 1][j], s[i][j])        # 単調
                for j in range(1, k + 1):
                    c.add(-r[i], -s[i - 1][j - 1], s[i][j])
        c.add(-s[m - 1][k])                              # k+1 個以上は禁止


def solve(h: int, p: int, k: int | None, timeout: int) -> tuple[str, float]:
    par, sink = pyramid(h)
    T = 2 * (h - 1) + 1
    c = q2_cnf.build(par, sink, p, T, window=True)
    if k is not None:
        # build が作った x は 1..n*(T+1) の順に並んでいる
        n = len(par)
        x = [[v * (T + 1) + t + 1 for t in range(T + 1)] for v in range(n)]
        add_atmost_intervals(c, x, n, T, k)
    fn = tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False).name
    c.dump(fn)
    import time
    t0 = time.time()
    try:
        r = subprocess.run(["cadical", fn, "-q"], capture_output=True, text=True, timeout=timeout)
        out = [l for l in r.stdout.splitlines() if l.startswith("s ")]
        st = out[0] if out else "打ち切り"
    except subprocess.TimeoutExpired:
        st = "打ち切り"
    finally:
        os.unlink(fn)
    return st, time.time() - t0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--hmin", type=int, default=4)
    ap.add_argument("--hmax", type=int, default=10)
    ap.add_argument("--k", type=int, default=2, help="許す区間数の上限")
    ap.add_argument("--timeout", type=int, default=600)
    a = ap.parse_args()

    PMIN = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16, 8: 20, 9: 23, 10: 26,
            11: 29, 12: 32, 13: 37, 14: 41, 15: 45, 16: 49, 17: 54, 18: 58}
    print(f"  各頂点を {a.k} 区間以下に制限したとき、p_min は変わるか")
    print(f"  {'h':>3} {'p_min':>6} {'制限つき p_min':>12} {'判定':>8}")
    bad = 0
    for h in range(a.hmin, a.hmax + 1):
        p = PMIN.get(h)
        if p is None:
            continue
        # p で SAT なら「k 区間で足りる」。p で UNSAT なら足りない
        st, sec = solve(h, p, a.k, a.timeout)
        if st.startswith("s SATIS"):
            verdict, val = f"✔ {a.k} 区間で足りる", p
        elif st.startswith("s UNSAT"):
            # 足りない → いくつまで上がるかを 1 つずつ上げて見る
            val = None
            for q in range(p + 1, p + 6):
                st2, _ = solve(h, q, a.k, a.timeout)
                if st2.startswith("s SATIS"):
                    val = q
                    break
            verdict = f"⛔ 足りない（{val} まで上がる）" if val else "⛔ 足りない"
            bad += 1
        else:
            verdict, val = "打ち切り（結果にしない）", None
        print(f"  {h:>3} {p:>6} {str(val) if val else '—':>12}  {verdict}  [{sec:.0f}s]")
    print()
    print(f"  {a.k} 区間で足りなかった h: {bad} 件")
    return 0


if __name__ == "__main__":
    sys.exit(main())
