#!/usr/bin/env python3
"""**最適解は何通りあるか** — 数え上げという別の方法論（2026-08-15）。

これまでは「最適値はいくつか」だけを問うてきた。ここでは
**最適値を達成する解の個数**を数える。これは新しい不変量であり、

* **多いほど対称性が高く、SAT にとって難しい**（UNSAT 証明が膨らむ理由）
* 台帳 Q9（ZDD で最適戦略の族を数え上げる）の前哨戦
* 「最適戦略はどれくらい一意か」という構造の問い

に直結する。

数え方: SAT で解を 1 つ得るたびに、その解を禁じる**阻止節**を足して繰り返す
（全解列挙）。⚠ 指数的に増えるので上限を設ける。**上限に当たったら「N 以上」と書く。**
"""
from __future__ import annotations
import argparse, os, subprocess, sys, tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import q2_cnf  # noqa: E402


def pyramid(h):
    par, idx = [], []
    for k in range(h):
        cur = []
        for i in range(h - k):
            cur.append(len(par))
            par.append([] if k == 0 else [idx[k-1][i], idx[k-1][i+1]])
        idx.append(cur)
    return par, idx[-1][0]


def count(h, p, limit=100000, timeout=600):
    par, sink = pyramid(h)
    T = 2 * (h - 1) + 1
    c = q2_cnf.build(par, sink, p, T, window=False)   # ⚠ 窓は解を減らすので使わない
    n = len(par)
    xs = [v * (T + 1) + t + 1 for v in range(n) for t in range(T + 1)]
    cls = list(c.cls)
    nv = c.n
    cnt = 0
    while cnt < limit:
        fn = tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False).name
        with open(fn, "w") as f:
            f.write(f"p cnf {nv} {len(cls)}\n")
            for cl in cls:
                f.write(" ".join(map(str, cl)) + " 0\n")
        try:
            r = subprocess.run(["cadical", fn, "-q", "--sat"], capture_output=True,
                               text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            os.unlink(fn); return cnt, "打ち切り"
        os.unlink(fn)
        if "s SATISFIABLE" not in r.stdout:
            return cnt, "全列挙"
        lits = {int(t) for l in r.stdout.splitlines() if l.startswith("v ")
                for t in l[2:].split() if t not in ("0",)}
        # 見つかった解の x 部分を禁じる
        block = [-v if v in lits else v for v in xs]
        cls.append(block)
        cnt += 1
    return cnt, "上限"


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--hmax", type=int, default=5)
    ap.add_argument("--limit", type=int, default=200000)
    a = ap.parse_args()
    PMIN = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13}
    print("  === 時間最適・ピーク最小のペブリングは何通りあるか ===")
    print(f"  {'h':>3} {'p_min':>6} {'解の個数':>12} {'状態':>8}")
    for h in range(2, a.hmax + 1):
        p = PMIN.get(h)
        if p is None: continue
        cnt, st = count(h, p, a.limit)
        print(f"  {h:>3} {p:>6} {cnt:>12,} {st:>8}", flush=True)
