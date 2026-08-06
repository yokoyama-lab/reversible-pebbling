"""$r$ の**全スケジュールにわたる最大値**を厳密に求める（P9）。

## 前周の記述の訂正

P8 で「(a) に穴がある」と書いたが、**主張自体に穴は無かった**。
`exp01b_engine.mstar` は状態空間を全探索した**真の**最小手数なので、
P1 が確かめた $M^*\\ge 4N-2\\min(p,N)-1$ は最初から
「すべての合法スケジュールについて」の主張である。

穴があるのは **(H) を経由する証明の道筋**のほうだった。
(H) と $r\\le p$ は正準な 1 本についてしか見ていないので、
**補題として使うなら全スケジュールで成り立つ必要がある**。ここを埋める。

## 何を計算するか

$$r_{\\max}(G,p) \\;=\\; \\max_{S} \\;\\#\\{v : S \\text{ で } v \\text{ がちょうど 1 回置かれる}\\}$$

（$S$ は合法な clean スケジュール全体を走る）。これが $\\le p$ なら、
**補題「$r\\le p$」が全スケジュールで成り立つ**ことになる。

## どう計算するか

状態を **(載っている集合, ちょうど 1 回置いた集合, 2 回以上置いた集合)** に拡張して
全探索する。頂点ごとの状態は「未・1 回・2 回以上」の 3 通りなので、
状態数は高々 $2^N\\cdot 3^N$。$N\\le8$ なら現実的（$N=8$ で 170 万）。

- `put v`: 先行点が可用・未載・ピーク $<p$。回数が 未→1 回→2 回以上 と上がる。
- `take v`: 先行点が可用・載っている。回数は変わらない。
- 終端: 載っているのが目標だけ。そこでの $|1 回組|$ の最大を取る。
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from exp02_dags import edges_to_dag, enumerate_nonisomorphic  # noqa: E402
from revpebble import Dag, restrict_to_ancestors  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CSV_PATH = ROOT / "data" / "families" / "max_once.csv"
FIELDS = ["source", "tag", "N", "p", "r_max", "ok"]

#: 状態数が $2^N 3^N$ なので、これ以上は現実的でない。
N_LIMIT = 8


def max_once(g: Dag, target: int, p: int) -> int | None:
    """全ての合法 clean スケジュールにわたる $r$ の最大値。到達不能なら `None`。"""
    verts = [v for v in range(g.n) if v not in g.free]
    idx = {v: i for i, v in enumerate(verts)}
    n = len(verts)
    free = g.free
    need = [
        sum(1 << idx[u] for u in g.preds[v] if u not in free) for v in verts
    ]
    goal = 1 << idx[target]

    start = (0, 0, 0)
    best: int | None = None
    seen = {start}
    stack = [start]
    while stack:
        peb, once, twice = stack.pop()
        if peb == goal:
            c = bin(once).count("1")
            best = c if best is None or c > best else best
        pc = bin(peb).count("1")
        for i in range(n):
            bit = 1 << i
            if peb & need[i] != need[i]:
                continue  # 先行点が載っていない
            if peb & bit:  # take
                nxt = (peb ^ bit, once, twice)
            else:  # put
                if pc >= p:
                    continue
                if twice & bit:
                    nxt = (peb | bit, once, twice)
                elif once & bit:
                    nxt = (peb | bit, once ^ bit, twice | bit)
                else:
                    nxt = (peb | bit, once | bit, twice)
            if nxt not in seen:
                seen.add(nxt)
                stack.append(nxt)
    return best


def rows_small_dags(nmax: int) -> list[dict]:
    out: list[dict] = []
    for n in range(1, nmax + 1):
        for i, edges in enumerate(enumerate_nonisomorphic(n)):
            g = edges_to_dag(edges, n, name=f"d{n}_{i}")
            for target in range(n):
                ga, t = restrict_to_ancestors(g, target)
                N = ga.n - len(ga.free)
                if N == 0 or N > N_LIMIT:
                    continue
                for p in range(1, N + 2):
                    r = max_once(ga, t, p)
                    if r is None:
                        continue
                    out.append({
                        "source": "dag", "tag": f"d{n}_{i}/t{target}",
                        "N": N, "p": p, "r_max": r, "ok": int(r <= min(p, N)),
                    })
    return out


def cmd_build(nmax: int) -> int:
    rows = rows_small_dags(nmax)
    bad = [r for r in rows if not r["ok"]]
    CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with CSV_PATH.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(rows)
    print(f"wrote {CSV_PATH}: {len(rows)} 行 / 反例 {len(bad)}")
    for b in bad[:5]:
        print(f"  反例 {b['tag']} N={b['N']} p={b['p']}: r_max={b['r_max']} > min(p,N)")
    tight = sum(1 for r in rows if r["r_max"] == min(int(r["p"]), int(r["N"])))
    print(f"  うち r_max = min(p,N) にタイト: {tight} 行")
    return 0


def cmd_verify() -> int:
    if not CSV_PATH.exists():
        print("OK  max_once.csv はまだ無い（P9 未実施）")
        return 0
    n = bad = 0
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        for r in csv.DictReader(fh):
            n += 1
            if r["ok"] != "1":
                bad += 1
                print(f"NG: {r['tag']} p={r['p']}: r_max={r['r_max']} > min(p,N)")
    if bad:
        return 1
    print(f"OK  全スケジュールでの r の最大値が min(p,N) 以下（{n} 行・反例なし）")
    return 0


if __name__ == "__main__":
    import argparse

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--build", action="store_true")
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--nmax", type=int, default=6)
    ns = ap.parse_args()
    if ns.build:
        raise SystemExit(cmd_build(ns.nmax))
    if ns.verify:
        raise SystemExit(cmd_verify())
    ap.print_help()
