#!/usr/bin/env python3
r"""Q13 の下界側の証人の**独立検証器**（2026-08-24）。

CNF も `q2_cnf.py` も `q13_nstar_witness.py` も import しない。
並列可逆ペブリングの**定義そのもの**から検査する:

1. $x[v][0]=0$（空から始める）
2. $x[\mathrm{sink}][T]=1$、他は $0$（clean 到達）
3. $x[v][t]\ne x[v][t+1]$ なら、$v$ の**すべての親** $q$ について
   $x[q][t]=x[q][t+1]=1$（親は変化の前後の両方に居る）
4. どの時刻でもペブル数 $\le p$
5. $T=2n-1$（鎖の時間最適）

これで $n^*(p)\ge n$ が証人だけで閉じる。上限側 $n^*(p)\le n$ は別（DRAT。
`data/q13_nstar_cert.csv`）。
"""
from __future__ import annotations
import argparse
import copy
import json
import sys
from pathlib import Path


def line_parents(n):
    """鎖: 頂点 i の親は i-1 のみ。sink は n-1。"""
    return [[] if i == 0 else [i - 1] for i in range(n)], n - 1


def check_schedule(sched, n, T, p):
    """定義を満たすかを見て、失敗の一覧を返す。"""
    par, sink = line_parents(n)
    e = []
    if T != 2 * n - 1:
        e.append(f"T={T} が時間最適 2n-1={2 * n - 1} でない")
    if len(sched) != T + 1:
        e.append(f"時刻の数が {len(sched)} で T+1={T + 1} でない")
        return e
    for t, row in enumerate(sched):
        if len(row) != n:
            e.append(f"t={t}: 頂点の数が {len(row)} で n={n} でない")
            return e
        if any(b not in (0, 1) for b in row):
            e.append(f"t={t}: 0/1 でない値がある")
            return e
    if any(sched[0]):
        e.append("t=0 が空でない")
    for v in range(n):
        want = 1 if v == sink else 0
        if sched[T][v] != want:
            e.append(f"t=T で頂点 {v} が {sched[T][v]}（clean 到達なら {want}）")
    for t in range(T):
        for v in range(n):
            if sched[t][v] != sched[t + 1][v]:
                for q in par[v]:
                    if not (sched[t][q] and sched[t + 1][q]):
                        e.append(f"t={t}→{t + 1} で頂点 {v} が変化したが親 {q} が"
                                 f"（{sched[t][q]},{sched[t + 1][q]}）＝両方には居ない")
    peak = max(sum(r) for r in sched)
    if peak > p:
        e.append(f"ピークが {peak} で p={p} を超えている")
    return e


def verify(doc, verbose=True):
    fails = []
    for p_str, w in sorted(doc["witness"].items(), key=lambda x: int(x[0])):
        p = int(p_str)
        n, T = w["n"], w["T"]
        if doc["nstar"].get(p_str) != n:
            fails.append(f"p={p}: 証人の n={n} が主張 n*({p})={doc['nstar'].get(p_str)} と違う")
        e = check_schedule(w["schedule"], n, T, p)
        peak = max(sum(r) for r in w["schedule"]) if w["schedule"] else -1
        if e:
            fails += [f"p={p}: {x}" for x in e]
        if verbose:
            print(f"  p={p}: n*({p}) >= {n} … {'OK' if not e else 'NG'}"
                  f"（T={T}、実測ピーク {peak}）")
    return fails


def self_test(doc):
    cases = []

    def mut(name, fn):
        d = copy.deepcopy(doc)
        fn(d)
        cases.append((name, d, True, d == doc))

    mut("t=0 にペブルを置く（p=6）",
        lambda d: d["witness"]["6"]["schedule"][0].__setitem__(0, 1))
    mut("終状態に余分なペブルを残す（p=7）",
        lambda d: d["witness"]["7"]["schedule"][-1].__setitem__(0, 1))
    mut("sink を終状態から外す（p=5）",
        lambda d: d["witness"]["5"]["schedule"][-1].__setitem__(
            d["witness"]["5"]["n"] - 1, 0))
    mut("親が居ないのに頂点を反転（p=4, t=1 の頂点 2）",
        lambda d: d["witness"]["4"]["schedule"][1].__setitem__(
            2, 1 - d["witness"]["4"]["schedule"][1][2]))
    def peak_over(d):
        """n も T も整合させたまま、ピーク 10 の証人を p=9 の欄に置く。
        n の照合では捕まらないので、ピークの検査だけが唯一の守りになる。"""
        d["witness"]["9"] = copy.deepcopy(d["witness"]["10"])
        d["nstar"]["9"] = d["witness"]["10"]["n"]

    mut("ピーク 10 の証人を p=9 の欄に置く（n も T も整合）", peak_over)
    mut("時刻を 1 つ削る（p=3）", lambda d: d["witness"]["3"]["schedule"].pop())
    mut("n を偽る（p=10 の n を 63 と主張）",
        lambda d: (d["witness"]["10"].__setitem__("n", 63),
                   d["nstar"].__setitem__("10", 63)))
    def pad_time(d):
        """最終行を 1 つ複製して T を 1 伸ばす。遷移も clean 到達も壊れないので、
        時間最適 T=2n-1 の検査だけが唯一の守りになる。"""
        w = d["witness"]["6"]
        w["schedule"].append(list(w["schedule"][-1]))
        w["T"] += 1

    mut("最終状態を 1 段複製して T を伸ばす（p=6）", pad_time)

    def nstar_only(d):
        """証人は無傷のまま、主張する n*(p) の値だけを 1 上げる。
        主張 n との照合だけが唯一の守りになる。"""
        d["nstar"]["6"] = d["witness"]["6"]["n"] + 1

    mut("主張する n*(6) だけを 1 上げる（証人は無傷）", nstar_only)

    cases.append(("対照: 無傷の証人", copy.deepcopy(doc), False, False))

    npos = nneg = okpos = okneg = ninert = 0
    for name, d, should_fail, inert in cases:
        if inert:
            print(f"  [不活性] {name}: 証人が変化していない（分母から外す）")
            ninert += 1
            continue
        fails = verify(d, verbose=False)
        got = bool(fails)
        if should_fail:
            npos += 1
            okpos += got
        else:
            nneg += 1
            okneg += not got
        print(f"  [{'OK' if got == should_fail else '**NG**'}] {name}: "
              f"{'検出' if got else '素通り'}" + (f" — {fails[0]}" if fails else ""))
    print(f"\n  陽性 {okpos}/{npos} 検出・陰性 {okneg}/{nneg} 通過・不活性 {ninert}")
    return 0 if (okpos == npos and okneg == nneg) else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cert", nargs="?", default="data/q13_nstar_witness.json")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    doc = json.loads(Path(a.cert).read_text(encoding="utf-8"))
    if a.self_test:
        print("=== 自己試験（証人への欠陥注入）===")
        return self_test(doc)
    print("=== Q13 の下界側（n*(p) >= n）の独立検証 ===")
    fails = verify(doc)
    if fails:
        print("\nVERIFY FAILED:")
        for f in fails[:10]:
            print("  - " + f)
        return 1
    print(f"\nVERIFY OK — p=2..10 の {len(doc['witness'])} 点すべてで下界が証人で閉じた")
    return 0


if __name__ == "__main__":
    sys.exit(main())
