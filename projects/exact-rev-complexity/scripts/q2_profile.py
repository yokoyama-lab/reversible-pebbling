#!/usr/bin/env python3
"""時間最適ペブリングの**最適解の形**を見る（2026-08-14）。

`layered` 構成はピーク $|V|$ を使うが、実測の $p_{\\min}$ はピラミッド h=17 で
$|V|$ の 0.36 倍しかない。**より良い構成の手がかりを得るため**、SAT の解を取り出して

* 各時刻の在ペブル数 $|P_t|$（プロファイル）
* 深さごとの在時間（窓のどこを使っているか）

を出す。⚠ 出した解は**必ずペブリング規則で独立検査**する（`verify`）。
検査に落ちた解は使わない。

使い方:
  q2_profile.py --family pyramid --n 8 --p 20
  q2_profile.py --family line --n 12 --p 6 --grid
"""
import argparse
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import q2_cnf  # noqa: E402


def solve_model(par, sink, p, T, window=True):
    """SAT を解いて `P[t] = set(頂点)` を返す。UNSAT なら None。"""
    c = q2_cnf.build(par, sink, p, T, window=window)
    n = len(par)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        path = f.name
    c.dump(path)
    try:
        r = subprocess.run(["cadical", path], capture_output=True, text=True,
                           timeout=36000)
    finally:
        os.unlink(path)
    if not any(ln.startswith("s SATISFIABLE") for ln in r.stdout.splitlines()):
        return None
    val = {}
    for ln in r.stdout.splitlines():
        if ln.startswith("v "):
            for tok in ln[2:].split():
                lit = int(tok)
                if lit:
                    val[abs(lit)] = lit > 0
    # x[v][t] は build() が最初に作るので番号は v*(T+1)+t+1
    return [{v for v in range(n) if val.get(v * (T + 1) + t + 1, False)}
            for t in range(T + 1)]


def verify(par, sink, P, T):
    """ペブリング規則の独立検査。破れた条件の一覧を返す（空なら合格）。"""
    bad = []
    if P[0]:
        bad.append("P[0] が空でない")
    if P[T] != {sink}:
        bad.append(f"P[T] = {sorted(P[T])} が {{sink}} でない")
    for t in range(T):
        changed = P[t] ^ P[t + 1]
        for v in changed:
            for u in par[v]:
                if u not in P[t] or u not in P[t + 1]:
                    bad.append(f"t={t}: {v} が変化したのに親 {u} が両側に居ない")
    return bad


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", choices=list(q2_cnf.FAMILIES), required=True)
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--grid", action="store_true", help="配置を格子で描く")
    a = ap.parse_args()

    par, sink = q2_cnf.FAMILIES[a.family](a.n)
    dep = q2_cnf.depths(par)
    D = dep[sink]
    T = 2 * D + 1
    nV = len(par)
    P = solve_model(par, sink, a.p, T)
    if P is None:
        print(f"UNSAT: {a.family} n={a.n} p={a.p} T={T}")
        return 1
    bad = verify(par, sink, P, T)
    if bad:
        print("✖ 独立検査に落ちた。この解は使ってはならない:")
        for b in bad[:10]:
            print("   ", b)
        return 1

    print(f"{a.family} n={a.n}  |V|={nV}  depth={D}  T={T}  p={a.p}"
          f"  （ピーク実測 {max(len(s) for s in P)}）")
    print(f"独立検査: 合格（{T} ステップすべてでペブリング規則を確認）")
    print(f"\n{'t':>4} {'|P_t|':>6} {'|V|比':>6}  深さ分布")
    for t, s in enumerate(P):
        byd: dict[int, int] = {}
        for v in s:
            byd[dep[v]] = byd.get(dep[v], 0) + 1
        dist = " ".join(f"{k}:{byd[k]}" for k in sorted(byd))
        print(f"{t:>4} {len(s):>6} {len(s) / nV:>6.2f}  {dist}")

    # 深さごとの「在時間」— 窓のどれだけを実際に使っているか
    print(f"\n{'深さ':>4} {'頂点数':>6} {'窓幅':>6} {'平均在時間':>10} {'使用率':>7}")
    for k in range(D + 1):
        vs = [v for v in range(nV) if dep[v] == k]
        if not vs:
            continue
        width = (T - k - 1) - (k + 1) + 1 if k < D else T - k
        occ = sum(sum(1 for t in range(T + 1) if v in P[t]) for v in vs) / len(vs)
        print(f"{k:>4} {len(vs):>6} {width:>6} {occ:>10.1f} {occ / width:>7.2f}")

    if a.grid:
        print("\n配置（行=頂点・列=時刻。深さ順に並べる）")
        order = sorted(range(nV), key=lambda v: (dep[v], v))
        for v in order:
            row = "".join("#" if v in P[t] else "." for t in range(T + 1))
            print(f"  v{v:<4} d{dep[v]:<3} {row}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
