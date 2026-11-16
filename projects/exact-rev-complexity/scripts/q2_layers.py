#!/usr/bin/env python3
"""**層状 DAG** で「ピークの下界」がどこまでタイトかを掃く（2026-08-14）。

層 `0..D` の大きさを `ns = [n_0, …, n_D]`（`n_D = 1`）とし、層 `l` の各頂点は
**層 `l-1` の全頂点**を親に持つ。この族は `ParPebbleWindow` の定理群の仮定を満たす
（親の深さがちょうど 1 小さい・sink 以外は深さ +1 の子を持つ・最深は sink のみ）。

機械証明した下界（`peak_lower_left` / `peak_lower_right`）は

    p >= max_k ( n_k + n_{k+1} )        （右端では k+2 <= D のとき +1）

**どの層構成でこれがタイトになるか**を SAT で確かめる。タイトな族が見つかれば、
そこは `p_min` が両側とも機械証明で決まる。
"""
import argparse
import itertools
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import q2_cnf  # noqa: E402


def build_layers(ns):
    """par, sink, dep を返す。層 l の頂点は層 l-1 の全頂点を親に持つ。"""
    assert ns[-1] == 1, "最深の層は 1 頂点でなければならない（sink の一意性）"
    idx, par, dep = [], [], []
    for l, n in enumerate(ns):
        cur = []
        for _ in range(n):
            cur.append(len(par))
            par.append(list(idx[l - 1]) if l else [])
            dep.append(l)
        idx.append(cur)
    return par, idx[-1][0], dep


def lower_bound(ns):
    """機械証明した下界（左端・右端の最大）。"""
    D = len(ns) - 1
    best = 0
    for k in range(D):
        v = ns[k] + ns[k + 1]                      # peak_lower_left（時刻 k+2）
        best = max(best, v)
        if k + 2 <= D:                             # peak_lower_right（sink も足せる）
            best = max(best, v + 1)
    return best


def solve(par, sink, dep, p, T):
    c = q2_cnf.build(par, sink, p, T, window=True)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        path = f.name
    c.dump(path)
    try:
        r = subprocess.run(["cadical", path, "-q"], capture_output=True,
                           text=True, timeout=1800)
        out = [ln for ln in r.stdout.splitlines() if ln.startswith("s ")]
        if not out:
            return None
        return "SATISFIABLE" in out[0] and "UNSAT" not in out[0]
    finally:
        os.unlink(path)


def pmin(ns, lo=None):
    par, sink, dep = build_layers(ns)
    D = len(ns) - 1
    T = 2 * D + 1
    lo = lo or lower_bound(ns)
    for p in range(lo, sum(ns) + 1):            # 下界から上へ（下界未満は不要）
        r = solve(par, sink, dep, p, T)
        if r is None:
            return None, "打ち切り"
        if r:
            return p, "確定"
    return None, "見つからず"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--maxD", type=int, default=4)
    ap.add_argument("--maxw", type=int, default=4)
    a = ap.parse_args()
    print(f"{'層の大きさ':>22} {'|V|':>4} {'下界(層1)':>9} {'p_min':>6} {'差':>4} {'判定':>6}")
    tight = same = 0
    for D in range(1, a.maxD + 1):
        for mid in itertools.product(range(1, a.maxw + 1), repeat=D):
            ns = list(mid) + [1]
            if len(ns) < 2 or ns[-2] == 1 and D > 1:
                pass
            lb = lower_bound(ns)
            v, st = pmin(ns, lb)
            if v is None:
                print(f"{str(ns):>22} {sum(ns):>4} {lb:>9} {'—':>6} {'':>4} {st:>6}")
                continue
            same += 1
            if v == lb:
                tight += 1
            print(f"{str(ns):>22} {sum(ns):>4} {lb:>9} {v:>6} {v - lb:>+4d} "
                  f"{'✔タイト' if v == lb else '':>6}")
    print(f"\n  {same} 例中 {tight} 例で下界がタイト")
    return 0


if __name__ == "__main__":
    sys.exit(main())
