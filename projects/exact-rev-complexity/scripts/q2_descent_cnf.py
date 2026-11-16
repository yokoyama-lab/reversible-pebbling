#!/usr/bin/env python3
"""ピラミッドの時間最適並列可逆ペブリングを **片道の「降下問題」** に帰着した CNF（2026-08-18）。

## 帰着（時間対称性は WLOG）

時間最適 $T = 2h-1$ の合法なペブリング $P$ を 1 つ取ると、その **上り（$t \\ge h$）を
時間反転して sink を除いた列** $Q_j = P_{T-j} \\setminus \\{\\mathrm{sink}\\}$（$j = 0..h-1$）は
$\\emptyset$ から始まる合法な列であり、$|Q_j| \\le p - 1$（上りでは sink が常在するから）。
$Q$ を下りに使い、時刻 $h$ で sink を置き、$Q$ を逆順に上れば、ピーク $\\le p$ の
**時間対称な**ペブリングになる。したがって

$$ p_{\\min}(P_h) = 1 + d(h), \\qquad
   d(h) := \\min_{Q}\\ \\max_{1 \\le t \\le h-1} |Q_t| $$

ここで $Q$ は「降下」= 次を満たす列 $Q_0 = \\emptyset, Q_1, \\dots, Q_{h-1}$:
- 各ステップが並列可逆ペブリングの規則を満たす（変化した頂点の親は前後の両方に居る）
- 層 $k$（$k \\le h-3$）は $Q_{k+1}$ と $Q_{k+2}$ に**全部**居る、層 $h-2$ は $Q_{h-1}$ に全部居る
  （時間最適性から強制される。Lean `present_at_dep`）
- 終状態 $Q_{h-1}$ は自由（sink を置くのに要る層 $h-2$ 以外は何でもよい）

Lean での機械証明は `lean/Revgarbage/ParPebbleSym.lean`（`sym_wlog` / `descent_of_pebbling`
/ `pebbling_of_descent`）。⚠ この CNF で取った UNSAT 証明書は、その定理と
**この生成器の正しさ**に乗る（素の CNF の証明書はどちらにも乗らない）。層ラベルを付けるときは
その旨を書く。

## 変数と節

`x[v][t]`（$t = 0..h-1$）。層 $k$ の頂点は $t \\le k$ で不在（深さ下界。Lean `depth_bound_seg`）。
規則は `q2_cnf.build` と同じ 4 節。基数制約は Sinz の逐次カウンタ。

使い方:
  q2_descent_cnf.py --h 13 --d 36 --out /tmp/desc.cnf     # d(13) = 36 なら SAT、35 なら UNSAT
  q2_descent_cnf.py --selftest                              # h=2..12 で 1+d(h) = p_min を照合
"""
from __future__ import annotations

import argparse
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from q2_cnf import Cnf, pyramid, depths, run_cadical  # noqa: E402

# 実測の p_min（台帳 Q11、h=2..18。h≥3 は素の CNF の DRAT つき）
PMIN = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16, 8: 20, 9: 23, 10: 26, 11: 29,
        12: 32, 13: 37, 14: 41, 15: 45, 16: 49, 17: 54, 18: 58}


def build_descent(h: int, d: int) -> tuple[Cnf, list[list[int]]]:
    """降下問題の CNF。戻り値は (cnf, x) で x[v][t] は変数番号。"""
    par, sink = pyramid(h)
    n = len(par)
    dep = depths(par)
    S = h - 1                      # 降下の最終時刻
    c = Cnf()
    x = [[c.new() for _ in range(S + 1)] for _ in range(n)]
    for v in range(n):
        k = dep[v]
        for t in range(S + 1):
            if t <= k:
                c.add(-x[v][t])              # 深さ下界（t=0 の空集合を含む）
        if v == sink:
            continue
        # 強制: 層 k は時刻 k+1, k+2 に全部居る（k+2 ≤ S のとき）
        for t in (k + 1, k + 2):
            if t <= S:
                c.add(x[v][t])
    for t in range(S):
        for v in range(n):
            a, b = x[v][t], x[v][t + 1]
            for q in par[v]:
                for tgt in (x[q][t], x[q][t + 1]):
                    c.add(-a, b, tgt)
                    c.add(a, -b, tgt)
    for t in range(1, S + 1):
        c.atmost([x[v][t] for v in range(n)], d)
    return c, x


def decode(h: int, x, val: dict[int, bool]) -> list[set[int]]:
    S = h - 1
    n = len(x)
    return [{v for v in range(n) if val.get(x[v][t], False)} for t in range(S + 1)]


def verify_descent(h: int, Q: list[set[int]]) -> list[str]:
    """降下の独立検査。破れた条件を返す（空なら合格）。"""
    par, sink = pyramid(h)
    dep = depths(par)
    S = h - 1
    bad = []
    if Q[0]:
        bad.append("Q[0] が空でない")
    for t in range(S):
        for v in Q[t] ^ Q[t + 1]:
            for u in par[v]:
                if u not in Q[t] or u not in Q[t + 1]:
                    bad.append(f"t={t}: {v} が変化したのに親 {u} が両側に居ない")
    for v in range(len(par)):
        if v == sink:
            continue
        for t in (dep[v] + 1, dep[v] + 2):
            if t <= S and v not in Q[t]:
                bad.append(f"層 {dep[v]} の {v} が時刻 {t} に居ない")
    return bad


def solve(h: int, d: int, timeout: int = 36000):
    """SAT なら降下列 Q（独立検査済み）、UNSAT なら None。"""
    import subprocess
    c, x = build_descent(h, d)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        path = f.name
    c.dump(path)
    try:
        r = subprocess.run(["cadical", path], capture_output=True, text=True, timeout=timeout)
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
    Q = decode(h, x, val)
    bad = verify_descent(h, Q)
    if bad:
        raise RuntimeError("降下の独立検査に落ちた: " + "; ".join(bad[:5]))
    return Q


def selftest(hmax: int = 12) -> int:
    bad = 0
    for h in range(2, hmax + 1):
        p = PMIN[h]
        sat = solve(h, p - 1) is not None
        unsat = solve(h, p - 2) is None if p >= 3 else True
        ok = sat and unsat
        print(f"  h={h}: d={p-1} {'SAT' if sat else 'UNSAT'}, d={p-2} {'UNSAT' if unsat else 'SAT'}"
              f"  → 1+d(h)={'=' if ok else '≠'}p_min={p} {'○' if ok else '**✗**'}")
        bad += 0 if ok else 1
    print("校正 OK" if bad == 0 else f"**校正 NG: {bad} 件**")
    return bad


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--hmax", type=int, default=12)
    ap.add_argument("--h", type=int)
    ap.add_argument("--d", type=int)
    ap.add_argument("--out")
    a = ap.parse_args()
    if a.selftest:
        sys.exit(1 if selftest(a.hmax) else 0)
    if not (a.h and a.d is not None and a.out):
        ap.print_help()
        sys.exit(2)
    c, _ = build_descent(a.h, a.d)
    c.dump(a.out)
    print(f"{a.out}: {c.n} 変数 / {len(c.cls)} 節 （降下 h={a.h} d={a.d}）")


if __name__ == "__main__":
    main()
