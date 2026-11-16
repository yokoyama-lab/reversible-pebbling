#!/usr/bin/env python3
"""Q11: ピラミッドの時間最適並列可逆ペブリングの**構造探針**（2026-08-18、docs/42）。

すべて SAT（cadical）で全数判定する。UNSAT 側は証明書を取らない（構造の観察用。
値の主張には `q2_cnf.py`/`q2_descent_cnf.py` の DRAT を使う）。

サブコマンド:
  --sym HS        時間対称（x[v][t]=x[v][T-t]、sink 以外）を課しても p_min で SAT か
                  （Lean `sym_wlog` により常に SAT のはず。生成器の校正になる）
  --interval HS   さらに「各層・各時刻の在集合が区間」を課して p_min で SAT か（区間性の onset）
  --prefix HS     降下（`q2_descent_cnf`）でピーク d(h)-1 を保てる最大の時刻 t*（接頭辞決定性）
  --dT T1,T2,..  --hs H1,H2,..   接頭辞問題 d_T(h)（時刻 ≤ T・層 < T だけ）の表（1+d_T を印字）
  --single HS     単一区間モデル（往復禁止・kept＋遅延）の最適値（CP-SAT が要る）
  --cert h,T,d    接頭辞問題の CNF（層 < T・時刻 ≤ T・ピーク ≤ d）を data/q2_certs/ に書き、
                  cadical の DRAT を drat-trim で検証して data/q11_prefix_cert_log.csv に記録する。
                  UNSAT なら d_T(h) ≥ d+1、したがって p_min(h) ≥ d+2（Lean `pmin_iff_descent`
                  ＋ d_T ≤ d ＋ この生成器の正しさに乗る）
HS は "2,3,4" のようなカンマ区切り。
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import q2_cnf  # noqa: E402
from q2_cnf import Cnf, pyramid, depths  # noqa: E402
from q2_descent_cnf import PMIN  # noqa: E402


def _levels(h):
    idx = {}
    k = 0
    for lvl in range(h):
        for i in range(h - lvl):
            idx[(lvl, i)] = k
            k += 1
    return idx


def _cadical(c: Cnf, want_model: bool = False):
    fd, path = tempfile.mkstemp(suffix=".cnf")
    os.close(fd)
    c.dump(path)
    try:
        r = subprocess.run(["cadical"] + ([] if want_model else ["-q"]) + [path],
                           capture_output=True, text=True, timeout=36000)
    finally:
        os.unlink(path)
    sat = any(ln.startswith("s SATISFIABLE") for ln in r.stdout.splitlines())
    if not want_model:
        return sat, None
    val = {}
    for ln in r.stdout.splitlines():
        if ln.startswith("v "):
            for tok in ln[2:].split():
                lit = int(tok)
                if lit:
                    val[abs(lit)] = lit > 0
    return sat, val


def _full_cnf(h, p, sym=False, interval=False):
    par, sink = pyramid(h)
    T = 2 * h - 1
    c = q2_cnf.build(par, sink, p, T, window=True)
    X = lambda v, t: v * (T + 1) + t + 1  # noqa: E731  build() が最初に作る変数
    if sym:
        for v in range(len(par)):
            if v == sink:
                continue
            for t in range(T + 1):
                if t < T - t:
                    c.add(-X(v, t), X(v, T - t))
                    c.add(X(v, t), -X(v, T - t))
    if interval:
        idx = _levels(h)
        for lvl in range(h):
            n = h - lvl
            for t in range(T + 1):
                for i in range(n):
                    for l in range(i + 2, n):
                        for j in range(i + 1, l):
                            c.add(-X(idx[(lvl, i)], t), -X(idx[(lvl, l)], t), X(idx[(lvl, j)], t))
    return c, par, sink, T, X


def _verify_full(par, sink, P, T):
    assert not P[0] and P[T] == {sink}
    for t in range(T):
        for v in P[t] ^ P[t + 1]:
            for u in par[v]:
                assert u in P[t] and u in P[t + 1]


def probe_sym(hs, interval=False):
    for h in hs:
        p = PMIN[h]
        c, par, sink, T, X = _full_cnf(h, p, sym=True, interval=interval)
        t0 = time.time()
        sat, val = _cadical(c, want_model=True)
        if sat:
            P = [{v for v in range(len(par)) if val.get(X(v, t), False)} for t in range(T + 1)]
            _verify_full(par, sink, P, T)
        print(f"  h={h} p={p} 対称{'＋区間' if interval else ''}: "
              f"{'SAT（解を独立検査）' if sat else 'UNSAT'}  {time.time()-t0:.1f}s", flush=True)


def _prefix_cnf(h, d, tstar, T=None):
    """降下 CNF でピーク d を時刻 1..tstar だけに課す。T を与えると層 < T・時刻 ≤ T に切り詰める。"""
    par, sink = pyramid(h)
    dep = depths(par)
    S = h - 1 if T is None else T
    vs = [v for v in range(len(par)) if (T is None or dep[v] < T)]
    idx = {v: i for i, v in enumerate(vs)}
    c = Cnf()
    x = [[c.new() for _ in range(S + 1)] for _ in vs]
    for v in vs:
        i, k = idx[v], dep[v]
        for t in range(S + 1):
            if t <= k:
                c.add(-x[i][t])
        if v == sink:
            continue
        for t in (k + 1, k + 2):
            if t <= S:
                c.add(x[i][t])
    for t in range(S):
        for v in vs:
            i = idx[v]
            a, b = x[i][t], x[i][t + 1]
            for q in par[v]:
                j = idx[q]
                for tgt in (x[j][t], x[j][t + 1]):
                    c.add(-a, b, tgt)
                    c.add(a, -b, tgt)
    for t in range(1, min(tstar, S) + 1):
        c.atmost([x[i][t] for i in range(len(vs))], d)
    return c


def probe_prefix(hs):
    for h in hs:
        d = PMIN[h] - 2                     # d(h)-1: 全時刻では実行不能な上限
        S = h - 1
        lo, hi = 0, S
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if _cadical(_prefix_cnf(h, d, mid))[0]:
                lo = mid
            else:
                hi = mid
        assert _cadical(_prefix_cnf(h, PMIN[h] - 1, S))[0]
        print(f"  h={h} d={d}: 保てる最大 t*={lo}、t={hi} で破れる（h-1={S}）", flush=True)


def dT(h, T):
    lo, hi = 2 * h - 2, h * (h + 1) // 2      # lo は実行不能（t=2 で 2h-1 要る）、hi は実行可能
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if _cadical(_prefix_cnf(h, mid, T, T=T))[0]:
            hi = mid
        else:
            lo = mid
    return hi


def probe_dT(Ts, hs):
    print("  T\\h " + " ".join(f"{h:3d}" for h in hs))
    for T in Ts:
        row = []
        for h in hs:
            row.append("  -" if T > h - 1 else f"{1 + dT(h, T):3d}")
        print(f"  T={T:2d} " + " ".join(row), flush=True)


def probe_single(hs):
    from ortools.sat.python import cp_model
    for h in hs:
        par, sink = pyramid(h)
        dep = depths(par)
        n = len(par)
        S = h - 1
        m = cp_model.CpModel()
        kept = [m.NewBoolVar(f"k{v}") for v in range(n)]
        J = h
        w = [[m.NewBoolVar(f"w{v}_{j}") for j in range(J + 2)] for v in range(n)]  # [c(v) ≥ j]
        for v in range(n):
            m.Add(w[v][0] == 1)
            for j in range(J + 1):
                m.AddImplication(w[v][j + 1], w[v][j])
            m.Add(w[v][1] == 1).OnlyEnforceIf(kept[v].Not())
            m.Add(w[v][1] == 0).OnlyEnforceIf(kept[v])
            for u in par[v]:
                for j in range(J + 1):
                    # v, u とも非常駐で c(v) ≥ j なら c(u) ≥ j+1（親は子より長く居る）
                    m.AddBoolOr([kept[u], w[v][j].Not(), kept[v], w[u][j + 1]])
        y = [[None] * (S + 1) for _ in range(n)]
        for v in range(n):
            k = dep[v]
            for t in range(S + 1):
                if t < k + 1 or v == sink:
                    continue
                yy = m.NewBoolVar(f"y{v}_{t}")
                j = (t - k + 1) // 2           # t ≤ k + 2c(v) ⟺ c(v) ≥ ⌈(t-k)/2⌉
                m.AddBoolOr([kept[v], w[v][j], yy.Not()])
                m.AddImplication(kept[v], yy)
                m.AddImplication(w[v][j], yy)
                y[v][t] = yy
        d = m.NewIntVar(0, n, "d")
        for t in range(1, S + 1):
            m.Add(sum(y[v][t] for v in range(n) if y[v][t] is not None) <= d)
        m.Minimize(d)
        s = cp_model.CpSolver()
        s.parameters.max_time_in_seconds = 600
        s.parameters.num_workers = 8
        st = s.Solve(m)
        if st != cp_model.OPTIMAL:
            print(f"  h={h}: {s.StatusName(st)}（打ち切り。値は使わない）")
            continue
        val = 1 + int(s.ObjectiveValue())
        print(f"  h={h}: 単一区間 1+d = {val}  p_min = {PMIN.get(h, '?')}  差 {val - PMIN[h] if h in PMIN else '?'}",
              flush=True)


def cert(h, T, d):
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    cdir = os.path.join(root, "data", "q2_certs")
    os.makedirs(cdir, exist_ok=True)
    cnf = os.path.join(cdir, f"pyr_h{h}_T{T}_d{d}.cnf")
    _prefix_cnf(h, d, T, T=T).dump(cnf)
    drat = os.path.join(tempfile.gettempdir(), f"pyr_h{h}_T{T}_d{d}.drat")
    t0 = time.time()
    r = subprocess.run(["cadical", cnf, drat, "--binary=false", "-q"], capture_output=True, text=True)
    res = next((ln.strip() for ln in r.stdout.splitlines() if ln.startswith("s ")), "打ち切り")
    sec = int(time.time() - t0)
    size, ver, vsec = "-", "-", 0
    if res == "s UNSATISFIABLE":
        size = os.path.getsize(drat)
        t1 = time.time()
        r2 = subprocess.run(["drat-trim", cnf, drat], capture_output=True, text=True)
        ver = next((ln.strip() for ln in r2.stdout.splitlines() if ln.strip() in ("s VERIFIED", "s NOT VERIFIED")),
                   "検証打ち切り")
        vsec = int(time.time() - t1)
    if os.path.exists(drat):
        os.unlink(drat)
    log = os.path.join(root, "data", "q11_prefix_cert_log.csv")
    new = not os.path.exists(log)
    with open(log, "a") as f:
        if new:
            f.write("h,T,d,result,sec,drat_bytes,verify,vsec\n")
        f.write(f"{h},{T},{d},{res},{sec},{size},{ver},{vsec}\n")
    print(f"  h={h} T={T} d={d}: {res} ({sec}s) DRAT {size} {ver} ({vsec}s)")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sym")
    ap.add_argument("--interval")
    ap.add_argument("--prefix")
    ap.add_argument("--dT")
    ap.add_argument("--hs")
    ap.add_argument("--single")
    ap.add_argument("--cert")
    a = ap.parse_args()
    parse = lambda s: [int(x) for x in s.split(",")]  # noqa: E731
    if a.sym:
        probe_sym(parse(a.sym))
    if a.interval:
        probe_sym(parse(a.interval), interval=True)
    if a.prefix:
        probe_prefix(parse(a.prefix))
    if a.dT:
        probe_dT(parse(a.dT), parse(a.hs))
    if a.single:
        probe_single(parse(a.single))
    if a.cert:
        h, T, d = parse(a.cert)
        cert(h, T, d)


if __name__ == "__main__":
    main()
