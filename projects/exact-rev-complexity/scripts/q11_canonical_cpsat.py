"""Q11: 最適解の**正準形**を取る（2026-08-18、docs/42 §3.1）。

ピラミッド h・ピーク ≤ p（= p_min）・T=2h-1 の位置つきモデルに時間対称（Lean `sym_wlog` で WLOG）を
課し、CP-SAT で総在時間 Σ_t |P_t| を最小化する。SAT ソルバの返す最適解は恣意的で構造が読めないが、
この正準化で「上は alt・下は部分 run」の形が見える。解はペブリング規則で独立検査してから印字する。
h=13 で最適 767（69 秒）、h=14 で 926（896 秒）。h ≥ 15 は 1500 秒で最適に届かない（FEASIBLE。値は使わない）。

使い方: .venv/bin/python scripts/q11_canonical_cpsat.py 13 37 [制限秒]
"""
import sys, time
from ortools.sat.python import cp_model
sys.path.insert(0, '<local>/dev/github.com/tetsuo-jp/exact-rev-complexity/scripts')
import q2_cnf

def build(h, p, sym=True, minimize='presence', hint=None, extra=None):
    par, sink = q2_cnf.pyramid(h)
    n = len(par); T = 2*h-1
    dep = q2_cnf.depths(par)
    m = cp_model.CpModel()
    x = [[m.NewBoolVar(f"x{v}_{t}") for t in range(T+1)] for v in range(n)]
    for v in range(n):
        m.Add(x[v][0] == 0)
        m.Add(x[v][T] == (1 if v == sink else 0))
        lo = dep[v]+1; hi = T if v == sink else T-dep[v]-1
        for t in range(T+1):
            if t < lo or t > hi: m.Add(x[v][t] == 0)
        if v == sink:
            for t in range(lo, T+1): m.Add(x[v][t] == 1)
        else:
            for t in (lo, lo+1, hi-1, hi): m.Add(x[v][t] == 1)
    for t in range(T):
        for v in range(n):
            for q in par[v]:
                # x[v][t] != x[v][t+1] -> x[q][t] and x[q][t+1]
                m.AddBoolOr([x[v][t], x[v][t+1].Not(), x[q][t]])
                m.AddBoolOr([x[v][t].Not(), x[v][t+1], x[q][t]])
                m.AddBoolOr([x[v][t], x[v][t+1].Not(), x[q][t+1]])
                m.AddBoolOr([x[v][t].Not(), x[v][t+1], x[q][t+1]])
    for t in range(T+1):
        m.Add(sum(x[v][t] for v in range(n)) <= p)
    if sym:
        for v in range(n):
            if v == sink: continue
            for t in range(T+1):
                if t < T-t: m.Add(x[v][t] == x[v][T-t])
    if extra: extra(m, x, h, T)
    if minimize == 'presence':
        m.Minimize(sum(x[v][t] for v in range(n) for t in range(T+1)))
    return m, x, par, sink, T

def solve(h, p, limit=600, workers=8, **kw):
    m, x, par, sink, T = build(h, p, **kw)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = limit; s.parameters.num_workers = workers
    st = s.Solve(m)
    if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE): return None, s.StatusName(st)
    n = len(par)
    P = [{v for v in range(n) if s.Value(x[v][t])} for t in range(T+1)]
    for t in range(T):
        for v in P[t]^P[t+1]:
            for u in par[v]: assert u in P[t] and u in P[t+1]
    assert not P[0] and P[T]=={sink}
    return P, (s.StatusName(st), int(s.ObjectiveValue()))


def grid(h, P):
    """層ごとの在否格子と、時刻ごとの個数・層別個数を印字する。"""
    T = 2 * h - 1
    idx = {}
    k = 0
    for lvl in range(h):
        for i in range(h - lvl):
            idx[(lvl, i)] = k
            k += 1
    print(f"h={h} T={T} peak={max(len(s) for s in P)}")
    print("     t: " + "".join(str(t % 10) for t in range(T + 1)))
    for lvl in range(h):
        for i in range(h - lvl):
            v = idx[(lvl, i)]
            row = "".join('#' if v in P[t] else '.' for t in range(T + 1))
            print(f"L{lvl:2d}i{i:2d}: {row}")
        print()
    print("cnt: " + " ".join(f"{len(s):2d}" for s in P))
    for lvl in range(h):
        print(f"L{lvl:2d}: " + " ".join(f"{sum(1 for i in range(h - lvl) if idx[(lvl, i)] in P[t]):2d}"
                                       for t in range(T + 1)))


if __name__ == '__main__':
    h=int(sys.argv[1]); p=int(sys.argv[2]); lim=float(sys.argv[3]) if len(sys.argv)>3 else 600
    t0=time.time(); P, info = solve(h,p,limit=lim)
    print(info, f"{time.time()-t0:.1f}s")
    if P: grid(h,P)
