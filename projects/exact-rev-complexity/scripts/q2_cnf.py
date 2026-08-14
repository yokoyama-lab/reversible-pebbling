#!/usr/bin/env python3
"""⚠ この符号化は **Meuli, Soeken, De Micheli, DATE 2019** §III と実質同一である
（変数 p_{v,i}、clean 到達、(p_{v,i} XOR p_{v,i+1}) -> 子が前後の両方に、各時刻の基数制約）。
**符号化自体を我々の寄与として主張してはならない。**詳細と逐語引用は
docs/34_survey_parallel_pebbling_novelty.md。
我々が足したのは --window（Lean で機械証明した時間窓制約）と、問いの立て方
（時間最適を固定して空間を問う）である。

並列可逆ペブリングの判定問題を **CNF** にする（台帳 Q2・下界の証明書化）。

**なぜ CNF か**: CP-SAT の `INFEASIBLE` は**証明書を出さない**ので層3 のまま。
CNF にして `cadical` の DRAT を `drat-trim` に通せば、**「そのような並列可逆ペブリングは
存在しない」を機械検証できる**（層2）。このリポジトリの規約:
「下界側＝存在しないことを示す側は、証明ログか定理証明器が要る」。

# 符号化（BHL Definition 1 と同一。arXiv 2110.04191v3 で確認済み）

変数 `x[v][t]` = 時刻 t に頂点 v にペブルがある。

1. `x[v][0] = 0`（空から始める）
2. `x[sink][T] = 1`, 他は 0（clean 到達。BHL の非 relaxed）
3. 各 (v,t) で `ch := x[v][t] XOR x[v][t+1]` とし、v の各親 q について
   **`ch → x[q][t]` かつ `ch → x[q][t+1]`**（親は前後の両方に居る）。
   補助変数を使わず 4 節で書ける。
4. 各 t で `sum_v x[v][t] <= p`（Sinz の逐次カウンタ）。

⚠ **空回り（何も変えないステップ）を禁止しない。**したがって UNSAT は
「長さ **T 以下**の合法なペブリングが存在しない」を意味する（padding できるため）。

使い方:
  q2_cnf.py --family line --n 8 --p 4 --T 15 --out /tmp/a.cnf
  q2_cnf.py --selftest        # 既知の SAT/UNSAT で符号化を校正する
"""
from __future__ import annotations

import argparse
import subprocess
import sys
import tempfile
import os


def line(n: int):
    par = [[] for _ in range(n)]
    for i in range(1, n):
        par[i] = [i - 1]
    return par, n - 1


def pyramid(h: int):
    idx = {}
    par: list[list[int]] = []
    for lvl in range(h):
        for k in range(h - lvl):
            idx[(lvl, k)] = len(par)
            par.append([])
    for lvl in range(1, h):
        for k in range(h - lvl):
            par[idx[(lvl, k)]] = [idx[(lvl - 1, k)], idx[(lvl - 1, k + 1)]]
    return par, idx[(h - 1, 0)]


def depths(par) -> list[int]:
    """各頂点の深さ（source からの最長路の辺数）。par は位相順に並んでいる前提。"""
    d = [0] * len(par)
    for v in range(len(par)):
        for u in par[v]:
            if d[u] + 1 > d[v]:
                d[v] = d[u] + 1
    return d


FAMILIES = {"line": line, "pyramid": pyramid}


class Cnf:
    def __init__(self):
        self.n = 0
        self.cls: list[list[int]] = []

    def new(self) -> int:
        self.n += 1
        return self.n

    def add(self, *lits: int):
        self.cls.append(list(lits))

    def atmost(self, lits: list[int], k: int):
        """Sinz (2005) の逐次カウンタ。lits の真の個数 <= k。"""
        n = len(lits)
        if k >= n:
            return
        if k == 0:
            for lit in lits:
                self.add(-lit)
            return
        s = [[self.new() for _ in range(k)] for _ in range(n)]
        self.add(-lits[0], s[0][0])
        for j in range(1, k):
            self.add(-s[0][j])
        for i in range(1, n):
            self.add(-lits[i], s[i][0])
            self.add(-s[i - 1][0], s[i][0])
            for j in range(1, k):
                self.add(-lits[i], -s[i - 1][j - 1], s[i][j])
                self.add(-s[i - 1][j], s[i][j])
            self.add(-lits[i], -s[i - 1][k - 1])

    def dump(self, path: str):
        with open(path, "w") as f:
            f.write(f"p cnf {self.n} {len(self.cls)}\n")
            for c in self.cls:
                f.write(" ".join(map(str, c)) + " 0\n")


def build(par, sink, p: int, T: int, fix_first: bool = False,
          depth_only: bool = False, window: bool = False,
          chain: bool = False) -> Cnf:
    n = len(par)
    c = Cnf()
    x = [[c.new() for _ in range(T + 1)] for _ in range(n)]
    for v in range(n):
        c.add(-x[v][0])                       # 空から
        c.add(x[v][T] if v == sink else -x[v][T])   # clean 到達
    # ---- 窓（すべて Lean で機械証明済み。SAT/UNSAT の両方に使ってよい） ----
    # lean/Revgarbage/ParPebbleWindow.lean:
    #   depth_bound_seg          : v ∈ P t → dep(v)+1 ≤ t          （任意 DAG）
    #   time_window_seg          : v ∈ P t → t ≤ T-dep(v)-1        （任意 DAG・sink 以外）
    #   no_slack                 : 窓の両端では必ず存在              （鎖）
    #   chain_sink_stays         : sink は置かれたら消えない         （鎖）
    # 含意節を足しているだけなので充足可能性は変わらない。
    lo = [0] * n
    hi = [T] * n
    forced: list[set[int]] = [set() for _ in range(T + 1)]
    if window:
        dep = depths(par)
        D = dep[sink]
        for v in range(n):
            lo[v] = min(dep[v] + 1, T)
            hi[v] = T if v == sink else max(T - dep[v] - 1, 0)
        for v in range(n):
            for t in range(T + 1):
                if t < lo[v] or t > hi[v]:
                    c.add(-x[v][t])
        # 両端強制は「sink 以外が深さ+1 の子を持つ」（hup）と T=2D+1 のときだけ正当。
        # 鎖もピラミッドも満たす。満たさない DAG では窓の制限だけを使う。
        has_child = [False] * n
        for v in range(n):
            for u in par[v]:
                if dep[u] + 1 == dep[v]:
                    has_child[u] = True
        hup = all(has_child[v] for v in range(n) if v != sink)
        if hup and T == 2 * D + 1:
            for v in range(n):
                if v == sink:
                    for t in range(lo[v], T + 1):
                        c.add(x[v][t])           # sink_at_and_stays_dep
                        forced[t].add(v)
                else:
                    for t in (lo[v], lo[v] + 1, hi[v] - 1, hi[v]):
                        if lo[v] <= t <= hi[v]:
                            c.add(x[v][t])       # present_at_dep / present_at_end_dep
                            forced[t].add(v)
    for t in range(T + 1):
        live = [v for v in range(n) if lo[v] <= t <= hi[v]]
        k = p - len(forced[t])
        if k < 0:
            c.add()                              # 空節 = UNSAT（ピークが足りない）
            continue
        c.atmost([x[v][t] for v in live if v not in forced[t]], k)
    if depth_only:
        # **証明済みの制約のみ**（Lean: ParPebble.depth_bound、公理ゼロ）:
        #   合法なペブリングでは v ∈ P t → v+1 ≤ t、すなわち t ≤ v なら x[v][t]=0。
        # 鎖では親が v-1 ただ一つなので深さ = 添字。**任意の合法ペブリングで成り立つので
        # SAT 側にも UNSAT 側にも使ってよい**（探索を速くするだけで解を落とさない）。
        for v in range(n):
            for t in range(min(v + 1, T + 1)):
                c.add(-x[v][t])
    if fix_first:
        # **補題 L1**: 時間最適（T=2n-1）なら頂点 i の初出はちょうど時刻 i+1。
        # ✅ 2026-08-14: L1 は present_at_window_start で機械証明された。
        #    UNSAT も根拠にしてよい。ただし**より強い --window を使うこと**。
        for v in range(n):
            for t in range(min(v + 1, T + 1)):
                c.add(-x[v][t])
            if v + 1 <= T:
                c.add(x[v][v + 1])
    for t in range(T):
        for v in range(n):
            a, b = x[v][t], x[v][t + 1]
            for q in par[v]:
                # (a XOR b) -> x[q][t] かつ x[q][t+1]
                for tgt in (x[q][t], x[q][t + 1]):
                    c.add(-a, b, tgt)
                    c.add(a, -b, tgt)
    return c


def run_cadical(cnf_path: str, drat_path: str | None = None, timeout: int = 3600):
    cmd = ["cadical", "--no-binary" if drat_path else "-q", cnf_path]
    if drat_path:
        cmd = ["cadical", cnf_path, drat_path, "--binary=false"]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    for ln in r.stdout.splitlines():
        if ln.startswith("s "):
            return ln.strip()
    return f"(s 行なし rc={r.returncode})"


def selftest() -> int:
    """**符号化の校正**。既知の SAT/UNSAT を再現しなければ数値を使わない。"""
    bad = 0
    cases = [
        # (族, n, p, T, 期待)  ※ n*(p) は (p-2)(p-3)+5
        ("line", 4, 3, 7, "SATISFIABLE"),    # n*(3) 圏内
        ("line", 7, 4, 13, "SATISFIABLE"),   # n*(4)=7
        ("line", 8, 4, 15, "UNSATISFIABLE"), # n*(4)+1
        ("line", 11, 5, 21, "SATISFIABLE"),  # n*(5)=11
        ("line", 12, 5, 23, "UNSATISFIABLE"),# n*(5)+1
        ("line", 5, 3, 9, "UNSATISFIABLE"),  # 実行可能性の限界(2^2=4)を超える
    ]
    for fam, n, p, T, want in cases:
        par, sk = FAMILIES[fam](n)
        c = build(par, sk, p, T)
        with tempfile.NamedTemporaryFile(suffix=".cnf", delete=False) as f:
            path = f.name
        c.dump(path)
        got = run_cadical(path)
        os.unlink(path)
        ok = want in got
        print(f"  {fam}(n={n}) p={p} T={T}: {got} （期待 s {want}） {'○' if ok else '**✗**'}")
        if not ok:
            bad += 1
    print("校正 OK" if bad == 0 else f"**校正 NG: {bad} 件。この符号化を使ってはいけない**")
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--family", choices=list(FAMILIES))
    ap.add_argument("--n", type=int)
    ap.add_argument("--p", type=int)
    ap.add_argument("--T", type=int)
    ap.add_argument("--out")
    ap.add_argument("--fix-first", action="store_true",
                    help="補題 L1 を制約として加える（**SAT 側の探索専用**。x[v][v+1]=1 は未証明）")
    ap.add_argument("--window", action="store_true",
                    help="機械証明済みの時間窓制約を足す（SAT/UNSAT 両方に使える）")
    ap.add_argument("--depth-only", action="store_true",
                    help="**証明済みの深さ下界のみ**を加える（Lean: depth_bound。SAT/UNSAT 両方に使える）")
    a = ap.parse_args()
    if a.selftest:
        sys.exit(1 if selftest() else 0)
    if not (a.family and a.n and a.p and a.out):
        ap.print_help()
        sys.exit(2)
    T = a.T if a.T else 2 * a.n - 1
    par, sk = FAMILIES[a.family](a.n)
    c = build(par, sk, a.p, T, a.fix_first, a.depth_only,
              window=a.window)
    c.dump(a.out)
    print(f"{a.out}: {c.n} 変数 / {len(c.cls)} 節 （{a.family} n={a.n} p={a.p} T={T}）")


if __name__ == "__main__":
    main()
