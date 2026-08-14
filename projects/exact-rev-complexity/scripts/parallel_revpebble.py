#!/usr/bin/env python3
"""並列可逆ペブリングの厳密値を CP-SAT で求める（2026-08-13 着手・台帳 Q2）。

⚠ **定義は再構成であって、Blocki–Holman–Lee (TCC 2022) の本文で確認していない。**
   2110.04191 の本文は未読（`docs/29_..._novelty.md` §8 の「未確認」に載っている）。
   **論文に数値を載せる前に、定義が一致するかを本文で確かめること。**
   ここで採る定義（標準的な並列可逆ペブリング）:

     配置 P_0 = ∅, P_1, …, P_T ⊆ V。各ステップで **同時に複数** 置ける／外せる。
     可逆性: v ∈ P_i △ P_{i+1}  ⟹  parents(v) ⊆ P_i ∩ P_{i+1}
     （置くときも外すときも、親が「前後の両方」に居ることを要求する。
       逐次版で「親が居るときだけ置ける／外せる」と言っているものの自然な並列化）

   目的: P_T ⊇ {sink}（到達）または clean（P_T = {sink}）。
   費用: **並列時間 T**（最小化）を、ピーク空間 ≤ p のもとで。

校正（**通らない限り数値を使わない**）:
  - 1 ステップに 1 手しか許さない設定（seq モード）で、逐次可逆ペブリングの既知値と一致すること
  - 並列は逐次以下の時間で済むこと（T_par ≤ T_seq）
  - 空間を増やすと時間は増えない（単調性）

使い方:
  parallel_revpebble.py --verify
  parallel_revpebble.py --family line --n 8 --p 4          # 1 点
  parallel_revpebble.py --sweep line --nmax 12 --out t.csv # 表を埋める
"""
from __future__ import annotations

import argparse
import csv
import os
import sys
import time

try:
    from ortools.sat.python import cp_model
except ImportError:
    print("ortools が要る（repo の .venv を使う）", file=sys.stderr)
    raise


# ---------- グラフ ----------

def line(n: int) -> tuple[list[list[int]], int]:
    """鎖 0 -> 1 -> ... -> n-1。sink は n-1。"""
    par = [[] for _ in range(n)]
    for i in range(1, n):
        par[i] = [i - 1]
    return par, n - 1


def pyramid(h: int) -> tuple[list[list[int]], int]:
    """高さ h のピラミッド。底が h 個、頂点が sink。"""
    idx = {}
    par: list[list[int]] = []
    for lvl in range(h):  # lvl=0 が底
        for k in range(h - lvl):
            idx[(lvl, k)] = len(par)
            par.append([])
    for lvl in range(1, h):
        for k in range(h - lvl):
            par[idx[(lvl, k)]] = [idx[(lvl - 1, k)], idx[(lvl - 1, k + 1)]]
    return par, idx[(h - 1, 0)]


FAMILIES = {"line": line, "pyramid": pyramid}


# ---------- 符号化 ----------

def solve(par, sink, p: int, T: int, clean: bool, seq: bool, workers: int = 8,
          max_sec: float = 60.0):
    """ピーク ≤ p・時間ちょうど T で到達できるか。返り値 True/False/None(未確定)。"""
    n = len(par)
    m = cp_model.CpModel()
    x = [[m.NewBoolVar(f"x{i}_{t}") for t in range(T + 1)] for i in range(n)]

    for i in range(n):
        m.Add(x[i][0] == 0)                       # 空から始める
    m.Add(x[sink][T] == 1)
    if clean:
        for i in range(n):
            if i != sink:
                m.Add(x[i][T] == 0)

    for t in range(T + 1):
        m.Add(sum(x[i][t] for i in range(n)) <= p)   # ピーク制約

    for t in range(T):
        changed = []
        for i in range(n):
            ch = m.NewBoolVar(f"c{i}_{t}")
            m.Add(x[i][t] != x[i][t + 1]).OnlyEnforceIf(ch)
            m.Add(x[i][t] == x[i][t + 1]).OnlyEnforceIf(ch.Not())
            changed.append(ch)
            # 可逆性: 動かすなら親は前後どちらにも居る
            for q in par[i]:
                m.AddImplication(ch, x[q][t])
                m.AddImplication(ch, x[q][t + 1])
        if seq:
            m.Add(sum(changed) <= 1)     # 逐次モード（校正用）
        else:
            m.Add(sum(changed) >= 1)     # 空回りを禁止（T を最小にするため）

    s = cp_model.CpSolver()
    s.parameters.num_search_workers = workers
    s.parameters.max_time_in_seconds = max_sec
    r = s.Solve(m)
    if r == cp_model.OPTIMAL or r == cp_model.FEASIBLE:
        return True
    if r == cp_model.INFEASIBLE:
        return False
    return None      # **打ち切り。到達不能ではない**


# **「打ち切り」と「範囲内で不可能」を同じ値で返さない**（番人を値と衝突させない）。
# 2026-08-13 に両方 None にして校正を誤って落とした。
INF = "範囲内で不可"      # T ≤ tmax のすべてで UNSAT（tmax の範囲での話）
CUT = "打ち切り"          # ソルバが時間切れ。**不可能ではない**


def min_time(par, sink, p: int, clean: bool, seq: bool, tmax: int = 200,
             max_sec: float = 60.0):
    """最小の T。到達不能なら INF、時間切れなら CUT を返す。"""
    for T in range(1, tmax + 1):
        r = solve(par, sink, p, T, clean, seq, max_sec=max_sec)
        if r is True:
            return T
        if r is None:
            return CUT
    return INF


# ---------- 校正 ----------

def verify() -> int:
    bad = 0

    def chk(label, got, want):
        nonlocal bad
        ok = got == want
        print(f"  {label} = {got} （期待 {want}） {'○' if ok else '**✗**'}")
        if not ok:
            bad += 1

    # (1) 鎖 n=2,3 は手で数えられる。clean 到達。
    #     n=2（0->1）: 0 を置く / 1 を置く / 0 を外す = 3 手（逐次）
    par, sk = line(2)
    chk("鎖 n=2 逐次 clean p=2", min_time(par, sk, 2, True, True), 3)
    # (2) 並列なら 2 手（「1 を置く」と「0 を外す」は同時にできない:
    #     0 を外すには 1 の親 0 が前後に必要。実際に測る）
    r_par = min_time(par, sk, 2, True, False)
    print(f"  鎖 n=2 並列 clean p=2 = {r_par}")
    if r_par is None or r_par > 3:
        print("  **✗ 並列が逐次より遅い/未確定はおかしい**")
        bad += 1
    # (3) 並列 ≤ 逐次（単調性）を鎖 n=3,4 で確認
    for n in (3, 4):
        par, sk = line(n)
        for p in (n, n + 1):
            a = min_time(par, sk, p, True, True)
            b = min_time(par, sk, p, True, False)
            ok = a is not None and b is not None and b <= a
            print(f"  鎖 n={n} p={p}: 逐次 {a} / 並列 {b} {'○' if ok else '**✗**'}")
            if not ok:
                bad += 1
    # (4) **既知値**: p 個のペブルで可逆に扱える鎖の長さは 2^(p-1)。
    #     → 鎖 n=5 は p=3 で不可能・p=4 で可能。ここが符号化の当たり判定になる。
    par, sk = line(5)
    chk("鎖 n=5 p=3（既知: 不可能）", min_time(par, sk, 3, True, False), INF)
    r4 = min_time(par, sk, 4, True, False)
    ok4 = isinstance(r4, int)
    print(f"  鎖 n=5 p=4（既知: 可能）= {r4} {'○' if ok4 else '**✗**'}")
    if not ok4:
        bad += 1
    # (5) 空間を増やして時間が増えないこと（可能な範囲だけで見る）
    ts = [min_time(par, sk, p, True, False) for p in (4, 5, 6)]
    ok = all(isinstance(a, int) for a in ts) and all(ts[i] >= ts[i + 1] for i in range(len(ts) - 1))
    print(f"  鎖 n=5 の p=4..6 の時間 {ts} が単調非増加 {'○' if ok else '**✗**'}")
    if not ok:
        bad += 1
    # (6) 鎖では並列化の余地が無いはず（親が前後に必要なので同時に動かせない）。
    #     **これは予測。外れたら定義の理解が違う**ので印を付けて出す。
    par3, sk3 = line(4)
    a, b = min_time(par3, sk3, 4, True, True), min_time(par3, sk3, 4, True, False)
    print(f"  鎖 n=4: 逐次 {a} / 並列 {b} — 鎖では一致するはず（{'一致' if a == b else '**不一致: 定義を見直す**'}）")

    # (7) **文献値との照合**（2026-08-13 追加）。実装が既知の2つの上限を
    #     「clean の有無」だけで再現することを固定する。
    #       clean（終状態が sink のみ）  : 鎖の上限 2^(p-1)   … 原稿の F(n,p)
    #       relaxed（sink に触ればよい） : 鎖の上限 2^p - 1  … Kral'ovic(2004) Thm 3.1
    for p_, nmax_clean, nmax_relaxed in ((3, 4, 7),):
        for n_, want in ((nmax_clean, True), (nmax_clean + 1, False)):
            par, sk = line(n_)
            got = isinstance(min_time(par, sk, p_, True, False, tmax=60, max_sec=60), int)
            ok = got == want
            print(f"  [文献] 鎖 n={n_} p={p_} clean: {got}（2^(p-1)={nmax_clean} より "
                  f"{'可' if want else '不可'}）{'○' if ok else '**✗**'}")
            if not ok:
                bad += 1
        for n_, want in ((nmax_relaxed, True), (nmax_relaxed + 1, False)):
            par, sk = line(n_)
            got = solve(par, sk, p_, 60, False, True, max_sec=120)
            ok = (got is True) == want
            print(f"  [文献] 鎖 n={n_} p={p_} relaxed: {got}（2^p-1={nmax_relaxed} より "
                  f"{'可' if want else '不可'}。Kral'ovic 2004 Thm 3.1）{'○' if ok else '**✗**'}")
            if not ok:
                bad += 1

    print("校正 OK" if bad == 0 else f"**校正 NG: {bad} 件。数値を使ってはいけない**")
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--family", choices=list(FAMILIES))
    ap.add_argument("--n", type=int)
    ap.add_argument("--p", type=int)
    ap.add_argument("--sweep", choices=list(FAMILIES))
    ap.add_argument("--nmax", type=int, default=12)
    ap.add_argument("--out")
    ap.add_argument("--max-sec", type=float, default=60.0)
    ap.add_argument("--clean", action="store_true", default=True)
    a = ap.parse_args()

    if a.verify:
        sys.exit(1 if verify() else 0)

    if a.sweep:
        f = FAMILIES[a.sweep]
        # **途中から再開できるようにする**（2026-08-13）。
        # 既に書かれている (family,n,p) は飛ばす。掃引は1点ごとに追記＋flush してあるので、
        # 打ち切られても済んだ点は残っている。
        done = set()
        if a.out and os.path.exists(a.out):
            with open(a.out, newline="") as fr:
                for row in csv.DictReader(fr):
                    if row.get("seq_T") and row.get("par_T"):
                        done.add((row["family"], row["n"], row["p"]))
            print(f"# 再開: 済み {len(done)} 点を飛ばす", file=sys.stderr)
            fh = open(a.out, "a", newline="")
            w = csv.writer(fh)
        else:
            fh = open(a.out, "w", newline="") if a.out else sys.stdout
            w = csv.writer(fh)
            w.writerow(["family", "n", "p", "seq_T", "par_T", "sec"])
            fh.flush()
        for n in range(2, a.nmax + 1):
            par, sk = f(n)
            for p in range(2, len(par) + 2):
                if (a.sweep, str(n), str(p)) in done:
                    continue
                t0 = time.time()
                s_ = min_time(par, sk, p, a.clean, True, max_sec=a.max_sec)
                p_ = min_time(par, sk, p, a.clean, False, max_sec=a.max_sec)
                w.writerow([a.sweep, n, p, s_, p_, round(time.time() - t0, 1)])
                fh.flush()   # **1 点ごとに flush**（打ち切られても残る）
        return

    if a.family and a.n and a.p:
        par, sk = FAMILIES[a.family](a.n)
        print(f"{a.family}(n={a.n}) p={a.p}: 逐次 {min_time(par, sk, a.p, True, True)} "
              f"/ 並列 {min_time(par, sk, a.p, True, False)}")
        return
    ap.print_help()


if __name__ == "__main__":
    main()
