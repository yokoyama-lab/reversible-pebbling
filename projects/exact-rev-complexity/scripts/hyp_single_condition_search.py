#!/usr/bin/env python3
r"""「graded と sink-directed の片方だけを破る反例」を全数で探す（2026-10-11, X-exact-rev-complexity-03）。

原稿 paper-ieice-q2/q2paper.tex（rem:hyp）は「graded かつ sink-directed」を外すと
no-slack（thm:noslack）と peak 下界（thm:peak）が崩れることを 2 つの DAG で示すが、
どちらの DAG も 2 条件を**同時に**破る。片方ずつ破る反例は無いかを機械で調べる。

## 測るもの（単一シンクの DAG を頂点数 n ごとに全列挙）

頂点 0..n-1 を位相順に番号付けし、シンク s = n-1、他の頂点はすべて子を持つ
（＝シンクは s ただ 1 つ）。すべての単一シンク DAG はこの形の少なくとも 1 つと同型。
各 DAG で（原稿の定義どおり。dpt = 最長路の辺数、D = dpt(s)）:

  * 4 象限の数: graded / sink-directed の真偽
  * sink-directed なすべての DAG（graded か否かを問わず）で、長さ T=2D+1 の
    **すべての**クリーンなペブリングについて
      (NS1) v ∈ P_{dpt(v)+1} ∩ P_{dpt(v)+2}         （全 v）
      (NS2) v ∈ P_{2D-dpt(v)-1} ∩ P_{2D-dpt(v)}       （v ≠ s）
      (NS3) s ∈ P_t（t ≥ D+1）
    が成り立つか。さらに Tpar = 2D+1 か（thm:time）
  * D ≥ 2 のとき pmin（長さ Tpar の最小ピーク）と下界 max_k(n_k+n_{k+1})・n_0+n_1+1
    （thm:peak）
  * 交互スケジュール（def:alt）が合法なペブリングか（thm:alt。原稿は graded を使うと言う）

判定は「全ペブリングを数える」のでなく、前向き到達集合 F_t と後ろ向き到達集合 B_u の
交わりで行う（長さ T のクリーンなペブリングの時刻 t の配置の全体は F_t ∩ B_{T-t}）。
1 歩は空でもよい（P=Q は合法）ので「ちょうど t 歩」と「t 歩以内」は同じ。

合法性（def:game）: v ∈ P△Q ⇒ pa(v) ⊆ P∩Q。

使い方:
    python3 scripts/hyp_single_condition_search.py --selftest
    python3 scripts/hyp_single_condition_search.py --n 7 --jobs 20 --out data/hyp_search_n7.json
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from multiprocessing import Pool

import numpy as np


# ───────────────────────────────────────────── グラフの性質（原稿の定義どおり）
def depths(n, pa):
    dep = [0] * n
    for v in range(n):
        for u in pa[v]:
            dep[v] = max(dep[v], dep[u] + 1)
    return dep


def children(n, pa):
    ch = [[] for _ in range(n)]
    for v in range(n):
        for u in pa[v]:
            ch[u].append(v)
    return ch


def is_graded(n, pa, dep):
    edges_ok = all(dep[u] + 1 == dep[v] for v in range(n) for u in pa[v])
    has_parent = all(pa[v] for v in range(n) if dep[v] > 0)
    return edges_ok and has_parent


def is_sink_directed(n, pa, dep, s):
    D = dep[s]
    if any(dep[v] == D for v in range(n) if v != s):
        return False
    ch = children(n, pa)
    return all(any(dep[c] == dep[v] + 1 for c in ch[v]) for v in range(n) if v != s)


# ───────────────────────────────────────────── ペブリングの到達集合
class Game:
    def __init__(self, n, pa):
        self.n = n
        N = 1 << n
        pam = [sum(1 << u for u in pa[v]) for v in range(n)]
        need = np.zeros(N, dtype=np.int64)
        for M in range(1, N):
            low = (M & -M).bit_length() - 1
            need[M] = need[M & (M - 1)] | pam[low]
        S = np.arange(N, dtype=np.int64)
        X = S[:, None] ^ S[None, :]
        A = S[:, None] & S[None, :]
        self.legal = (need[X] & ~A) == 0                      # legal[P, Q]
        self.pop = np.array([bin(i).count("1") for i in range(N)])
        self.N = N

    def forward(self, T, mask=None):
        L = self.legal if mask is None else (self.legal & mask[:, None] & mask[None, :])
        F = [np.zeros(self.N, bool)]
        F[0][0] = True
        for _ in range(T):
            F.append(L[F[-1]].any(axis=0))
        return F

    def backward(self, T, goal, mask=None):
        L = self.legal if mask is None else (self.legal & mask[:, None] & mask[None, :])
        B = [np.zeros(self.N, bool)]
        B[0][goal] = True
        for _ in range(T):
            B.append(L[:, B[-1]].any(axis=1))
        return B

    def tpar(self, goal, tmax):
        F = [np.zeros(self.N, bool)]
        F[0][0] = True
        for t in range(tmax + 1):
            if F[-1][goal]:
                return t
            F.append(self.legal[F[-1]].any(axis=0))
        return None

    def pmin(self, T, goal):
        for p in range(1, self.n + 1):
            F = self.forward(T, mask=self.pop <= p)
            if F[T][goal]:
                return p
        return None


def alt_schedule(n, dep, s):
    D = dep[s]
    T = 2 * D + 1
    out = []
    for t in range(T + 1):
        P = 0
        for v in range(n):
            k = dep[v]
            if v == s:
                inn = t >= D + 1
            elif k % 2 == 1:
                inn = k + 1 <= t <= 2 * D - k
            else:
                inn = (k + 1 <= t <= k + 2) or (2 * D - k - 1 <= t <= 2 * D - k)
            if inn:
                P |= 1 << v
        out.append(P)
    return out


def analyse(n, pa, want_pmin=True, force=False):
    """1 つの単一シンク DAG を調べ、結果の dict を返す。force=True なら sd でなくても検査する（自己検査用）。"""
    s = n - 1
    dep = depths(n, pa)
    D = dep[s]
    g = is_graded(n, pa, dep)
    sd = is_sink_directed(n, pa, dep, s)
    r = {"graded": g, "sd": sd, "D": D}
    if (not sd and not force) or D < 1:
        return r
    T = 2 * D + 1
    goal = 1 << s
    G = Game(n, pa)
    tp = G.tpar(goal, T + 1)
    r["tpar_ok"] = (tp == T)
    F = G.forward(T)
    B = G.backward(T, goal)
    on = [F[t] & B[T - t] for t in range(T + 1)]          # 時刻 t に現れうる配置
    idx = np.arange(G.N)
    viol = []
    for v in range(n):
        bit = (idx >> v) & 1
        times = [dep[v] + 1, dep[v] + 2]
        if v != s:
            times += [2 * D - dep[v] - 1, 2 * D - dep[v]]
        else:
            times += list(range(D + 1, T + 1))
        for t in times:
            if 0 <= t <= T and (on[t] & (bit == 0)).any():
                viol.append((v, t))
    r["ns_ok"] = not viol
    if viol:
        r["ns_viol"] = viol[:4]
    alt = alt_schedule(n, dep, s)
    r["alt_ok"] = alt[0] == 0 and alt[-1] == goal and all(
        bool(G.legal[alt[t], alt[t + 1]]) for t in range(T))
    if D >= 2:
        lev = [sum(1 for v in range(n) if dep[v] == k) for k in range(D + 1)]
        r["lb01"] = lev[0] + lev[1] + 1
        r["lbmax"] = max(lev[k] + lev[k + 1] for k in range(D))
        lb = max(r["lb01"], r["lbmax"])
        if want_pmin:
            r["pmin"] = G.pmin(T, goal)
            r["peak_ok"] = r["pmin"] >= lb
        else:
            # 下界を 1 下回るピークでクリーンなペブリングが在るかだけを見る（pmin を求めるより速い）
            r["peak_ok"] = not G.forward(T, mask=G.pop <= lb - 1)[T][goal]
    return r


# ───────────────────────────────────────────── 列挙
def enum_pa(n, first_choice=None):
    """位相順・シンク n-1・他の頂点は子を持つ、の DAG を親集合の形で列挙。
    頂点 u（< n-1）の子集合は {u+1..n-1} の空でない部分集合。first_choice で頂点 0 の子集合を固定（分割用）。"""
    choices = []
    for u in range(n - 1):
        hi = list(range(u + 1, n))
        subs = []
        for m in range(1, 1 << len(hi)):
            subs.append(tuple(hi[i] for i in range(len(hi)) if (m >> i) & 1))
        choices.append(subs)
    if first_choice is not None:
        choices[0] = [choices[0][first_choice]]

    def rec(u, pa):
        if u == n - 1:
            yield [frozenset(p) for p in pa]
            return
        for cs in choices[u]:
            for c in cs:
                pa[c].append(u)
            yield from rec(u + 1, pa)
            for c in cs:
                pa[c].pop()
    yield from rec(0, [[] for _ in range(n)])


def shard(args):
    n, fc = args
    st = {"total": 0, "quad": {"g&sd": 0, "g&!sd": 0, "!g&sd": 0, "!g&!sd": 0},
          "sd_checked": 0, "tpar_bad": 0, "ns_bad": 0, "peak_checked": 0, "peak_bad": 0,
          "alt_bad_graded": 0, "alt_bad_nongraded": 0, "alt_checked_nongraded": 0,
          "ex_g_notsd": None, "ex_ns_bad": None, "ex_peak_bad": None, "ex_alt_bad_nongraded": None,
          "ex_tpar_bad": None}
    for pa in enum_pa(n, fc):
        st["total"] += 1
        r = analyse(n, pa, want_pmin=False)
        key = ("g" if r["graded"] else "!g") + "&" + ("sd" if r["sd"] else "!sd")
        st["quad"][key] += 1
        paL = [sorted(p) for p in pa]
        if r["graded"] and not r["sd"] and st["ex_g_notsd"] is None:
            st["ex_g_notsd"] = paL
        if "ns_ok" not in r:
            continue
        st["sd_checked"] += 1
        if not r["tpar_ok"]:
            st["tpar_bad"] += 1
            st["ex_tpar_bad"] = st["ex_tpar_bad"] or paL
        if not r["ns_ok"]:
            st["ns_bad"] += 1
            st["ex_ns_bad"] = st["ex_ns_bad"] or {"pa": paL, "viol": r["ns_viol"]}
        if "peak_ok" in r:
            st["peak_checked"] += 1
            if not r["peak_ok"]:
                st["peak_bad"] += 1
                st["ex_peak_bad"] = st["ex_peak_bad"] or {"pa": paL, **{k: r[k] for k in ("lb01", "lbmax")}}
        if r["graded"]:
            st["alt_bad_graded"] += (not r["alt_ok"])
        else:
            st["alt_checked_nongraded"] += 1
            if not r["alt_ok"]:
                st["alt_bad_nongraded"] += 1
                if st["ex_alt_bad_nongraded"] is None or len(sum(paL, [])) < len(sum(st["ex_alt_bad_nongraded"], [])):
                    st["ex_alt_bad_nongraded"] = paL
    return st


def merge(a, b):
    out = {}
    for k in a:
        if isinstance(a[k], int):
            out[k] = a[k] + b[k]
        elif isinstance(a[k], dict) and k == "quad":
            out[k] = {q: a[k][q] + b[k][q] for q in a[k]}
        else:
            out[k] = a[k] if a[k] is not None else b[k]
    return out


# ───────────────────────────────────────────── 自己検査（既知の値を再現すること）
def selftest():
    ok = True

    def chk(name, cond, detail=""):
        nonlocal ok
        print(("✔ " if cond else "✘ ") + name + (f"  ({detail})" if detail else ""))
        ok &= bool(cond)

    # 鎖 0→1→2→3: Tpar=7, pmin=3（原稿 ex:chain4）, no-slack 成立, graded&sd
    pa = [frozenset(), frozenset({0}), frozenset({1}), frozenset({2})]
    r = analyse(4, pa)
    chk("鎖 4: graded&sd・Tpar=7・no-slack・pmin=3", r["graded"] and r["sd"] and r["tpar_ok"]
        and r["ns_ok"] and r["pmin"] == 3, r)
    # 完全二分木 D=2（7 頂点）: pmin = 3·2^{D-1}+1 = 7、交互スケジュールは合法
    pa = [frozenset()] * 4 + [frozenset({0, 1}), frozenset({2, 3}), frozenset({4, 5})]
    r = analyse(7, pa)
    chk("二分木 D=2: pmin=7・alt 合法・no-slack", r["pmin"] == 7 and r["alt_ok"] and r["ns_ok"], r)
    # 原稿 rem:hyp の反例 1（辺 0→3, 1→2→3）を位相順に並べ替え: 1→a, 順 [1,0,2,3]
    # 頂点 0..3 = (1, 0, 2, 3) の元の名前。pa: 2←{0}, 3←{1,2}
    pa = [frozenset(), frozenset(), frozenset({0}), frozenset({1, 2})]
    s = 3
    dep = depths(4, pa)
    chk("rem:hyp 反例 1 は graded でも sd でもない",
        not is_graded(4, pa, dep) and not is_sink_directed(4, pa, dep, s))
    G = Game(4, pa)
    T = 2 * dep[s] + 1
    F = G.forward(T)
    B = G.backward(T, 1 << s)
    on1 = F[1] & B[T - 1]
    idx = np.arange(G.N)
    chk("rem:hyp 反例 1 で no-slack が破れる（時刻 1 に頂点 1 が無い配置がある）",
        (on1 & (((idx >> 1) & 1) == 0)).any())
    # rem:hyp 反例 2: sources 0,1,2; pa(3)={1,2}, pa(4)={3}, pa(5)={0,4}: pmin=4 < 5
    pa = [frozenset(), frozenset(), frozenset(), frozenset({1, 2}), frozenset({3}), frozenset({0, 4})]
    dep = depths(6, pa)
    G = Game(6, pa)
    T = 2 * dep[5] + 1
    chk("rem:hyp 反例 2: Tpar=7・pmin=4", G.tpar(1 << 5, T + 1) == T and G.pmin(T, 1 << 5) == 4)
    # 本番の判定経路（analyse）が既知の違反を実際に検出すること
    ex1 = [frozenset(), frozenset(), frozenset({0}), frozenset({1, 2})]
    r = analyse(4, ex1, want_pmin=False, force=True)
    chk("analyse が rem:hyp 反例 1 の no-slack 違反を検出", r["ns_ok"] is False, r.get("ns_viol"))
    ex2 = [frozenset(), frozenset(), frozenset(), frozenset({1, 2}), frozenset({3}), frozenset({0, 4})]
    r = analyse(6, ex2, want_pmin=False, force=True)
    chk("analyse（高速経路）が rem:hyp 反例 2 の peak 違反を検出", r["peak_ok"] is False, r)
    r = analyse(6, ex2, want_pmin=True, force=True)
    chk("analyse（pmin 経路）も同じく検出・pmin=4", r["peak_ok"] is False and r["pmin"] == 4, r)
    # ── 片方だけを破る証人（原稿 rem:hyp 用。2026-10-11）
    # (W1) graded だが sink-directed でない: 単一シンクでは存在しない（graded ⇒ sd）。
    #      シンクを 2 つ許せば在る: 鎖 0→2→4（s=4）と、離れた辺 1→3（3 は第 2 のシンク）
    w1 = [frozenset(), frozenset(), frozenset({0}), frozenset({1}), frozenset({2})]
    d1 = depths(5, w1)
    r = analyse(5, w1, want_pmin=True, force=True)
    chk("W1（2 シンク）: graded・¬sd で no-slack も peak 下界も破れる（pmin=3 < n0+n1+1=5）",
        is_graded(5, w1, d1) and not is_sink_directed(5, w1, d1, 4)
        and r["ns_ok"] is False and r["pmin"] == 3 and r["lb01"] == 5, r)
    # (W2) sink-directed だが graded でない: 鎖 0→1→2→3 に近道 0→3。no-slack・peak は成り立ち、
    #      交互スケジュール（thm:alt）だけが非合法になる＝graded は thm:alt のための仮定
    w2 = [frozenset(), frozenset({0}), frozenset({1}), frozenset({0, 2})]
    d2 = depths(4, w2)
    r = analyse(4, w2, want_pmin=True)
    chk("W2: sd・¬graded で no-slack・peak は成立し、交互スケジュールだけが非合法",
        is_sink_directed(4, w2, d2, 3) and not is_graded(4, w2, d2)
        and r["ns_ok"] and r["peak_ok"] and r["alt_ok"] is False, r)
    # 列挙の数: ∏_{u<n-1} (2^{n-1-u}-1)
    for n in (3, 4, 5):
        cnt = sum(1 for _ in enum_pa(n))
        exp = 1
        for u in range(n - 1):
            exp *= (1 << (n - 1 - u)) - 1
        chk(f"列挙数 n={n} = {exp}", cnt == exp, cnt)
    # 変異: 取り除きに親を要求しない（不可逆なペブルゲーム）。鎖 4 で pmin が 3 から 2 に落ち、
    # no-slack も破れるはず＝この検査器の判定が合法性の定義に実際に依存していることの確認
    pa = [frozenset(), frozenset({0}), frozenset({1}), frozenset({2})]
    G = Game(4, pa)
    S = np.arange(16)
    pam = [0, 1, 2, 4]
    need = np.array([sum(pam[v] for v in range(4) if (M >> v) & 1) for M in range(16)])
    G.legal = (need[S[None, :] & ~S[:, None]] & ~S[:, None]) == 0
    pm = G.pmin(7, 1 << 3)
    chk("変異（取り除きに親を要求しない）で鎖 4 の pmin が 3 でなくなる", pm != 3, pm)
    print("自己検査:", "全件合格" if ok else "不合格あり")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int)
    ap.add_argument("--jobs", type=int, default=1)
    ap.add_argument("--out")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        return 0 if selftest() else 1
    n = a.n
    t0 = time.time()
    nfirst = (1 << (n - 1)) - 1
    tasks = [(n, i) for i in range(nfirst)]
    with Pool(a.jobs) as pool:
        parts = pool.map(shard, tasks, chunksize=1)
    st = parts[0]
    for p in parts[1:]:
        st = merge(st, p)
    st["n"] = n
    st["seconds"] = round(time.time() - t0, 1)
    exp = 1
    for u in range(n - 1):
        exp *= (1 << (n - 1 - u)) - 1
    st["total_expected"] = exp
    js = json.dumps(st, ensure_ascii=False, indent=1)
    print(js)
    if a.out:
        open(a.out, "w").write(js + "\n")
    return 0 if st["total"] == exp else 2


if __name__ == "__main__":
    sys.exit(main())
