#!/usr/bin/env python3
"""**「見かけの対称性」を剥がして、本当に効く対称性だけを測る**（2026-09-06）。

前任 `pbcert_symmetry.py` は抽象 CNF h=3 B=5 の自己同型群の位数を **7.46e46** と測り、
自分で「大きすぎる。自由変数の符号反転による見かけの対称性ではないか」と疑った。
本スクリプトはその疑いを**測定で決着させる**ための道具である。

見かけの対称性の源は 3 つある。分けて数えないと「巨大な対称性がある」と誤読する:

1. **どの節にも現れない変数（自由変数）**。Crawford 還元では孤立した K2 成分になり、
   f 個あれば位数に **2^f · f!** を掛ける（内部の極性反転 2 通り × 相互の入れ替え f!）。
   ⚠ 探索にも証明にも一切効かない。**これが今回の主犯である。**
2. **重複した節**。節節点が入れ替わるだけで、変数には何も起きない（d 重の節が
   あれば d! を掛ける）。
3. **極性反転**（変数の値の付け替え）。これは本物の対称性だが、対称性除去で
   使う「変数の置換」とは別物なので、分けて測る。

そこで 3 通りの位数を測る:

| 記号 | 色分け | 意味 |
|---|---|---|
| `G_raw`  | リテラル / 節（自由変数を残す） | 前任が測ったもの |
| `G_full` | 同上（**自由変数を除去**） | 置換 ＋ 極性反転 |
| `G_perm` | 正リテラル / 負リテラル / 節（自由変数を除去） | **極性反転を禁じた＝純粋な変数置換** |

`--selftest` は測定器を**陽性・陰性の対**で検定する（`pbcert_symmetry.py` の
グラフ 5 件に加えて、位数が理論的に決まる CNF 5 件）。ここが合わなければ以降は使わない。
"""
from __future__ import annotations

import argparse
import math
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

GRPSIZE = re.compile(r"grpsize=([0-9.]+(?:e\+?-?[0-9]+)?)")
ORBITS = re.compile(r"([0-9]+) orbit")


def run_dreadnaut(nodes: int, adj: dict[int, set[int]], colors: list[list[int]],
                  timeout: int = 1800) -> tuple[float, float, int, str]:
    """(位数, 位数の log10, 軌道数, エラー文字列)。色は節点番号のリストの列。

    ⚠ 位数は float に入らないことがある（抽象 CNF h=7 で 10^406）。**判定には
    必ず log10 の方を使う**。float 側は表示用で、大きいと `inf` になる。
    """
    lines = [f"n={nodes} g"]
    for v in range(nodes):
        nb = sorted(x for x in adj.get(v, ()) if x > v)
        lines.append(f"{v}: {' '.join(map(str, nb))};")
    lines.append(".")
    lines.append("f=[" + "|".join(",".join(map(str, c)) for c in colors if c) + "]")
    lines.append("c x")
    lines.append("q")
    r = subprocess.run(["dreadnaut"], input="\n".join(lines) + "\n",
                       capture_output=True, text=True, timeout=timeout)
    m = GRPSIZE.search(r.stdout)
    if not m:
        return -1.0, float("nan"), -1, (r.stdout + r.stderr)[-300:]
    s = m.group(1)
    # ⚠ 10^406 は float に入らない。仮数と指数を分けて log10 を作る
    if "e" in s:
        mant, _, ex = s.partition("e")
        lg = math.log10(float(mant)) + int(ex)
    else:
        lg = math.log10(float(s))
    o = ORBITS.search(r.stdout)
    return float(s), lg, (int(o.group(1)) if o else -1), ""


# ------------------------------------------------------------------ 還元 ----

def cnf_graph(nvars: int, clauses: list[list[int]], split_polarity: bool):
    """CNF → 彩色グラフ（Crawford 1992 / Aloul 2003）。

    `split_polarity=True` なら正リテラル節点と負リテラル節点を別の色にする
    ＝**極性反転を禁じる**ので、純粋な変数置換の群だけが残る。
    """
    def lit(l: int) -> int:
        return 2 * (abs(l) - 1) + (0 if l > 0 else 1)

    n_nodes = 2 * nvars + len(clauses)
    adj: dict[int, set[int]] = {}

    def link(a, b):
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)

    for i in range(nvars):
        link(2 * i, 2 * i + 1)
    for ci, c in enumerate(clauses):
        cn = 2 * nvars + ci
        for l in c:
            link(cn, lit(l))
    if split_polarity:
        colors = [[2 * i for i in range(nvars)], [2 * i + 1 for i in range(nvars)],
                  list(range(2 * nvars, n_nodes))]
    else:
        colors = [list(range(2 * nvars)), list(range(2 * nvars, n_nodes))]
    return n_nodes, adj, colors


def cnf_group(nvars: int, clauses: list[list[int]], split_polarity: bool = False,
              timeout: int = 1800):
    n_nodes, adj, colors = cnf_graph(nvars, clauses, split_polarity)
    g, lg, orb, err = run_dreadnaut(n_nodes, adj, colors, timeout)
    return g, lg, orb, n_nodes, err


def strip_free(nvars: int, clauses: list[list[int]]):
    """出現しない変数を落として詰め直す。(新 nvars, 新 clauses, 自由変数の個数)。"""
    used = sorted({abs(l) for c in clauses for l in c})
    ren = {v: i + 1 for i, v in enumerate(used)}
    new = [[(ren[abs(l)] if l > 0 else -ren[abs(l)]) for l in c] for c in clauses]
    return len(used), new, nvars - len(used)


def dup_clauses(clauses: list[list[int]]) -> tuple[int, float]:
    """(重複ぶんの節数, 位数に掛かる因子 Π d_i! の **log10**)。

    d_i! は h=6 で 10^13 を超えるので、桁で持つ。
    """
    import collections
    cnt = collections.Counter(tuple(sorted(set(c))) for c in clauses)
    extra = sum(v - 1 for v in cnt.values() if v > 1)
    log10fac = sum(math.lgamma(v + 1) / math.log(10) for v in cnt.values() if v > 1)
    return extra, log10fac


# ------------------------------------------------------------- 自己試験 ----

def php(pigeons: int, holes: int) -> tuple[int, list[list[int]]]:
    def v(i, j):
        return i * holes + j + 1
    cls = [[v(i, j) for j in range(holes)] for i in range(pigeons)]
    for j in range(holes):
        for i1 in range(pigeons):
            for i2 in range(i1 + 1, pigeons):
                cls.append([-v(i1, j), -v(i2, j)])
    return pigeons * holes, cls


def brute_group(nvars: int, clauses: list[list[int]]) -> int:
    """**独立第 2 実装**: 変数置換 × 極性反転を全数で数える（nvars <= 7 用）。

    dreadnaut は「彩色グラフの自己同型」を数える。それが「CNF の対称性」と
    一致することを、還元を一切使わない素朴な全数で確かめる。
    ⚠ 重複した節があると節節点の入れ替えぶんだけグラフ側が大きくなるので、
    照合には重複の無い CNF を使う。
    """
    from itertools import permutations, product
    target = frozenset(frozenset(c) for c in clauses)
    cnt = 0
    for perm in permutations(range(1, nvars + 1)):
        for flips in product((1, -1), repeat=nvars):
            m = {}
            for i, (p, f) in enumerate(zip(perm, flips), start=1):
                m[i], m[-i] = f * p, -f * p
            if frozenset(frozenset(m[l] for l in c) for c in clauses) == target:
                cnt += 1
    return cnt


def rand_cnf(seed: int, nvars: int, nclauses: int, width: int):
    """決定的な擬似乱数で小さい CNF を作る（重複節は落とす）。"""
    import random
    rnd = random.Random(seed)
    seen, out = set(), []
    for _ in range(nclauses * 3):
        if len(out) >= nclauses:
            break
        vs = rnd.sample(range(1, nvars + 1), width)
        c = tuple(sorted(v if rnd.random() < 0.5 else -v for v in vs))
        if c in seen:
            continue
        seen.add(c)
        out.append(list(c))
    return out


def selftest(timeout: int) -> int:
    bad = 0
    print("=" * 96)
    print("(a) グラフの位数（dreadnaut の呼び出しと読み取りの校正。既知値と照合）")
    print("=" * 96)
    for name, n, edges, want in [
        ("三角形 K3", 3, [(0, 1), (1, 2), (0, 2)], 6.0),
        ("道 P3", 3, [(0, 1), (1, 2)], 2.0),
        ("K4", 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)], 24.0),
        ("閉路 C5", 5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], 10.0),
        ("K3,3", 6, [(i, 3 + j) for i in range(3) for j in range(3)], 72.0),
    ]:
        adj: dict[int, set[int]] = {i: set() for i in range(n)}
        for a, b in edges:
            adj[a].add(b)
            adj[b].add(a)
        got, _, _, err = run_dreadnaut(n, adj, [list(range(n))], timeout)
        ok = abs(got - want) < 1e-6
        bad += 0 if ok else 1
        print(f"  [{'OK ' if ok else '**NG**'}] {name:<12} 位数 {got:>12}（既知 {want}）{err}")

    print()
    print("=" * 96)
    print("(b) CNF の位数を**独立第 2 実装（全数）**と突き合わせる")
    print("=" * 96)
    print("    ⚠ 予測を手で立てると外す。実際 2026-09-06 に「単位節 6 本で自明群」と")
    print("      書いて 2 が出た（鳩 0 と鳩 2 の単位節の並びが同型だっただけで、")
    print("      測定器は正しかった）。そこで手の予測をやめ、全数実装を基準にする。")
    cases = [("PHP(3,2) 対称群 S3×S2", *php(3, 2))]
    cases.append(("PHP(3,2)+単位節（対称性を壊す）", *(lambda t: (t[0], t[1] + [[1]]))(php(3, 2))))
    cases.append(("極性反転だけが対称性: (x1∨x2)(~x1∨~x2)", 2, [[1, 2], [-1, -2]]))
    cases.append(("自由変数 2 個つき PHP(3,2)", php(3, 2)[0] + 2, php(3, 2)[1]))
    for s in range(1, 9):
        cases.append((f"乱択 CNF seed={s}（6 変数・9 節・幅 3）", 6, rand_cnf(s, 6, 9, 3)))
    for name, n, c in cases:
        want = brute_group(n, c)
        got, _, orb, _, err = cnf_group(n, c, False, timeout)
        ok = abs(got - want) <= max(1e-6, want * 1e-5)
        bad += 0 if ok else 1
        tag = "対称性あり" if want > 1 else "**対称性なし（陰性）**"
        print(f"  [{'OK ' if ok else '**NG**'}] {name:<42} dreadnaut {got:>10.6g} / "
              f"全数 {want:>8}  {tag} {err}")

    print()
    print("  --- 自由変数が位数に掛ける因子 2^f · f! の校正（今回の主張の要）---")
    for f in (0, 1, 3, 5, 8):
        nv, cls = php(4, 3)
        got, _, _, _, err = cnf_group(nv + f, cls, False, timeout)
        want = 144.0 * (2 ** f) * math.factorial(f)
        ok = abs(got - want) <= want * 1e-6
        bad += 0 if ok else 1
        print(f"  [{'OK ' if ok else '**NG**'}] PHP(4,3) に未使用変数 {f} 個を足す: "
              f"位数 {got:>16.6g}（予測 144·2^{f}·{f}! = {want:.6g}）{err}")
    got, _, _, _, _ = cnf_group(php(3, 2)[0] + 2, php(3, 2)[1], False, timeout)
    want = brute_group(php(3, 2)[0] + 2, php(3, 2)[1])
    print(f"  [{'OK ' if abs(got - want) < 1e-6 else '**NG**'}] 同じ因子を全数でも確認: "
          f"PHP(3,2)+自由変数 2 個 = {got:g} / 全数 {want}（= 12·2^2·2! = {12*4*2}）")

    print()
    print("測定器 校正 OK（既知値・全数実装と一致。対称性のある側と無い側の両方で）" if bad == 0
          else f"**校正 NG: {bad} 件。以降の位数を使ってはいけない**")
    return bad



# ------------------------------------------- PB レベル（Sinz 展開前）の対称性 ----

def pb_graph(nvars: int, clauses: list[list[int]], cards: list[tuple[list[int], int]],
             split_polarity: bool = False):
    """節 ＋ **基数制約を 1 個の節点として持つ**グラフ。

    Sinz の逐次カウンタは `lits` の**順序**に依存するので、基数制約が本来もつ
    「リテラルの入れ替えで不変」という性質を壊す。ここでは基数制約を 1 節点
    （次数 = リテラル数）で表し、**壊す前の対称性**を測る。
    基数制約の節点は右辺 k ごとに色を分ける（k が違うものを同一視しないため）。
    """
    def lit(l: int) -> int:
        return 2 * (abs(l) - 1) + (0 if l > 0 else 1)

    n_nodes = 2 * nvars + len(clauses) + len(cards)
    adj: dict[int, set[int]] = {}

    def link(a, b):
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)

    for i in range(nvars):
        link(2 * i, 2 * i + 1)
    for ci, c in enumerate(clauses):
        cn = 2 * nvars + ci
        for l in c:
            link(cn, lit(l))
    by_k: dict[int, list[int]] = {}
    for di, (lits, k) in enumerate(cards):
        dn = 2 * nvars + len(clauses) + di
        by_k.setdefault(k, []).append(dn)
        for l in lits:
            link(dn, lit(l))

    if split_polarity:
        colors = [[2 * i for i in range(nvars)], [2 * i + 1 for i in range(nvars)]]
    else:
        colors = [list(range(2 * nvars))]
    colors.append(list(range(2 * nvars, 2 * nvars + len(clauses))))
    for k in sorted(by_k):
        colors.append(by_k[k])
    return n_nodes, adj, colors


def pb_group(nvars, clauses, cards, split_polarity=False, timeout=1800):
    n_nodes, adj, colors = pb_graph(nvars, clauses, cards, split_polarity)
    g, lg, orb, err = run_dreadnaut(n_nodes, adj, colors, timeout)
    return g, lg, orb, n_nodes, err


def pyramid_mirror_check(h: int, T: int) -> str:
    """ピラミッドの**左右鏡映**が符号化の対称性になっているかを、nauty を使わずに直接見る。

    鏡映 (lvl,k) -> (lvl, h-lvl-1-k) は DAG の自己同型。x[v][t] -> x[mirror(v)][t] が
    節集合を保つかを集合の一致で判定する（測定器から独立した確認）。
    """
    import q2_cnf
    par, sk = q2_cnf.pyramid(h)
    n = len(par)
    idx, inv = {}, {}
    for lvl in range(h):
        for k in range(h - lvl):
            v = len(idx)
            idx[(lvl, k)] = v
            inv[v] = (lvl, k)
    mir = [idx[(lvl, h - lvl - 1 - k)] for v in range(n) for (lvl, k) in [inv[v]]]

    out = []
    for tag, p in (("構造節のみ（基数制約なし）", n), ("Sinz 展開つき（p=p_min-1）", None)):
        if p is None:
            P_MIN = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16}
            if h not in P_MIN:
                continue
            p = P_MIN[h] - 1
        c = q2_cnf.build(par, sk, p, T, window=True)
        nx = n * (T + 1)                    # x[v][t] は先頭に v 優先で並ぶ
        def m(l: int) -> int:
            a = abs(l)
            if a > nx:
                return l                     # 補助変数は動かさない
            v, t = (a - 1) // (T + 1), (a - 1) % (T + 1)
            b = mir[v] * (T + 1) + t + 1
            return b if l > 0 else -b
        S = frozenset(frozenset(cl) for cl in c.cls)
        S2 = frozenset(frozenset(m(l) for l in cl) for cl in c.cls)
        out.append(f"    {tag:<28} 節 {len(c.cls):>6} 補助変数 {c.n - nx:>6}  "
                   f"鏡映で不変か: {'**はい**' if S == S2 else '**いいえ**'}")
    return "\n".join(out)


# ------------------------------------------------------------------ 本番 ----

def dedup(clauses: list[list[int]]) -> list[list[int]]:
    seen, out = set(), []
    for c in clauses:
        k = tuple(sorted(set(c)))
        if k not in seen:
            seen.add(k)
            out.append(list(c))
    return out


def _l10(x: float) -> float:
    return math.log10(x) if x > 0 else float("-inf")


def report(label: str, nvars: int, clauses: list[list[int]], timeout: int) -> None:
    """見かけの対称性を 2 段階で剥がし、残った位数を「本当に効く対称性」と呼ぶ。"""
    g_raw, lg_raw, orb_raw, nn_raw, e1 = cnf_group(nvars, clauses, False, timeout)

    nv2, cls2, nfree = strip_free(nvars, clauses)
    g_nofree, lg_nofree, _, _, e2 = cnf_group(nv2, cls2, False, timeout)

    cls3 = dedup(cls2)
    nv3, cls3, _ = strip_free(nv2, cls3)
    g_clean, lg_clean, orb_clean, _, e3 = cnf_group(nv3, cls3, False, timeout)
    g_perm, _, _, _, e4 = cnf_group(nv3, cls3, True, timeout)

    ndup, dupfac_log = dup_clauses(clauses)

    # log10 で突き合わせる（f! は f=138 で float に入らない）
    pred_log = lg_clean + nfree * math.log10(2) + \
        (math.lgamma(nfree + 1) / math.log(10)) + dupfac_log
    gap = abs(pred_log - lg_raw)

    print(f"\n### {label}")
    print(f"  変数 {nvars}（**どの節にも現れない** {nfree}）/ 節 {len(clauses)}"
          f"（**重複** {ndup} 本・因子 10^{dupfac_log:.2f}）/ 節点 {nn_raw}")
    print(f"  G_raw   自由変数も重複節も残す（＝前任が測った量）  = 10^{lg_raw:.3f}"
          f"  ({g_raw:.6g}) {e1}")
    print(f"  G_nofree 自由変数を除去                        = 10^{lg_nofree:.3f}"
          f"  ({g_nofree:.6g}) {e2}")
    print(f"  **G_clean 自由変数＋重複節を除去（置換＋極性反転）= {g_clean:.6g}**"
          f"  軌道 {orb_clean} {e3}")
    print(f"  **G_perm  さらに極性反転も禁止（純粋な変数置換）  = {g_perm:.6g}** {e4}")
    print(f"  ⇒ 内訳の検算: G_clean · 2^{nfree} · {nfree}! · 重複因子 = 10^{pred_log:.3f} "
          f"vs G_raw = 10^{lg_raw:.3f}  差 {gap:.2e} 桁"
          f"{'  → **G_raw は見かけの対称性で説明しきれる**' if gap < 1e-6 else '  → **説明できない残差あり**'}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--hs", default="3,4,5")
    ap.add_argument("--pebbling", action="store_true",
                    help="本物のペブリング CNF（x[v][t]）も測る")
    ap.add_argument("--pb", action="store_true",
                    help="**Sinz 展開前**（基数制約を 1 本のまま）の対称性を測る")
    ap.add_argument("--timeout", type=int, default=1800)
    a = ap.parse_args()
    if a.selftest:
        return 1 if selftest(a.timeout) else 0

    import pbcert_pyr_opb as enc
    from pbcert_measure import L_ABSTRACT

    if a.pb:
        import q2_cnf
        P_MIN = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16}
        for h in [int(x) for x in a.hs.split(",")]:
            B = L_ABSTRACT[h] - 1
            print(f"\n### h={h}: **Sinz 展開の前後**で対称性がどう変わるか")

            # (1) 抽象系: PB レベル（ピーク制約 1 本） vs CNF レベル（Sinz 展開後）
            pb = enc.build(h, B)
            cl = [it[1] for it in pb.items if it[0] == "cl"]
            cd = [(it[1], it[2]) for it in pb.items if it[0] == "am"]
            nv3, cl3, _ = strip_free(pb.n, cl + [l for l, _ in cd])
            # strip_free は節としてしか見ないので、基数制約も込みで使用変数を決める
            used = sorted({abs(l) for c in cl for l in c} |
                          {abs(l) for lits, _ in cd for l in lits})
            ren = {v: i + 1 for i, v in enumerate(used)}
            cl_r = [[(ren[abs(l)] if l > 0 else -ren[abs(l)]) for l in c] for c in dedup(cl)]
            cd_r = [([ren[abs(l)] for l in lits], k) for lits, k in cd]
            g, lg, orb, nn, err = pb_group(len(used), cl_r, cd_r, False, a.timeout)
            gp, _, _, _, _ = pb_group(len(used), cl_r, cd_r, True, a.timeout)
            print(f"  抽象 **PB レベル**（ピーク制約 {len(cd)} 本を 1 節点ずつで表現）"
                  f" 変数 {len(used)} 節 {len(cl_r)}")
            print(f"      G = {g:.6g}（極性反転を禁じると {gp:.6g}） 軌道 {orb} {err}")

            # (2) ペブリング系: 基数制約を外した構造節のみ
            par, sk = q2_cnf.pyramid(h)
            n = len(par)
            T = 2 * (h - 1) + 1
            cstruct = q2_cnf.build(par, sk, n, T, window=True)   # p=n なので atmost は空
            nvs, cls_s, nf = strip_free(cstruct.n, dedup(cstruct.cls))
            g2, _, orb2, _, e2 = cnf_group(nvs, cls_s, False, a.timeout)
            print(f"  ペブリング **構造節のみ**（基数制約なし） 変数 {nvs} 節 {len(cls_s)}")
            print(f"      G = {g2:.6g} 軌道 {orb2} {e2}")

            # (3) ペブリング系: 構造節 ＋ 基数制約を 1 節点で
            if h in P_MIN:
                p = P_MIN[h] - 1
                dep = q2_cnf.depths(par)
                D = dep[sk]
                lo = [min(dep[v] + 1, T) for v in range(n)]
                hi = [T if v == sk else max(T - dep[v] - 1, 0) for v in range(n)]
                nx = n * (T + 1)
                cards = []
                for t in range(T + 1):
                    live = [v for v in range(n) if lo[v] <= t <= hi[v]]
                    cards.append(([v * (T + 1) + t + 1 for v in live], p))
                used2 = sorted({abs(l) for c in cstruct.cls for l in c} |
                               {abs(l) for lits, _ in cards for l in lits})
                ren2 = {v: i + 1 for i, v in enumerate(used2)}
                cl2 = [[(ren2[abs(l)] if l > 0 else -ren2[abs(l)]) for l in c]
                       for c in dedup(cstruct.cls)]
                cd2 = [([ren2[l] for l in lits], k) for lits, k in cards]
                g3, _, orb3, _, e3 = pb_group(len(used2), cl2, cd2, False, a.timeout)
                print(f"  ペブリング **PB レベル**（各時刻のピークを 1 節点） "
                      f"変数 {len(used2)} 節 {len(cl2)} 基数 {len(cd2)}")
                print(f"      G = {g3:.6g} 軌道 {orb3} {e3}")

            print("  --- nauty を使わない直接確認（左右鏡映が符号化の対称性か）---")
            print(pyramid_mirror_check(h, T))
        return 0

    for h in [int(x) for x in a.hs.split(",")]:
        B = L_ABSTRACT[h] - 1
        nv, cls = enc.build(h, B).to_cnf()
        report(f"抽象 CNF h={h} B={B}（DRAT 基準線が使っているもの）", nv, cls, a.timeout)

        if a.pebbling:
            import q2_cnf
            P_MIN = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16}
            if h in P_MIN:
                par, sk = q2_cnf.pyramid(h)
                c = q2_cnf.build(par, sk, P_MIN[h] - 1, 2 * (h - 1) + 1, window=True)
                report(f"ペブリング CNF h={h} p={P_MIN[h]-1}", c.n, c.cls, a.timeout)
    return 0


if __name__ == "__main__":
    sys.exit(main())
