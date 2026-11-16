#!/usr/bin/env python3
"""候補10 — 最小ガベージ幅の厳密表（依存: 標準ライブラリのみ、決定的）。

3 つの模型を区別する。$f:\\{0,1\\}^n \\to \\{0,1\\}^m$ に対し

  (F) 自由ガベージ模型: 単射 $x \\mapsto (f(x), \\gamma(x))$、$\\gamma$ は任意。
      最小幅 $g_{\\mathrm{free}}(f)$。
  (P) 射影ガベージ模型: $\\gamma(x) = x|_S$（入力ビットの部分集合）に限る。
      最小幅 $g_{\\mathrm{proj}}(f) = \\min\\{|S| : x \\mapsto (f(x), x|_S)$ が単射$\\}$。
  (G) ゲート引数個数制約: 幅 $N$ の線に arity $< N$ のゲートだけを載せる。
      このとき実現できるのは偶置換のみ（`perm_sign` で検査）。

情報論的下界 $\\mathrm{lb}(f) = \\lceil \\log_2 \\max_y |f^{-1}(y)| \\rceil$ は (F) では
常に達成される（自明・既知: Toffoli 1980, Maslov–Dueck 2006）。(P) では緩む。

使い方:
    python3 scripts/exp10_garbage.py            # 全実験（n<=4）
    python3 scripts/exp10_garbage.py --quick    # n<=3 のみ
"""

from __future__ import annotations

import argparse
import itertools
import sys
from collections import Counter

# ---------------------------------------------------------------- 基本ユーティリティ


def bits(x: int, n: int) -> tuple[int, ...]:
    """x の下位 n ビット。インデックス i がビット i（LSB 始まり）。"""
    return tuple((x >> i) & 1 for i in range(n))


def truth_table(n: int, fn) -> tuple[int, ...]:
    """fn: bits タプル -> 出力整数。長さ 2^n の真理値表を返す。"""
    return tuple(fn(bits(x, n)) for x in range(1 << n))


def clog2(k: int) -> int:
    """ceil(log2 k)（k >= 1）。"""
    g = 0
    while (1 << g) < k:
        g += 1
    return g


def fiber_sizes(tt) -> Counter:
    return Counter(tt)


def lower_bound(tt) -> int:
    """情報論的下界 ceil(log2 max_y |f^{-1}(y)|)。"""
    return clog2(max(fiber_sizes(tt).values()))


# ---------------------------------------------------------------- (F) 自由ガベージ


def g_free(tt) -> int:
    """自由ガベージ模型の最小幅（閉じた式による実装）。"""
    return lower_bound(tt)


def _exists_injective_assignment(tt, g: int) -> bool:
    """素朴な後戻り探索: 各 x にガベージ値 in [0,2^g) を割り当てて
    x -> (f(x), gamma(x)) を単射にできるか。閉じた式を一切使わない。"""
    n_in = len(tt)
    used: set[tuple[int, int]] = set()
    order = list(range(n_in))

    def rec(i: int) -> bool:
        if i == n_in:
            return True
        for v in range(1 << g):
            key = (tt[order[i]], v)
            if key in used:
                continue
            used.add(key)
            if rec(i + 1):
                return True
            used.discard(key)
        return False

    return rec(0)


def g_free_bruteforce(tt, gmax: int = 6) -> int | None:
    """自由ガベージ模型の最小幅（探索による独立実装。二重実装照合用）。"""
    for g in range(gmax + 1):
        if _exists_injective_assignment(tt, g):
            return g
    return None


# ---------------------------------------------------------------- (P) 射影ガベージ


def is_proj_injective(tt, n: int, subset_mask: int) -> bool:
    seen = set()
    for x in range(1 << n):
        key = (tt[x], x & subset_mask)
        if key in seen:
            return False
        seen.add(key)
    return True


def g_proj(tt, n: int) -> int:
    """min |S| s.t. x -> (f(x), x|_S) が単射。"""
    for size in range(n + 1):
        for S in itertools.combinations(range(n), size):
            mask = 0
            for i in S:
                mask |= 1 << i
            if is_proj_injective(tt, n, mask):
                return size
    raise AssertionError("S = 全ビットなら必ず単射なのでここには来ない")


def is_proj_injective_subcube(tt, n: int, subset_mask: int) -> bool:
    """独立実装（二重実装照合用）。`ProjOK` の言い換え:
    「S のビットを固定した各部分キューブ上で f が単射」。
    素朴実装（`is_proj_injective`）は組 (f(x), x|_S) の重複を見るのに対し、
    こちらは対 (a,b) を回して「S 上で一致し f 値も一致するなら a=b」を確かめる。"""
    for a in range(1 << n):
        for b in range(a + 1, 1 << n):
            if (a & subset_mask) == (b & subset_mask) and tt[a] == tt[b]:
                return False
    return True


def g_proj_subcube(tt, n: int) -> int:
    for size in range(n + 1):
        for S in itertools.combinations(range(n), size):
            mask = 0
            for i in S:
                mask |= 1 << i
            if is_proj_injective_subcube(tt, n, mask):
                return size
    raise AssertionError("到達不能")


def g_proj_witnesses(tt, n: int) -> list[tuple[int, ...]]:
    """最小サイズを達成する S の一覧。"""
    g = g_proj(tt, n)
    out = []
    for S in itertools.combinations(range(n), g):
        mask = 0
        for i in S:
            mask |= 1 << i
        if is_proj_injective(tt, n, mask):
            out.append(S)
    return out


# ---------------------------------------------------------------- (G) ゲートとパリティ


def gate_permutation(N: int, targets: tuple[int, ...], perm: tuple[int, ...]) -> tuple[int, ...]:
    """N 線のうち targets（線番号のタプル、長さ k）に {0,1}^k 上の置換 perm を載せた
    ゲートが誘導する {0,1}^N 上の置換。targets[j] が perm の入力ビット j に対応。"""
    k = len(targets)
    assert len(perm) == (1 << k)
    out = []
    for x in range(1 << N):
        sub = 0
        for j, t in enumerate(targets):
            sub |= ((x >> t) & 1) << j
        img = perm[sub]
        y = x
        for j, t in enumerate(targets):
            b = (img >> j) & 1
            y = (y & ~(1 << t)) | (b << t)
        out.append(y)
    return tuple(out)


def perm_sign(p) -> int:
    """置換の符号（+1 / -1）。巡回分解の偶奇。"""
    seen = [False] * len(p)
    sign = 1
    for i in range(len(p)):
        if seen[i]:
            continue
        length = 0
        j = i
        while not seen[j]:
            seen[j] = True
            j = p[j]
            length += 1
        if length % 2 == 0:
            sign = -sign
    return sign


def nct_generators(N: int) -> list[tuple[int, ...]]:
    """N 線上の NOT / CNOT / Toffoli（多重制御は N-1 制御まで）の生成元。"""
    gens = []
    for t in range(N):
        # NOT
        gens.append(tuple(x ^ (1 << t) for x in range(1 << N)))
        others = [i for i in range(N) if i != t]
        for nc in range(1, N):
            for ctrl in itertools.combinations(others, nc):
                cmask = 0
                for c in ctrl:
                    cmask |= 1 << c
                gens.append(
                    tuple(
                        (x ^ (1 << t)) if (x & cmask) == cmask else x
                        for x in range(1 << N)
                    )
                )
    return gens


def compose(p, q):
    """まず q、次に p（p∘q）。"""
    return tuple(p[q[i]] for i in range(len(q)))


def generated_group_size(N: int, limit: int = 1_000_000) -> tuple[int, bool]:
    """NCT 生成元が生成する {0,1}^N 上の置換群の位数と、全要素が偶置換かどうか。"""
    gens = nct_generators(N)
    ident = tuple(range(1 << N))
    seen = {ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for p in frontier:
            for gg in gens:
                q = compose(gg, p)
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
                    if len(seen) > limit:
                        raise RuntimeError("群が大きすぎる")
        frontier = nxt
    all_even = all(perm_sign(p) == 1 for p in seen)
    return len(seen), all_even


def arity_bounded_gates_all_even(N: int) -> tuple[int, bool]:
    """N 線上の arity <= N-1 の**すべての**ゲート（任意の置換を載せる）が
    偶置換を誘導することを全数検査する。"""
    count = 0
    for k in range(1, N):
        for targets in itertools.permutations(range(N), k):
            for perm in itertools.permutations(range(1 << k)):
                if perm_sign(gate_permutation(N, targets, perm)) != 1:
                    return count, False
                count += 1
    return count, True


def parity_is_free_with_ancilla(n: int, N: int, tt, m: int) -> dict:
    """入力を (x, 0^{N-n}) に置く埋め込みでは、非正規領域（アンシラが 0 でない入力）が
    2^N - 2^n >= 2 個あるので、そこの 2 点を入れ替えて符号を反転できる。
    実際に埋め込み 1 個を作り、両符号が得られることを構成的に確認する。"""
    assert N >= n and (N - n) >= 1
    g = N - m
    assert g >= lower_bound(tt), "幅が足りない"
    # 正規領域 (x, 0^{N-n}) -> (f(x), gamma(x)) を貪欲に作る
    F = [None] * (1 << N)
    used = set()
    counter: Counter = Counter()
    for x in range(1 << n):
        y = tt[x]
        v = counter[y]
        counter[y] += 1
        img = y | (v << m)
        assert img < (1 << N), "ガベージ幅が足りない"
        F[x] = img
        used.add(img)
    free_dom = [i for i in range(1 << N) if F[i] is None]
    free_img = [i for i in range(1 << N) if i not in used]
    assert len(free_dom) == len(free_img)
    for d, im in zip(free_dom, free_img):
        F[d] = im
    F = tuple(F)
    s1 = perm_sign(F)
    # 非正規領域の 2 点の像を入れ替える（正規領域の制約は不変）
    assert len(free_dom) >= 2, "自由点が 2 個未満"
    G = list(F)
    a, b = free_dom[0], free_dom[1]
    G[a], G[b] = G[b], G[a]
    s2 = perm_sign(tuple(G))
    return {"n": n, "N": N, "free_points": len(free_dom), "sign1": s1, "sign2": s2}


# ---------------------------------------------------------------- 全数列挙


def set_partitions(elements: list[int]):
    """集合分割をすべて列挙（ブロックのリストのリスト）。"""
    if not elements:
        yield []
        return
    first, rest = elements[0], elements[1:]
    for part in set_partitions(rest):
        for i in range(len(part)):
            yield part[:i] + [[first] + part[i]] + part[i + 1 :]
        yield [[first]] + part


def partition_to_tt(part, size: int) -> tuple[int, ...]:
    tt = [0] * size
    for idx, block in enumerate(part):
        for x in block:
            tt[x] = idx
    return tuple(tt)


def scan_all_partitions(n: int):
    """n 入力の**すべての**関数を出力ラベルの付け替えを除いて走査する。
    lb・g_proj はファイバー分割のみで決まるので、集合分割の列挙で全 m を一挙に覆う。"""
    size = 1 << n
    rows = []
    for part in set_partitions(list(range(size))):
        tt = partition_to_tt(part, size)
        lb = lower_bound(tt)
        gp = g_proj(tt, n)
        rows.append((tt, lb, gp))
    return rows


def scan_single_output(n: int):
    """n 入力 1 出力の全 2^{2^n} 関数を走査。"""
    size = 1 << n
    rows = []
    for code in range(1 << size):
        tt = tuple((code >> x) & 1 for x in range(size))
        rows.append((tt, lower_bound(tt), g_proj(tt, n)))
    return rows


# ---------------------------------------------------------------- 実験本体


def fmt_tt(tt) -> str:
    return "".join(str(v) for v in tt)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="n<=3 のみ")
    args = ap.parse_args(argv)

    print("=" * 72)
    print("実験 A: 自由ガベージ模型では下界が常に達成される（自明性の確認）")
    print("=" * 72)
    mismatch = 0
    checked = 0
    for part in set_partitions(list(range(8))):
        tt = partition_to_tt(part, 8)
        if g_free(tt) != lower_bound(tt):
            mismatch += 1
        checked += 1
    print(f"n=3 の全 {checked} 分割（= 出力ラベル付け替えを除く全関数）で")
    print(f"  g_free == lb の不一致: {mismatch} 件")
    print("素朴な後戻り探索との二重実装照合（分割を 200 個間引いて）:")
    bf_mismatch = 0
    bf_checked = 0
    for i, part in enumerate(set_partitions(list(range(8)))):
        if i % 21 != 0:
            continue
        tt = partition_to_tt(part, 8)
        if g_free_bruteforce(tt) != g_free(tt):
            bf_mismatch += 1
        bf_checked += 1
    print(f"  照合 {bf_checked} 件、不一致 {bf_mismatch} 件")

    print()
    print("=" * 72)
    print("実験 B: 射影ガベージ模型では下界が緩む（n=3 全数）")
    print("=" * 72)
    rows = scan_all_partitions(3)
    hist: Counter = Counter()
    for tt, lb, gp in rows:
        hist[(lb, gp)] += 1
    print(f"n=3: 全 {len(rows)} 分割")
    print("  (lb, g_proj) -> 個数")
    for key in sorted(hist):
        print(f"    {key} -> {hist[key]}")
    gap_hist = Counter(gp - lb for _, lb, gp in rows)
    print("  gap = g_proj - lb のヒストグラム:", dict(sorted(gap_hist.items())))
    # 最小の反例（gap>0 でブロック数が最小、次に lb が最小）
    gaps = [(tt, lb, gp) for tt, lb, gp in rows if gp > lb]
    gaps.sort(key=lambda r: (r[2] - r[1], len(set(r[0])), r[1], r[0]))
    print(f"  gap>0 の分割: {len(gaps)} 件。最小の例（ブロック数の少ない順に 5 件）:")
    for tt, lb, gp in gaps[:5]:
        print(f"    tt={fmt_tt(tt)} blocks={len(set(tt))} lb={lb} g_proj={gp}")
    maxgap = max(gap_hist)
    print(f"  n=3 での最大 gap = {maxgap}")

    print()
    print("=" * 72)
    print("実験 B2: g_proj の二重実装照合（素朴 vs 部分キューブ単射性）")
    print("=" * 72)
    bad = 0
    for tt, lb, gp in rows:
        if g_proj_subcube(tt, 3) != gp:
            bad += 1
    print(f"  n=3 の全 {len(rows)} 分割で不一致: {bad} 件")

    print()
    print("=" * 72)
    print("実験 C: 射影ガベージ模型 n=4、1 出力の全 65536 関数")
    print("=" * 72)
    if args.quick:
        print("  --quick 指定によりスキップ")
    else:
        rows4 = scan_single_output(4)
        hist4 = Counter((lb, gp) for _, lb, gp in rows4)
        print(f"n=4, m=1: 全 {len(rows4)} 関数")
        for key in sorted(hist4):
            print(f"    (lb,g_proj)={key} -> {hist4[key]}")
        gap4 = Counter(gp - lb for _, lb, gp in rows4)
        print("  gap ヒストグラム:", dict(sorted(gap4.items())))
        worst = max(gap4)
        ex = [r for r in rows4 if r[2] - r[1] == worst][:3]
        print(f"  最大 gap = {worst}、例:")
        for tt, lb, gp in ex:
            print(f"    tt={fmt_tt(tt)} lb={lb} g_proj={gp}")

    print()
    print("=" * 72)
    print("実験 D: ゲート引数個数制約下のパリティ障害")
    print("=" * 72)
    for N in (2, 3, 4):
        cnt, ok = arity_bounded_gates_all_even(N)
        print(f"  N={N}: arity<=N-1 の全ゲート {cnt} 個、すべて偶置換 = {ok}")
    for N in (2, 3):
        size, all_even = generated_group_size(N)
        total = 1
        for i in range(1, (1 << N) + 1):
            total *= i
        print(
            f"  N={N}: <NOT,CNOT,...,C^{N-1}NOT> の位数 = {size}"
            f"（|S_{{2^{N}}}| = {total}, 全偶置換 = {all_even}）"
        )

    print()
    print("=" * 72)
    print("実験 E: アンシラが 1 本でもあればパリティ障害は消える（構成的確認）")
    print("=" * 72)
    MAJ3 = truth_table(3, lambda b: 1 if sum(b) >= 2 else 0)
    for N in (4, 5):
        r = parity_is_free_with_ancilla(3, N, MAJ3, 1)
        print(
            f"  n=3,N={N}: 自由点 {r['free_points']} 個、"
            f"符号 {r['sign1']:+d} と入替後 {r['sign2']:+d} の両方が実現可能"
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
