#!/usr/bin/env python3
"""IC3 が構成した不変量の**節が何を言っているか**を記述統計で見る（2026-09-06）。

§12 で不変量が正しいことは外部検証済み。ここは「中身を読む」側の第一歩で、
docs/35 の負の結果（足りないのは位置情報・鍵は $\\mathrm{runs}(S)$）と突き合わせる。

不変量は $I = \\lnot\\bigvee_C C$ なので、**各 cube $C$ は「この形は起きない」という禁止形**である。
cube の中の値 1 のリテラルは「その頂点に居る」、値 0 は「居ない」を指す。

見るもの（すべて**記述統計**。因果や必要性は主張しない）:

1. 時刻を確定させている cube の割合と、その時刻の分布
2. 節が触れる層の分布
3. **run 構造**: 各層で「居る」と指定された位置が何個の連続塊に分かれるか。
   docs/35 の Lean 定理 `touchable_card_add_runs`（触れる子の個数 + runs = |S|）が
   効くのは run が少ないときなので、**PDR の節が run の少ない形を狙って禁止しているか**を見る。
   ⚠ 比較のため**同じ個数・同じ層幅で位置だけを一様に散らした帰無モデル**の期待 run 数を併記する
   （閉形式 $E[\\mathrm{runs}] = m(n-m+1)/n$、$m$ 個を幅 $n$ に置いたとき）。

使い方:
  ic3_clause_stats.py --h 13 --p 36 --inv notes/ic3/invariants/pyr_h13_p36.inv.gz
"""
from __future__ import annotations

import argparse
import gzip
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ic3_pyramid import Model  # noqa: E402


def read_pla(path: str):
    op = gzip.open if path.endswith(".gz") else open
    names, cubes = [], []
    with op(path, "rt") as f:
        for ln in f:
            ln = ln.strip()
            if ln.startswith(".ilb"):
                names = ln.split()[1:]
            elif ln.startswith(".") or ln.startswith("#") or not ln:
                continue
            else:
                cubes.append(ln.split()[0])
    return names, cubes


def runs(sorted_pos: list[int]) -> int:
    if not sorted_pos:
        return 0
    return 1 + sum(1 for i in range(1, len(sorted_pos))
                   if sorted_pos[i] != sorted_pos[i - 1] + 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--inv", required=True)
    a = ap.parse_args()
    m = Model(a.h, a.p)
    names, cubes = read_pla(a.inv)
    tw = max(1, (m.T).bit_length())
    base, layer, width = {}, {}, {}
    vid = 0
    for lvl in range(m.h):
        base[lvl] = vid
        width[lvl] = m.h - lvl
        for _ in range(m.h - lvl):
            layer[vid] = lvl
            vid += 1
    sup = [int(nm[2:]) for nm in names]

    n_t_exact = 0
    n_dead = 0
    tbits_hist = Counter()
    t_hist = Counter()
    layer_hist = Counter()
    obs_runs = tot_ones = 0
    exp_runs = 0.0
    per_layer_runs: dict[int, list[tuple[int, int, int]]] = {}
    full_pairs = [0, 0]
    nf = [0, 0, 0.0]
    size_hist = Counter()

    for pat in cubes:
        spec = {j: int(ch) for j, ch in zip(sup, pat) if ch != "-"}
        size_hist[len(spec)] += 1
        tb = [j for j in spec if m.n <= j < m.n + tw]
        tbits_hist[len(tb)] += 1
        if len(tb) == tw:
            n_t_exact += 1
            t_hist[sum(spec[m.n + i] << i for i in range(tw))] += 1
        if m.n + tw in spec:
            n_dead += 1
        ones: dict[int, list[int]] = {}
        for j, v in spec.items():
            if j < m.n:
                layer_hist[layer[j]] += 1
                if v == 1:
                    ones.setdefault(layer[j], []).append(j - base[layer[j]])
        for lvl, pos in ones.items():
            pos.sort()
            r = runs(pos)
            obs_runs += r
            tot_ones += len(pos)
            n, k = width[lvl], len(pos)
            exp_runs += k * (n - k + 1) / n
            per_layer_runs.setdefault(lvl, []).append((k, r, n))
            # ⚠ 対抗仮説: 両端強制で層が丸ごと在るなら塊が 1 個になるのは当たり前。
            #   層まるごとを除いた分も別に集計する。
            if k == n:
                full_pairs[0] += 1
            else:
                full_pairs[1] += 1
                nf[0] += k; nf[1] += r; nf[2] += k * (n - k + 1) / n

    print(f"h={a.h} p={a.p}: cube {len(cubes)} 本 / support {len(names)} latch "
          f"（|V|={m.n}, T={m.T}）")
    print(f"  cube あたりの指定リテラル数: 中央値 "
          f"{sorted(size_hist.elements())[len(cubes)//2]}, 最大 {max(size_hist)}")
    print(f"  時刻を一意に決めている cube: {n_t_exact}/{len(cubes)} "
          f"({100*n_t_exact/len(cubes):.1f}%)")
    tb_str = ", ".join(f"{k} 本:{v}" for k, v in sorted(tbits_hist.items()))
    print(f"  cube が固定している時刻ビットの本数（全 {tw} 本中）: {tb_str}")
    print(f"  dead を固定している cube: {n_dead}/{len(cubes)} "
          f"({100*n_dead/len(cubes):.1f}%)")
    if t_hist:
        top = ", ".join(f"t={t}:{c}" for t, c in t_hist.most_common(8))
        print(f"    多い時刻: {top}")
        print(f"    出現する時刻の範囲: {min(t_hist)}..{max(t_hist)}"
              f"（地平線 0..{m.T}）")
    lh = ", ".join(f"層{k}:{v}" for k, v in sorted(layer_hist.items()))
    print(f"  節が触れる層（リテラル延べ数）: {lh}")
    print(f"  「居る」と指定された頂点: 延べ {tot_ones} 個 / 連続塊 {obs_runs} 個"
          f" → 1 塊あたり {tot_ones/max(obs_runs,1):.2f} 頂点")
    print(f"    帰無モデル（同じ個数を層内に一様配置）の期待塊数: {exp_runs:.0f}"
          f" → 実測は帰無の {obs_runs/max(exp_runs,1e-9):.2f} 倍")
    print(f"  ⚠ 対抗仮説の点検: 層を**丸ごと**在ると指定した (節,層) 対は "
          f"{full_pairs[0]}/{full_pairs[0]+full_pairs[1]} "
          f"({100*full_pairs[0]/max(sum(full_pairs),1):.1f}%)")
    print(f"    層まるごとを除くと: 居る {nf[0]} / 塊 {nf[1]} → "
          f"1 塊あたり {nf[0]/max(nf[1],1):.2f} 頂点、帰無の "
          f"{nf[1]/max(nf[2],1e-9):.2f} 倍")
    print("  層ごと（塊あたり頂点数。1.00 なら全部バラバラ）:")
    for lvl in sorted(per_layer_runs):
        d = per_layer_runs[lvl]
        k = sum(x[0] for x in d)
        r = sum(x[1] for x in d)
        e = sum(x[0] * (x[2] - x[0] + 1) / x[2] for x in d)
        print(f"    層 {lvl:2d}（幅 {width[lvl]:2d}）: {len(d):6d} 節 / "
              f"居る {k:7d} / 塊 {r:7d} → {k/max(r,1):5.2f}"
              f"（帰無 {k/max(e,1e-9):5.2f}）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
