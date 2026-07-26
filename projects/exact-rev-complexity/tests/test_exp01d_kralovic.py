"""Královič 2004 の量（$S_{\\min}$, $T$）の実装が**彼の定理を再現するか**の検証。

これは単なる回帰テストではなく、**我々のモデルの読みが正しいかの検証**である。
`docs/20_prior_art.md` は我々の clean-reach 流儀の $\\mathrm{reach}(p)=2^{p-1}$ を
「Královič Thm 3.1（$S^{-1}(p)=2^p-1$）の系」と書いていたが、
2 つの量は終端条件が違う（`scripts/exp01b_engine.py` の該当節を参照）。

**ここで彼の Thm 3.1 を彼の流儀で再現できれば、読みが正しいと確認できる。**
できなければ、モデルの解釈が間違っている。

出典（本文精読・2026-07-27）:
  R. Královič, "Time and space complexity of reversible pebbling",
  RAIRO-Inf. Theor. Appl. 38(2):137–161, 2004, doi:10.1051/ita:2004008.
  - §2: R1/R2 と complete computation の定義（p.139）
  - Thm 3.1: $S^{-1}(p)=2^p-1$（p.142）
  - Thm 4.9: $S_{\\min}(h)=h+\\Theta(\\lg^* h)$（p.153）
  - Thm 4.12: バタフライも $d+\\Theta(\\lg^* d)$（p.155）
  - Lem 4.10/4.11: $S(Bf(d))=S(Bt(d))$（p.154）

実行: python3 tests/test_exp01d_kralovic.py
"""

from __future__ import annotations

import sys
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import revpebble as rp  # noqa: E402
from exp01b_engine import (  # noqa: E402
    all_pebbled,
    butterfly,
    mstar,
    pmin,
    reach_target_dist,
    smin_kralovic,
    tmin_kralovic,
)


def lg_star(x: float) -> int:
    """彼の Thm 4.9 の定義そのまま: $\\lg^*(x)=0$ for $x\\le0$、さもなくば $1+\\lg^*(\\lg x)$。

    注意: よく使われる「$\\lg^*$ を $\\le1$ になるまでの回数」とは **1 ずれる**
    （彼の定義では $\\lg^*(1)=1$、一般的な定義では 0）。比較するときは必ず揃える。
    """
    from math import log2

    n = 0
    while x > 0:
        x = log2(x)
        n += 1
    return n


# --------------------------------------------------------------------------
# 1. 彼の Thm 3.1 の再現 —— モデルの読みが正しいことの検証
# --------------------------------------------------------------------------


def test_prior_project_complete_computation_times() -> None:
    """先行プロジェクトの「完全計算変種の厳密時間」$T(2^p-1,p) = 2,8,26,76,218$ を再現。

    `docs/20_prior_art.md` §2 に記録された値。これが Královič の
    **complete computation** の時間であることの確認になる（独立実装での再現）。
    """
    want = [2, 8, 26, 76, 218]
    got = [tmin_kralovic(rp.chain(2**p - 1), 2**p - 1, p) for p in range(1, 6)]
    assert got == want, got


def test_kralovic_thm34_recurrence_inequality() -> None:
    """**Thm 3.4: $T(S^{-1}(p{+}1),p{+}1) \\ge 2S^{-1}(p)+2+2T(S^{-1}(p),p)$。**

    彼が与えたのは**この不等式だけ**（厳密値の表は無い）。実測値が満たすか確認する。
    """
    for p in range(1, 5):
        lhs = tmin_kralovic(rp.chain(2 ** (p + 1) - 1), 2 ** (p + 1) - 1, p + 1)
        rhs_t = tmin_kralovic(rp.chain(2**p - 1), 2**p - 1, p)
        assert lhs is not None and rhs_t is not None, p
        assert lhs >= 2 * (2**p - 1) + 2 + 2 * rhs_t, (p, lhs, rhs_t)


def test_kralovic_thm31_chain_smin_inverse() -> None:
    """**Thm 3.1: $S^{-1}(p)=2^p-1$。** 彼の流儀で再現できるか。

    $S^{-1}(p)$ = ピーク $p$ で complete computation ができる最大の鎖長。
    我々の `chain(n)` のペブル対象部分は彼の $Ch(n)$ と同型（free な源は空間に数えない）。
    """
    for p in range(1, 6):
        best = 0
        for n in range(1, 2 ** (p + 1) + 2):
            g = rp.chain(n)
            if reach_target_dist(g, n, p) is not None:
                best = n
            else:
                break
        assert best == 2**p - 1, f"p={p}: 得た {best}, 期待 {2**p - 1}"


def test_our_reach_relates_to_his_by_index_shift() -> None:
    """我々の $\\mathrm{reach}(p)=2^{p-1}$ と彼の $S^{-1}(p)=2^p-1$ の**正確な関係**。

    2 つは同じ量ではない（$2^{p-1} \\ne 2^p-1$）。成り立つのは**添字をずらした等式**

    $$\\mathrm{reach}(p) \\;=\\; S^{-1}(p-1) + 1 .$$

    直観: clean 到達では最後のペブルが終端に居座るので、残り $p-1$ 本で
    長さ $\\mathrm{reach}(p)-1$ の前半を complete computation として畳む必要がある。

    → `docs/20_prior_art.md` の「$S^{-1}(p)=2^p-1$ の系」は添字のずれを飛ばしていて
    そのままでは正確でない。上の形なら正しい。
    """
    for p in range(2, 7):
        ours = 0
        for n in range(1, 2 ** (p + 1) + 2):
            if mstar(rp.chain(n), n, p) is not None:
                ours = n
            else:
                break
        assert ours == 2 ** (p - 1), (p, ours)
        assert ours != 2**p - 1, f"p={p}: 2 つの量が一致してしまった"
        assert ours == (2 ** (p - 1) - 1) + 1, (p, ours)  # = S^{-1}(p-1)+1


def test_kralovic_lemma42_smin_vs_semicomplete() -> None:
    """**Lem 4.2: $S_{\\min}(h) \\le S'_{\\min}(h) \\le S_{\\min}(h)+1$。**

    $S'_{\\min}$ = 我々の $p_{\\min}$（Def 4.1 = clean-reach）。
    彼の $Bt(h)$ は $2^h-1$ 頂点なので、我々の `all_pebbled(complete_binary_tree(h-1))`。
    """
    for h in range(1, 5):
        g = all_pebbled(rp.complete_binary_tree(h - 1))
        t = g.n - 1
        s = smin_kralovic(g, t)
        sp = pmin(g, t)  # = S'_min(h)
        assert s is not None and sp is not None, h
        assert s <= sp <= s + 1, f"h={h}: S_min={s}, S'_min={sp}"


def test_kralovic_lemma43_exact_recurrence() -> None:
    """**Lem 4.3: $S'_{\\min}(h+1) = S_{\\min}(h) + 2$（厳密な漸化式）。**

    我々の測定値がこれを満たすことは、モデルの読みと数値の両方の検証になる。
    """
    for h in range(1, 5):
        g_h = all_pebbled(rp.complete_binary_tree(h - 1))
        g_h1 = all_pebbled(rp.complete_binary_tree(h))
        s = smin_kralovic(g_h, g_h.n - 1)
        sp1 = pmin(g_h1, g_h1.n - 1)  # = S'_min(h+1)
        assert s is not None and sp1 is not None, h
        assert sp1 == s + 2, f"h={h}: S'_min({h+1})={sp1}, S_min({h})+2={s+2}"


def test_kralovic_lemma43_predicts_our_new_pmin_t7() -> None:
    """Lem 4.3 は我々が新規確定した $p_{\\min}(T_7)=10$ を**正しく予測する**。

    $S_{\\min}(Bt(6))=8$（本作業で測定）$\\Rightarrow S'_{\\min}(Bt(7))=10$。
    我々は商グラフの全数探索（下界）＋構成的証書（上界）で独立に 10 を得た。
    値は `tests/test_exp01c_treedp.py` に固定してある。
    """
    from treedp import smin_tree

    assert smin_tree(5) == 8  # S_min(Bt(6))。m=5 が彼の h=6
    assert 8 + 2 == 10  # Lem 4.3 の予測
    # 我々の独立測定（p_min(Bt(7)) = pmin_tree(6) = 10）は
    # tests/test_exp01c_treedp.py::KNOWN_PMIN と data/exp01b_certificate.md に固定。


def test_smin_at_most_pmin() -> None:
    """彼の $S_{\\min}$ は我々の $p_{\\min}$ 以下（終端条件が易しいので）。"""
    graphs = (
        [rp.chain(n) for n in range(1, 12)]
        + [all_pebbled(rp.complete_binary_tree(h)) for h in (1, 2, 3)]
        + [all_pebbled(rp.pyramid(h)) for h in (1, 2, 3, 4)]
        + [rp.pyramid(h) for h in (1, 2, 3, 4, 5)]
    )
    for g in graphs:
        t = g.n - 1
        s = smin_kralovic(g, t)
        q = pmin(g, t)
        assert s is not None and q is not None, g.name
        assert s <= q, (g.name, s, q)


def test_reach_target_dist_at_most_mstar() -> None:
    """片道の最小手数 $\\le M^*$（clean にする分だけ余計にかかる）。"""
    for g in (rp.chain(8), all_pebbled(rp.pyramid(3)), rp.complete_binary_tree(3)):
        t = g.n - 1
        for p in range(1, 9):
            a = reach_target_dist(g, t, p)
            b = mstar(g, t, p)
            if b is None:
                continue
            assert a is not None and a <= b, (g.name, p, a, b)


def test_tmin_is_twice_one_way() -> None:
    """彼の $T(G,s)$ が片道の 2 倍として定義できている（状態グラフが無向だから）。"""
    g = all_pebbled(rp.pyramid(3))
    t = g.n - 1
    for p in range(1, 9):
        d = reach_target_dist(g, t, p)
        assert tmin_kralovic(g, t, p) == (None if d is None else 2 * d), p


# --------------------------------------------------------------------------
# 2. 彼の Bt(h) = 我々の all-pebbled 完全二分木
# --------------------------------------------------------------------------


def test_his_bt_is_our_all_pebbled_tree() -> None:
    """彼の $Bt(h)$ は葉も空間に数える流儀。標準ペブリング空間 $h+1$ で確認する。

    彼は「標準ペブル空間は $h+1$」を引用している（[7]）。
    我々の all-pebbled 流儀の完全二分木がその形。
    （ここでは可逆側の $S_{\\min}\\ge h+1$ だけを確かめる。標準ペブリングは候補2 の担当。）
    """
    for h in (1, 2, 3):
        g = all_pebbled(rp.complete_binary_tree(h))
        s = smin_kralovic(g, g.n - 1)
        assert s is not None and s >= h + 1, (h, s)


def test_butterfly_output_cone_is_a_complete_binary_tree() -> None:
    """バタフライの 1 出力の**祖先錐は先行点で閉じた完全二分木**（$2^{k+1}-1$ 頂点）。

    これが Lem 4.10/4.11 の計算的な根拠になる。
    """
    for k in (1, 2, 3):
        g = butterfly(k)
        t = g.n - 1
        cone = {t}
        stack = [t]
        while stack:
            v = stack.pop()
            for u in g.preds[v]:
                if u not in cone:
                    cone.add(u)
                    stack.append(u)
        assert len(cone) == 2 ** (k + 1) - 1, (k, len(cone))
        # 錐は先行点で閉じている（= 誘導部分グラフで入次数が保たれる）
        for v in cone:
            assert all(u in cone for u in g.preds[v]), (k, v)


def test_kralovic_thm412_butterfly_equals_tree_space() -> None:
    """**Lem 4.10/4.11: $S(Bf(d)) = S(Bt(d))$。**

    彼の $Bf(d)$ は $V=\\{1..d\\}\\times\\{0..2^{d-1}-1\\}$、我々の `butterfly(k)` は
    $k+1$ 段 $\\times 2^k$ なので $d=k+1$ で対応する。

    彼の complete computation は「**全頂点**が一度カバーされる」だが、
    (i) どの頂点も何らかの出力の祖先で、(ii) 各出力の祖先錐は先行点で閉じた完全二分木
    （上のテスト）なので

        「全頂点がカバーされる」 ⟺ 「各出力が（同時でなく順番にでも）カバーされる」

    順番にやれば peak は 1 つの錐の値 = $S(Bt(k))$。Lem 4.10（制限）が逆向きを与える。
    よって 1 出力を target にした計算で $S(Bf)$ が求まる。
    """
    for k in (1, 2, 3):
        bf = all_pebbled(butterfly(k))
        bt = all_pebbled(rp.complete_binary_tree(k))
        sb = smin_kralovic(bf, bf.n - 1)
        st = smin_kralovic(bt, bt.n - 1)
        assert sb == st, (k, sb, st)


def test_lg_star_helper() -> None:
    """lg* の実装（彼の Thm 4.9 の定義に合わせる）。"""
    assert lg_star(1) == 1
    assert lg_star(2) == 2
    assert lg_star(4) == 3
    assert lg_star(16) == 4
    assert lg_star(65536) == 5
    # 彼の h=1..7 での値
    assert [lg_star(h) for h in range(1, 8)] == [1, 2, 3, 3, 4, 4, 4]


def test_excess_is_not_equal_to_lg_star() -> None:
    """実測の超過分 $S'_{\\min}(h)-h$ は $\\lg^*h$ と**一致しない**（$\\Theta$ なので矛盾ではない）。

    実測 $S'_{\\min}(h)-h = 0,1,2,2,2,2,3$（$h=1..7$）に対し
    $\\lg^*h-1 = 0,1,2,2,3,3,3$。$h=5,6$ で 1 ずれる（実測のほうが小さい）。
    → **段差の位置は彼の定理からは決まらない。** 我々の厳密値が新情報である。
    """
    measured = [0, 1, 2, 2, 2, 2, 3]  # tests/test_exp01c_treedp.py::KNOWN_PMIN より
    shifted = [lg_star(h) - 1 for h in range(1, 8)]
    assert shifted == [0, 1, 2, 2, 3, 3, 3], shifted
    assert measured != shifted
    assert measured[:4] == shifted[:4]  # h<=4 では一致
    assert measured[4] < shifted[4] and measured[5] < shifted[5]  # h=5,6 で実測が小さい


def test_kralovic_thm49_tower_bounds_are_satisfied_but_vacuous() -> None:
    """**Thm 4.9 の証明が与える界は、我々の域では実質何も言わない。**

    証明中: $S'^{-1}_{\\min}(p) \\le \\underbrace{8^{8^{\\cdots}}}_{p}$ かつ
    $S'^{-1}_{\\min}(p) \\ge \\underbrace{2^{2^{\\cdots}}}_{p-2}$。

    $S'^{-1}_{\\min}(p)$ = 超過分がちょうど $p$ になる最大の $h$。
    実測では $S'^{-1}_{\\min}(0)=1,\\ S'^{-1}_{\\min}(1)=2,\\ S'^{-1}_{\\min}(2)=6$。
    $p=2$ の上界は $8^8 = 16777216$ で、真値 6 との差は 7 桁。
    """

    def tower(base: int, height: int) -> int:
        v = 1
        for _ in range(height):
            v = base**v
        return v

    measured_inv = {0: 1, 1: 2, 2: 6}  # 超過分 p を取る最大の h（実測 h<=7 の範囲）
    for p, h in measured_inv.items():
        assert h <= tower(8, p) or p == 0, (p, h)
        assert h >= tower(2, max(p - 2, 0)), (p, h)
    # 上界が実質無意味であることを数値で示す
    assert tower(8, 2) == 16777216
    assert measured_inv[2] * 1000 < tower(8, 2)


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn()
                print(f"ok   {name}")
            except AssertionError as exc:
                failures += 1
                print(f"FAIL {name}: {exc}")
    sys.exit(1 if failures else 0)
