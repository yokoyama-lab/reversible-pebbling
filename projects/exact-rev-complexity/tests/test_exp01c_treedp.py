"""完全二分木の Aut 商グラフ探索 `scripts/treedp.py` の回帰テスト（テストファースト）。

`treedp.py` は状態を「兄弟入れ替えの下での同型類（shape）」に潰して BFS する。
$\\varnothing$ と目標状態 $\\{root\\}$ はどちらも Aut 不変なので、商グラフ上の最短距離は
元のグラフ上の最短距離に**厳密に等しい**（標準的な事実）。

ここでは `exp01b_engine`（= `revpebble.bfs` と全域一致済み）と重なる範囲で
完全一致することを確認する。一致しない範囲の数値は使わない。

実行: python3 tests/test_exp01c_treedp.py
"""

from __future__ import annotations

import sys
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import revpebble as rp  # noqa: E402
from exp01b_engine import mstar as mstar_fast  # noqa: E402
from exp01b_engine import verify_schedule  # noqa: E402
from treedp import (  # noqa: E402
    QuotientTree,
    compose_schedule,
    invert,
    level_index,
    lift,
    mstar_tree,
    pmin_tree,
    realize_optimal,
)

# free-leaves 流儀 cbt(h) の M*（p = p_min。= all-pebbled 流儀 cbt(h-1)）。
# h=2,3,4 は exp01 初回測定、h=5（155）は exp01b の厳密 BFS、
# h=6（429）は本モジュールの商グラフ探索で新規確定（2026-07-27）。
MSTAR_CBT_FREE_LEAVES = {1: 1, 2: 5, 3: 17, 4: 53, 5: 155, 6: 429}

# トレードオフ曲線 M*(cbt(h) free-leaves, p)。h -> {p: M*}
TRADEOFF = {
    3: {5: 17, 6: 15, 7: 13},
    4: {6: 53, 7: 45, 8: 43},
    5: {7: 155, 8: 115, 9: 105},
    6: {8: 429, 9: 339, 10: 295},
}


def test_shape_counts_match_orbit_formula() -> None:
    """shape の数え上げが独立な軌道数の公式と一致する。"""
    from math import comb

    def orbit_counts(hmax: int, kmax: int) -> list[list[int]]:
        f = [[0] * (kmax + 1) for _ in range(hmax + 1)]
        f[0][0] = f[0][1] = 1
        for h in range(1, hmax + 1):
            g = f[h - 1]
            for k in range(kmax + 1):
                tot = 0
                for b in (0, 1):
                    r = k - b
                    if r < 0:
                        continue
                    for i in range(r // 2 + 1):
                        j = r - i
                        if j > kmax:
                            continue
                        tot += g[i] * g[j] if i < j else g[i] * (g[i] + 1) // 2
                f[h][k] = tot
        return f

    f = orbit_counts(3, 8)
    # 高さ 2 の木（7 頂点）の 2-部分集合の軌道数は手で数えられる
    assert f[2][0] == 1
    assert f[2][1] == 3  # 根 / 中段 / 葉
    assert sum(f[2][k] for k in range(8)) <= comb(7, 7) * 2**7

    qt = QuotientTree(2)
    got = qt.count_shapes(kmax=3)
    assert got == [f[2][k] for k in range(4)], (got, [f[2][k] for k in range(4)])


def test_neighbors_are_symmetric() -> None:
    """shape 間の隣接関係は対称（トグルは対合）。双方向 BFS の前提。"""
    qt = QuotientTree(3)
    seen = {qt.empty_id()}
    frontier = [qt.empty_id()]
    for _ in range(4):
        nxt = []
        for s in frontier:
            for t in qt.neighbors(qt.m, s):
                assert s in qt.neighbors(qt.m, t), (s, t)
                if t not in seen:
                    seen.add(t)
                    nxt.append(t)
        frontier = nxt


def test_matches_exact_engine_all_p() -> None:
    """厳密エンジンと全 p で一致（到達不能の判定も含む）。m = h-1。"""
    for h in (1, 2, 3, 4):
        g = rp.complete_binary_tree(h)
        for p in range(1, 10):
            want = mstar_fast(g, g.n - 1, p)
            got = mstar_tree(h - 1, p)
            assert got == want, (h, p, got, want)


def test_matches_all_pebbled_normalization() -> None:
    """all-pebbled 流儀 cbt(h)* とも一致（レベルずれ 1）。"""
    for h in (1, 2, 3):
        g = replace(rp.complete_binary_tree(h), free=frozenset())
        for p in range(1, 9):
            assert mstar_tree(h, p) == mstar_fast(g, g.n - 1, p), (h, p)


def test_known_mstar_table() -> None:
    """確定済みの M* 表を再現する（回帰用に固定）。"""
    for h, want in MSTAR_CBT_FREE_LEAVES.items():
        p = pmin_tree(h - 1)
        assert p is not None
        assert mstar_tree(h - 1, p) == want, (h, mstar_tree(h - 1, p), want)


def test_pmin_table() -> None:
    """p_min(cbt(h) free-leaves) = 1,3,5,6,7,8（h=1..6）。

    → 超過 $p_{\\min}-h$ = 0,1,2,2,2,2。Královič の $h+\\Theta(\\lg^* h)$ の
    段差は $h=3$ 以降 $h=6$ までは起きていない。
    """
    assert [pmin_tree(m) for m in range(0, 6)] == [1, 3, 5, 6, 7, 8]


def test_tradeoff_curve() -> None:
    """トレードオフ曲線の厳密値（回帰用に固定）。"""
    for h, row in TRADEOFF.items():
        for p, want in row.items():
            assert mstar_tree(h - 1, p) == want, (h, p, mstar_tree(h - 1, p), want)


def test_mstar_is_nonincreasing_in_p() -> None:
    """$M^*(G,p)$ は p について単調非増加（ペブルを増やして損はしない）。"""
    for m in range(0, 5):
        p0 = pmin_tree(m)
        assert p0 is not None
        vals = [mstar_tree(m, p) for p in range(p0, p0 + 4)]
        assert all(a is not None and b is not None and a >= b for a, b in zip(vals, vals[1:])), (
            m,
            vals,
        )


def test_conjecture_two_times_three_to_the_h_refuted() -> None:
    """`data/exp01_findings.md` §3 の予想 $M^*(T_h)=2\\cdot3^h-1$ は偽。

    3点（5,17,53）では成立するが、4点目 155 ≠ 161 で崩れる。
    """
    seq = [MSTAR_CBT_FREE_LEAVES[h] for h in (2, 3, 4, 5, 6)]
    assert seq[:3] == [2 * 3**k - 1 for k in (1, 2, 3)], seq
    assert seq[3] != 2 * 3**4 - 1, "155 == 161 のはずがない"
    assert seq[3] == 155 and seq[4] == 429


# --------------------------------------------------------------------------
# 手順の復元と逐次合成の証書
# --------------------------------------------------------------------------


def test_level_index_roundtrip() -> None:
    """頂点番号 ⟷ (レベル, 位置) の対応が `complete_binary_tree` と整合する。"""
    for h in (1, 2, 3, 4):
        g = rp.complete_binary_tree(h)
        assert level_index(h, g.n - 1) == (h, 0), h  # 根は最上レベルの 0 番
        for v in range(g.n):
            d, j = level_index(h, v)
            assert 0 <= j < 2 ** (h - d)
        # レベル 0 が葉（free）
        assert all(level_index(h, v)[0] == 0 for v in g.free)


def test_realize_optimal_is_valid_and_optimal() -> None:
    """商グラフから復元した手順が規則を満たし、長さが M* に一致する。"""
    for h in (2, 3, 4, 5):
        p = pmin_tree(h - 1)
        assert p is not None
        seq = realize_optimal(h, p)
        assert seq is not None
        g = rp.complete_binary_tree(h)
        verify_schedule(g, g.n - 1, p, seq)  # 独立な検証器
        assert len(seq) == mstar_tree(h - 1, p), (h, len(seq))


def test_invert_returns_to_empty() -> None:
    """invert が clean に戻す手順になっている。"""
    h = 3
    p = pmin_tree(h - 1)
    assert p is not None
    seq = realize_optimal(h, p)
    assert seq is not None
    state: set[int] = set()
    for kind, v in seq + invert(seq):
        state.symmetric_difference_update({v})
    assert state == set()


def test_lift_maps_into_correct_subtree() -> None:
    """lift が親の木の左／右部分木へ正しく写る（先行点関係を保つ）。"""
    h = 4
    gp = rp.complete_binary_tree(h)
    gc = rp.complete_binary_tree(h - 1)
    for right in (False, True):
        seq = [("put", v) for v in range(gc.n)]
        moved = [v for _, v in lift(h, seq, right=right)]
        assert len(set(moved)) == gc.n
        # 子で先行点だったペアが、写した先でも先行点になっている
        for v in range(gc.n):
            for u in gc.preds[v]:
                assert moved[u] in gp.preds[moved[v]], (right, u, v)


def test_compose_schedule_certifies_pmin_bound() -> None:
    """逐次合成が $p_{\\min}(T_h) \\le p_{\\min}(T_{h-1})+2$ の証書になる。

    生成した手順を独立な検証器にかけ、ピーク $q+2$ で clean 到達することを確認する。
    """
    for h in (3, 4, 5):
        q = pmin_tree(h - 2)
        assert q is not None
        sub = realize_optimal(h - 1, q)
        assert sub is not None
        seq = compose_schedule(h, sub)
        g = rp.complete_binary_tree(h)
        verify_schedule(g, g.n - 1, q + 2, seq)  # ピーク q+2 で通ること
        assert len(seq) == 4 * len(sub) + 1
        # 合成は上界にすぎない（h>=4 では真に最適でない）
        p0 = pmin_tree(h - 1)
        assert p0 is not None and p0 <= q + 2


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
