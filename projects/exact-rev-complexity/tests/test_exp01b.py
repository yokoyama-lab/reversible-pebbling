"""候補1 の高速エンジン `scripts/exp01b_engine.py` の回帰テスト（テストファースト）。

方針（CLAUDE.md「二重実装で照合」）:
  1. 既知の厳密値（先行プロジェクトの鎖の表、exp01 の初回測定）を再現すること。
  2. 素朴実装 `revpebble.bfs`（frozenset 版）と**重なる全域で完全一致**すること。
     一致しない範囲の数値は使わない。

実行: python3 tests/test_exp01b.py
"""

from __future__ import annotations

import sys
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import revpebble as rp  # noqa: E402
from exp01b_engine import (  # noqa: E402
    butterfly,
    compile_dag,
    mstar,
    mstar_pmin,
    pmin,
    schedule,
    mstar_mask,
    pmin_mask,
    schedule_mask,
    spinal_tree,
    verify_schedule,
    verify_schedule_mask,
)

MSTAR_CHAIN = [1, 3, 5, 9, 11, 15, 19, 25, 25, 29, 33, 39, 45, 53]


def all_pebbled(g: rp.Dag) -> rp.Dag:
    """free を空にした版（exp01 の "all-pebbled" 流儀）。"""
    return replace(g, free=frozenset(), name=f"{g.name} all-pebbled")


# --------------------------------------------------------------------------
# 1. 既知値の再現
# --------------------------------------------------------------------------


def test_chain_table() -> None:
    got = [mstar_pmin(rp.chain(n), n)[1] for n in range(1, len(MSTAR_CHAIN) + 1)]
    assert got == MSTAR_CHAIN, got


def test_chain_pmin() -> None:
    for n in range(1, 33):
        assert pmin(rp.chain(n), n) == 1 + (n - 1).bit_length(), n


def test_cbt_known() -> None:
    """exp01 初回測定（free-leaves 流儀）: h=2 -> (3,5), h=3 -> (5,17)。"""
    for h, want in {2: (3, 5), 3: (5, 17)}.items():
        g = rp.complete_binary_tree(h)
        assert mstar_pmin(g, g.n - 1) == want, h


def test_pyr_known() -> None:
    """exp01 初回測定（free-base 流儀）: h=3 -> (5,13), h=4 -> (6,27), h=5 -> (7,47)。"""
    for h, want in {3: (5, 13), 4: (6, 27), 5: (7, 47)}.items():
        g = rp.pyramid(h)
        assert mstar_pmin(g, g.n - 1) == want, h


def test_normalization_level_shift() -> None:
    """`X(h) all-pebbled` == `X(h+1) free-*`（exp01_findings §2 の再確認）。"""
    for h in range(1, 4):
        a = all_pebbled(rp.complete_binary_tree(h))
        b = rp.complete_binary_tree(h + 1)
        assert mstar_pmin(a, a.n - 1) == mstar_pmin(b, b.n - 1), ("cbt", h)
    for h in range(1, 5):
        a = all_pebbled(rp.pyramid(h))
        b = rp.pyramid(h + 1)
        assert mstar_pmin(a, a.n - 1) == mstar_pmin(b, b.n - 1), ("pyr", h)


# --------------------------------------------------------------------------
# 2. 素朴実装との完全一致（重なる域）
# --------------------------------------------------------------------------


def test_agrees_with_naive_bfs() -> None:
    """revpebble.bfs と全 p で一致すること（到達不能の判定も含む）。"""
    graphs = (
        [rp.chain(n) for n in range(1, 10)]
        + [rp.complete_binary_tree(h) for h in (1, 2, 3)]
        + [all_pebbled(rp.complete_binary_tree(h)) for h in (1, 2, 3)]
        + [rp.pyramid(h) for h in (1, 2, 3, 4)]
        + [all_pebbled(rp.pyramid(h)) for h in (1, 2, 3)]
        + [spinal_tree(k) for k in (1, 2, 3, 4)]
        + [butterfly(1), butterfly(2)]
    )
    for g in graphs:
        t = g.n - 1
        for p in range(1, len(g.pebbleable()) + 2):
            want, _ = rp.bfs(g, t, p)
            got = mstar(g, t, p)
            assert got == want, (g.name, p, got, want)


def test_non_root_targets_agree() -> None:
    """終端が根以外でも一致する（部分木の合成検証に使うため）。"""
    g = all_pebbled(rp.pyramid(3))
    for t in g.pebbleable():
        for p in range(1, 8):
            assert mstar(g, t, p) == rp.bfs(g, t, p)[0], (t, p)


# --------------------------------------------------------------------------
# 3. スケジュール抽出
# --------------------------------------------------------------------------


def test_schedule_valid_and_optimal() -> None:
    for g in (rp.chain(6), all_pebbled(rp.pyramid(3)), rp.complete_binary_tree(3)):
        t = g.n - 1
        p, m = mstar_pmin(g, t)
        seq = schedule(g, t, p)
        assert seq is not None and len(seq) == m, (g.name, len(seq), m)
        verify_schedule(g, t, p, seq)  # 規則違反があれば AssertionError


def test_verify_schedule_rejects_bad() -> None:
    g = rp.chain(3)
    bad = [("put", 2)]  # 先行点 1 が未ペブル
    try:
        verify_schedule(g, 3, 3, bad)
    except AssertionError:
        return
    raise AssertionError("不正なスケジュールを検出できていない")


# --------------------------------------------------------------------------
# 4. 新しいグラフ族の構成
# --------------------------------------------------------------------------


def test_spinal_tree_shape() -> None:
    """spinal tree S_k: 長さ k の背骨の各節点に葉が1枚ぶら下がる。頂点数 2k+1。"""
    g = spinal_tree(3)
    assert g.n == 7, g.n
    t = g.n - 1
    assert compile_dag(g).n_move == len(g.pebbleable())
    assert mstar(g, t, 10) is not None


def test_butterfly_shape() -> None:
    """バタフライ BF_k: k+1 段 × 2^k 頂点、各頂点の入次数 2（段 0 以外）。"""
    for k in (1, 2, 3):
        g = butterfly(k)
        assert g.n == (k + 1) * 2**k, (k, g.n)
        for v in range(2**k, g.n):
            assert len(g.preds[v]) == 2, (k, v)


# --------------------------------------------------------------------------
# 5. 複数終端（マスク版）— バタフライの「全出力」用
# --------------------------------------------------------------------------


def test_mask_single_vertex_matches_scalar() -> None:
    """マスク版が単一終端版の一般化になっている。"""
    g = all_pebbled(rp.pyramid(3))
    for t in g.pebbleable():
        for p in range(1, 8):
            assert mstar_mask(g, 1 << t, p) == mstar(g, t, p), (t, p)


def test_mask_free_vertices_are_ignored() -> None:
    """free 頂点だけを終端に指定したら 0 手。"""
    g = rp.chain(4)
    assert mstar_mask(g, 1 << 0, 3) == 0


def test_mask_schedule_valid() -> None:
    """複数終端のスケジュールが規則を満たし、長さが最小手数に一致する。"""
    g = butterfly(2)
    goal = 0
    for j in range(4):  # 最終段の全頂点
        goal |= 1 << (2 * 4 + j)
    p = pmin_mask(g, goal)
    assert p is not None
    m = mstar_mask(g, goal, p)
    seq = schedule_mask(g, goal, p)
    assert seq is not None and len(seq) == m
    verify_schedule_mask(g, goal, p, seq)


def test_spinal_tree_equals_chain() -> None:
    """free-leaves 流儀の spinal tree は鎖と厳密に同じ（側枝の葉は制約にならない）。"""
    for k in range(1, 9):
        s = spinal_tree(k)
        c = rp.chain(k)
        for p in range(1, k + 3):
            assert mstar(s, s.n - 1, p) == mstar(c, k, p), (k, p)


# all-pebbled 流儀の spinal tree（潰れない設定）。k=1..16、p = p_min。
MSTAR_SPINAL_STAR = [5, 11, 19, 25, 35, 45, 61, 57, 71, 85, 101, 119, 137, 155, 179, 153]


def test_spinal_star_pmin_is_floor_log2_plus_3() -> None:
    """$p_{\\min}(S_k^*) = \\lfloor\\log_2 k\\rfloor + 3$（$k\\le12$。段差はちょうど 2 の冪）。

    段差位置が事前に予測できるので、飽和指標 $\\sigma$ の検証台になる
    （`data/exp01_results.md` §3.3）。
    """
    for k in range(1, 13):
        g = all_pebbled(spinal_tree(k))
        assert pmin(g, g.n - 1) == (k.bit_length() - 1) + 3, k


def test_spinal_star_mstar_table() -> None:
    """$M^*(S_k^*)$ の表（回帰用に固定）。$k=8,16$ で**減る**ことに注意。"""
    for k in range(1, 13):
        g = all_pebbled(spinal_tree(k))
        p, m = mstar_pmin(g, g.n - 1)
        assert m == MSTAR_SPINAL_STAR[k - 1], (k, m, MSTAR_SPINAL_STAR[k - 1])


def test_mstar_nonmonotone_across_pmin_step() -> None:
    """$p_{\\min}$ の段差をまたぐと $M^*(p_{\\min})$ は**減りうる**。

    これが `data/exp01_findings.md` §4 の「当てはめ崩壊」の正体
    （$M^*(G,p_{\\min})$ は族の大きさについて単調でさえない）。
    """
    assert MSTAR_SPINAL_STAR[6] == 61 and MSTAR_SPINAL_STAR[7] == 57  # k=7 -> 8
    assert MSTAR_SPINAL_STAR[14] == 179 and MSTAR_SPINAL_STAR[15] == 153  # k=15 -> 16


def test_butterfly_single_output_equals_cbt() -> None:
    """単一出力のバタフライは完全二分木と厳密に一致（出力の錐が木になる）。

    → バタフライで新しい情報を得るには終端を「全出力」にする必要がある。
    """
    for k in (1, 2, 3):
        b = butterfly(k)
        t = b.n - 1
        c = rp.complete_binary_tree(k)
        for p in range(1, k + 4):
            assert mstar(b, t, p) == mstar(c, c.n - 1, p), (k, p)


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
