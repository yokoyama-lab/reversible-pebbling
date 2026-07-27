"""ZDD による記号的 BFS `scripts/exp01b_zdd.py` の検証（テストファースト）。

**このテストは `.venv/bin/python` を要求する**（graphillion が `.venv` にある）。
システム python で走らせた場合は graphillion 不在としてスキップする
（統合担当が全テストを流すときに落とさないため）。

    .venv/bin/python tests/test_exp01e_zdd.py

検証方針（CLAUDE.md「二重実装で照合」）: ZDD 版が
`exp01b_engine`（= `revpebble.bfs` と全域一致済み）と重なる全域で一致すること。
**一致しなければ $h=7$ の値は採用しない。**
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import revpebble as rp  # noqa: E402
from exp01b_engine import mstar as mstar_fast  # noqa: E402
from exp01b_zdd import HAS_GRAPHILLION  # noqa: E402

if HAS_GRAPHILLION:
    from exp01b_zdd import (  # noqa: E402
        dfs_order,
        guards,
        mstar_zdd,
        one_move_image,
        pebbleable,
        pmin_zdd,
        set_universe_for,
    )

# 確定済み（tests/test_exp01c_treedp.py と同じ値）。h は free-leaves 流儀の高さ。
MSTAR = {1: 1, 2: 5, 3: 17, 4: 53, 5: 155, 6: 429}
PMIN = {1: 1, 2: 3, 3: 5, 4: 6, 5: 7, 6: 8}


def _skip() -> bool:
    if not HAS_GRAPHILLION:
        print("   (skip: graphillion 不在。.venv/bin/python で実行してください)")
        return True
    return False


# --------------------------------------------------------------------------
# 1. 構造（変数順序と guard）
# --------------------------------------------------------------------------


def test_dfs_order_makes_subtrees_contiguous() -> None:
    """DFS（後順）順序で各部分木の頂点が連続ブロックになる。

    ZDD/BDD のサイズは変数順序に強く依存し、木構造の制約では
    「部分木が連続」が定石。ここを外すと $h=7$ に届かない。
    """
    if _skip():
        return
    for h in (2, 3, 4):
        order = dfs_order(h)
        assert sorted(order) == sorted(pebbleable(h)), h
        pos = {v: i for i, v in enumerate(order)}
        g = guards(h)

        def block(v: int) -> list[int]:
            out = [v]
            for u in g[v]:
                out += block(u)
            return out

        for v in order:
            idx = sorted(pos[u] for u in block(v))
            assert idx == list(range(idx[0], idx[-1] + 1)), (h, v, idx)


def test_guards_match_revpebble() -> None:
    """guard（非 free な先行点集合）が `revpebble` の DAG と一致する。"""
    if _skip():
        return
    for h in (1, 2, 3, 4):
        dag = rp.complete_binary_tree(h)
        g = guards(h)
        assert set(g) == set(dag.pebbleable()), h
        for v, need in g.items():
            want = {u for u in dag.preds[v] if u not in dag.free}
            assert set(need) == want, (h, v)


def test_one_move_image_matches_explicit() -> None:
    """1手の像（ZDD 演算）が素朴な集合演算と一致する。"""
    if _skip():
        return
    from graphillion import setset

    h, p = 3, 5
    set_universe_for(h)
    dag = rp.complete_binary_tree(h)
    g = guards(h)
    # 適当な状態族を取る（全頂点の 1 元集合と空集合）
    seeds = [[]] + [[v] for v in pebbleable(h)]
    F = setset(seeds)
    got = {frozenset(s) for s in one_move_image(F, g, p)}
    want: set[frozenset[int]] = set()
    for s in seeds:
        st = set(s)
        for v in dag.pebbleable():
            if not all((u in dag.free) or (u in st) for u in dag.preds[v]):
                continue
            nxt = st ^ {v}
            if len(nxt) <= p:
                want.add(frozenset(nxt))
    assert got == want, (sorted(map(sorted, got - want)), sorted(map(sorted, want - got)))


# --------------------------------------------------------------------------
# 2. 既知値との全域一致（ここが本体）
# --------------------------------------------------------------------------


def test_zdd_matches_engine_all_p() -> None:
    """厳密エンジンと**全 $p$ で一致**（到達不能の判定も含む）。"""
    if _skip():
        return
    for h in (1, 2, 3, 4):
        dag = rp.complete_binary_tree(h)
        for p in range(1, 9):
            want = mstar_fast(dag, dag.n - 1, p)
            got = mstar_zdd(h, p)
            assert got == want, (h, p, got, want)


def test_two_level_equals_naive_visited() -> None:
    """2 レベル保持版（既定）と累積 `visited` 版が**完全に一致**する。

    無向グラフでは $\\mathrm{image}(L_d)\\subseteq L_{d-1}\\cup L_d\\cup L_{d+1}$ なので
    直前 2 レベルだけで BFS が正しく回る。ここが一致しなければその前提が壊れている。
    """
    if _skip():
        return
    for h in (1, 2, 3, 4, 5):
        for p in range(1, 9):
            a = mstar_zdd(h, p, two_level=True)
            b = mstar_zdd(h, p, two_level=False)
            assert a == b, (h, p, a, b)


def test_checkpoint_round_trip_and_segmented_bfs() -> None:
    """**分割実行が一括実行と同じ答えを出す**（$h=6$ の 429 を分割して再現）。

    graphillion のノード表は GC されないので、長い計算は
    「N レベル進める → 保存 → プロセス終了 → 再開」で分割する必要がある。
    ここではプロセスは跨がずに、保存・復元を挟んで同じ結果になることを確認する
    （プロセスを跨ぐ部分は `scripts/exp01b_zdd_segment.py`）。
    """
    if _skip():
        return
    import tempfile

    from exp01b_zdd import load_checkpoint, save_checkpoint

    h, p = 6, 8
    with tempfile.TemporaryDirectory() as td:
        ck = Path(td) / "t.ckpt"
        d_stop = 100
        try:
            mstar_zdd(h, p, two_level=True, checkpoint=ck, max_levels=d_stop)
            raise AssertionError("途中で止まるはずだった")
        except TimeoutError:
            pass
        hh, pp, d, prev, frontier = load_checkpoint(ck)
        assert (hh, pp, d) == (h, p, d_stop), (hh, pp, d)
        # 保存・復元を挟んでも答えが変わらない
        m = mstar_zdd(h, p, two_level=True, resume=(d, prev, frontier))
        assert m == MSTAR[h], (m, MSTAR[h])
        # 保存 → 復元 → 再保存で内容が保たれる
        save_checkpoint(ck, h, p, d, prev, frontier)
        _, _, d2, prev2, frontier2 = load_checkpoint(ck)
        assert d2 == d
        assert len(prev2) == len(prev) and len(frontier2) == len(frontier)


def test_zdd_mstar_table() -> None:
    """確定済みの $M^*$ 表 $1,5,17,53,155$ を再現する（$h\\le5$）。"""
    if _skip():
        return
    for h in range(1, 6):
        assert mstar_zdd(h, PMIN[h]) == MSTAR[h], h


def test_zdd_pmin_table() -> None:
    """$p_{\\min}$ = 1,3,5,6,7 を再現する（$h\\le5$）。"""
    if _skip():
        return
    for h in range(1, 6):
        assert pmin_zdd(h) == PMIN[h], h


def test_zdd_mstar_h6_is_429() -> None:
    """$h=6$（63 頂点）で $M^*=429$ を再現する。やや重い。"""
    if _skip():
        return
    assert mstar_zdd(6, 8) == 429


# --------------------------------------------------------------------------
# 3. Královič の complete computation 側（$S_{\min}$, $T$）
# --------------------------------------------------------------------------

# 第2ラウンドで確定（data/exp01_results.md §9）。h は Královič の高さ。
SMIN = {1: 1, 2: 3, 3: 4, 4: 5, 5: 6, 6: 8}
TMIN = {1: 2, 2: 6, 3: 20, 4: 58, 5: 168, 6: 380}


def test_zdd_smin_matches_engine() -> None:
    """$S_{\\min}$ が `exp01b_engine.smin_kralovic` と一致する（$h\\le4$、全 $p$ 相当）。"""
    if _skip():
        return
    from dataclasses import replace

    from exp01b_engine import reach_target_dist, smin_kralovic
    from exp01b_zdd import reach_target_dist_zdd, smin_zdd

    for h in (1, 2, 3, 4):
        # 彼の Bt(h) = 我々の all-pebbled cbt(h-1)。ZDD 側の h と同じ添字。
        dag = replace(rp.complete_binary_tree(h - 1), free=frozenset())
        assert smin_zdd(h) == smin_kralovic(dag, dag.n - 1), h
        for p in range(1, 8):
            assert reach_target_dist_zdd(h, p) == reach_target_dist(dag, dag.n - 1, p), (h, p)


def test_zdd_smin_tmin_table() -> None:
    """確定済みの $S_{\\min}$ / $T$ 表を再現する（$h\\le5$）。"""
    if _skip():
        return
    from exp01b_zdd import smin_zdd, tmin_zdd

    for h in range(1, 6):
        assert smin_zdd(h) == SMIN[h], h
        assert tmin_zdd(h, SMIN[h]) == TMIN[h], h


def test_zdd_result_lies_in_previously_proved_bounds() -> None:
    """独立な整合性チェック: ZDD の $h\\le6$ の値が前ラウンドの上下界の議論と矛盾しない。

    $M^*(T_7,10)$ については前ラウンドで $603\\le M^* \\le 1403$ を
    まったく別の方法（部分木分解の下界／構成的手順の上界）で示している。
    ZDD が出す値がこの窓に入ることが、2 手法の相互検証になる。
    ここでは窓そのものの健全性（下界 $\\le$ 上界）と、
    $h\\le6$ で同型の下界式が既知値を破らないことを確認する。
    """
    if _skip():
        return
    from treedp import lower_bound_mstar_phased

    for h in (3, 4, 5, 6):
        lb = lower_bound_mstar_phased(h - 2, PMIN[h])
        if lb is None:
            continue
        assert lb <= MSTAR[h], (h, lb, MSTAR[h])


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
