"""新しいグラフ族 `scripts/families.py` の回帰テスト（テストファースト）。

方針（CLAUDE.md「二重実装で照合」）:
  1. **構造の不変量**（頂点数・free・先行点の個数・トポロジカル順）を固定する。
  2. **既存の族との一致**を固定する。新しい族はパラメタの端で既知の族に退化するので、
     そこで既に検証済みの厳密値（鎖・ピラミッド・完全二分木）と一致しなければならない。
     これが「新しい族の定義が正しい」ことの一次証拠になる。
  3. 素朴実装 `revpebble.bfs` と高速実装 `exp01b_engine.mstar` が**重なる全域で一致**すること。

厳密値そのもの（トーラス的な巻きが効く $k\\le h$ の領域）は、この時点では**書かない**。
2 実装で出してから `data/families/atlas.csv` に載せ、`test_families_atlas.py` で固定する。
（`docs/00_overview.md` §2.1「少数点の当てはめは崩壊する」— 先に数を書かない。）

実行: python3 tests/test_families.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import revpebble as rp  # noqa: E402
import exp01b_engine as fast  # noqa: E402
from families import (  # noqa: E402
    FAMILIES,
    anc,
    bitrev,
    cylinder,
    game_signature,
    kary_tree,
    top_of,
)


# ---------------------------------------------------------------------------
# 構造の不変量
# ---------------------------------------------------------------------------


def test_cylinder_shape() -> None:
    for k in (1, 2, 3, 5):
        for h in (1, 2, 4):
            g = cylinder(k, h)
            assert g.n == k * (h + 1), f"頂点数 {g.n} != {k * (h + 1)}"
            assert g.free == frozenset(range(k)), "レベル0が free でない"
            for lv in range(1, h + 1):
                for j in range(k):
                    v = lv * k + j
                    want = {(lv - 1) * k + ((j - 1) % k), (lv - 1) * k + j}
                    assert set(g.preds[v]) == want, f"{g.name} の頂点 {v} の先行点"
            assert top_of(g) == g.n - 1, "終端は最上段の末尾（= 最大番号）"


def test_kary_tree_shape() -> None:
    for k in (2, 3, 4):
        for h in (0, 1, 2, 3):
            g = kary_tree(k, h)
            want_n = (k ** (h + 1) - 1) // (k - 1)
            assert g.n == want_n, f"{g.name}: 頂点数 {g.n} != {want_n}"
            assert top_of(g) == g.n - 1, "根が最大番号"
            if h > 0:
                assert len(g.free) == k**h, "葉の枚数"
                assert len(g.preds[g.n - 1]) == k, "根の子の数"
            for v in range(g.n):
                for u in g.preds[v]:
                    assert u < v, "トポロジカル順でない"


def test_bitrev_shape() -> None:
    for k in (1, 2, 3):
        n = 2**k
        g = bitrev(k)
        assert g.n == 2 * n, f"{g.name}: 頂点数"
        assert g.free == frozenset({0}), "入力源は u_0 のみ"
        assert top_of(g) == 2 * n - 1, "終端は w の末尾"
        # w_i の先行点は {w_{i-1}} ∪ {u_{bitrev(i)}}
        for i in range(n):
            w = n + i
            rev = int(format(i, f"0{k}b")[::-1], 2)
            want = {rev} | ({n + i - 1} if i > 0 else set())
            assert set(g.preds[w]) == want, f"{g.name}: w_{i} の先行点"


def test_all_dags_are_valid() -> None:
    """FAMILIES に登録した全インスタンスが Dag の不変条件を満たす。"""
    for name, build, params in FAMILIES:
        for ps in params:
            g = build(*ps)
            assert g.n > 0
            t = top_of(g)
            assert 0 <= t < g.n
            assert t not in g.free, f"{name}{ps}: 終端が free"


# ---------------------------------------------------------------------------
# 端での退化 = 既知の族との一致（新しい定義が正しいことの一次証拠）
# ---------------------------------------------------------------------------


def test_cylinder_k1_is_chain() -> None:
    """幅 1 の円筒は鎖そのもの。既に確定している鎖の表と一致しなければならない。"""
    known = [1, 3, 5, 9, 11, 15, 19]  # M*(chain(n)), n=1..7（先行プロジェクト確定値）
    for h, want in enumerate(known, start=1):
        g = cylinder(1, h)
        t = top_of(g)
        p = fast.pmin(g, t)
        assert p == rp.pmin(rp.chain(h), h), f"cylinder(1,{h}) の p_min が鎖と違う"
        assert fast.mstar(g, t, p) == want, f"cylinder(1,{h}) の M* が {want} でない"


def test_cylinder_wide_is_pyramid() -> None:
    """幅が高さより広い（$k \\ge h+1$）円筒は、巻きが効かずピラミッドに退化する。"""
    for h in (1, 2, 3, 4):
        k = h + 1
        gc, tc = anc(cylinder(k, h))
        gp = rp.pyramid(h)
        tp = gp.n - 1
        assert gc.n == gp.n, f"祖先に制限した cylinder({k},{h}) の頂点数がピラミッドと違う"
        pc = fast.pmin(gc, tc)
        pp = fast.pmin(gp, tp)
        assert pc == pp, f"cylinder({k},{h}) と pyr({h}) の p_min: {pc} vs {pp}"
        assert fast.mstar(gc, tc, pc) == fast.mstar(gp, tp, pp), (
            f"cylinder({k},{h}) と pyr({h}) の M* が違う"
        )


def test_cylinder_k_ge_h_has_the_same_game_as_pyramid() -> None:
    """**$k\\ge h$ なら円筒はピラミッドと同じゲームである**（測定ではなく構造の帰結）。

    退化の補題が保証するのは $k\\ge h+1$ までだが、測定では $k=h$ でも
    $p_{\\min}$・$M^*$ が一致した（`data/families/findings.md` §3.2）。理由は
    **$k=h$ で衝突するのがレベル 0（`free`）の 2 頂点だけ**だからである。
    ゲームは free 頂点の同一視に影響されない（先行点が free なら常に可用なので、
    どの free かは効かない）。したがって**非 free 頂点とその非 free 先行点だけ**の
    署名が一致すれば、厳密値の一致は測定に依らず従う。
    """
    for h in (2, 3, 4, 5, 6):
        want = game_signature(rp.pyramid(h))
        for k in (h, h + 1, h + 2):
            got = game_signature(anc(cylinder(k, h))[0])
            assert got == want, f"cylinder({k},{h}) の署名がピラミッド({h}) と違う"


def test_cylinder_k_lt_h_is_a_different_game() -> None:
    """$k\\le h-1$ では巻きが**非 free 頂点**に届くので、署名が一致しなくなる。

    効き始めの位置を型で押さえておく（ここから先が新規測定の領域である）。
    """
    for h in (3, 4, 5, 6):
        want = game_signature(rp.pyramid(h))
        got = game_signature(anc(cylinder(h - 1, h))[0])
        assert got != want, f"cylinder({h - 1},{h}) の署名がピラミッド({h}) と同じ"


def test_game_signature_ignores_free_identity() -> None:
    """署名が「free 頂点の個数」に依らないこと（同じゲームを別の入力源で書いても同じ）。"""
    g = cylinder(3, 3)
    ga, _ = anc(g)
    sig = game_signature(ga)
    assert len(sig) == ga.n - len(ga.free), "署名の長さは非 free 頂点の個数"
    assert all(all(0 <= u < len(sig) for u in ps) for ps in sig), "番号が範囲外"


def test_kary_k2_is_complete_binary_tree() -> None:
    """2 分木は既存の `complete_binary_tree` と厳密値が一致する。"""
    # 葉 free 流儀。exp01 の all-pebbled 流儀の表 5, 17, 53 と**レベルが 1 ずれる**
    # （`data/exp01_findings.md` §2「2 つの正規化は1レベルずれるだけ」）。
    known_mstar = {1: 1, 2: 5, 3: 17, 4: 53}
    for h in (1, 2, 3, 4):
        g = kary_tree(2, h)
        t = top_of(g)
        gb = rp.complete_binary_tree(h)
        tb = gb.n - 1
        p = fast.pmin(g, t)
        assert p == fast.pmin(gb, tb), f"kary(2,{h}) と cbt({h}) の p_min"
        m = fast.mstar(g, t, p)
        assert m == fast.mstar(gb, tb, p), f"kary(2,{h}) と cbt({h}) の M*"
        assert m == known_mstar[h], f"kary(2,{h}) の M* = {m}（既知値 {known_mstar[h]}）"


# ---------------------------------------------------------------------------
# 二重実装の照合（素朴 frozenset BFS ⟷ ビットマスク双方向 BFS）
# ---------------------------------------------------------------------------


def _naive_vs_fast(g: rp.Dag, pmax: int = 12) -> None:
    t = top_of(g)
    for p in range(1, pmax + 1):
        a, _ = rp.bfs(g, t, p)
        b = fast.mstar(g, t, p)
        assert a == b, f"{g.name} p={p}: 素朴 {a} != 高速 {b}"


def test_matches_komarath_sarma_sawlani_tree_results() -> None:
    """文献の値と突き合わせる（KF-25/KF-26。arXiv:1604.05510 本文）。

    対応: **我々の `kary_tree(2,h)`（葉が free）= 彼らの $Bt_h$**（$2^h-1$ 頂点・全ペブル）。
    彼らの Definition 1（$P_1=\\emptyset$, $P_m=\\{r\\}$, 1 手 1 トグル）は我々のゲームと同一で、
    彼らの persistent reversible pebbling number $R_\\bullet$ が我々の $p_{\\min}$ に当たる。

    本文から取れる検査:
      - Proposition 16(2): **$R_\\bullet(Bt_3)=5$**（明示の厳密値）
      - Proposition 16(1): $R_\\bullet(Bt_h) \\ge R_\\bullet(Bt_{h-1})+1$
      - Proposition 16(2): $R_\\bullet(Bt_h) \\ge h+2$（$h\\ge3$）
      - Proposition 16(3): $R_\\bullet(Ch_n) \\le \\lceil\\log_2 n\\rceil+1$（KF-04 と同じ）

    ⚠️ 彼らは **visiting** $R_\\phi$ と **persistent** $R_\\bullet$ を区別し
    $R_\\phi \\le R_\\bullet \\le R_\\phi+1$ としている。我々の $p_{\\min}$ は $R_\\bullet$ のほう。
    引用時に取り違えないこと（KF-07 と同型の罠）。
    """
    import math

    pmin_bt = {h: fast.pmin(kary_tree(2, h), top_of(kary_tree(2, h))) for h in (1, 2, 3, 4)}
    assert pmin_bt[3] == 5, f"R_bullet(Bt_3) は本文で 5、実測 {pmin_bt[3]}"
    for h in (2, 3, 4):
        assert pmin_bt[h] >= pmin_bt[h - 1] + 1, f"Prop 16(1) に反する（h={h}）"
    for h in (3, 4):
        assert pmin_bt[h] >= h + 2, f"Prop 16(2) に反する（h={h}）"
    # Prop 16(3): 鎖の上界（我々の chain(n) は入力源が free なので n 頂点がペブル対象）
    for n in (2, 4, 8, 12):
        g = cylinder(1, n)  # = chain(n)
        p = fast.pmin(g, top_of(g))
        assert p <= math.ceil(math.log2(n)) + 1, f"Prop 16(3) に反する（n={n}, p_min={p}）"


def test_agrees_with_naive_bfs() -> None:
    for g in (cylinder(2, 2), cylinder(3, 2), cylinder(3, 3), cylinder(2, 4)):
        _naive_vs_fast(g, pmax=8)
    for g in (kary_tree(3, 1), kary_tree(3, 2), kary_tree(4, 1)):
        _naive_vs_fast(g, pmax=8)
    for g in (bitrev(1), bitrev(2)):
        _naive_vs_fast(g, pmax=8)


# ---------------------------------------------------------------------------
# 健全性（`data/cpsat_interval_findings.md` §1 の系）
# ---------------------------------------------------------------------------


def test_mstar_is_odd() -> None:
    """clean 可逆ペブリングでは $M^*=2A-1$ なので、$M^*$ は常に奇数。

    偶数が出たら実装のバグである（族が変わっても成り立つ普遍の検査）。
    """
    for g in (cylinder(2, 3), cylinder(3, 3), kary_tree(3, 2), bitrev(2)):
        t = top_of(g)
        p = fast.pmin(g, t)
        assert p is not None, f"{g.name}: p_min が見つからない"
        for q in range(p, p + 3):
            m = fast.mstar(g, t, q)
            if m is not None:
                assert m % 2 == 1, f"{g.name} p={q}: M*={m} が偶数"


def test_schedule_verifies() -> None:
    """抽出した最適スケジュールが独立の検証器を通り、長さが M* と一致する。"""
    for g in (cylinder(2, 3), cylinder(3, 2), kary_tree(3, 2), bitrev(2)):
        t = top_of(g)
        p = fast.pmin(g, t)
        seq = fast.schedule(g, t, p)
        assert seq is not None, f"{g.name}: スケジュールが取れない"
        fast.verify_schedule(g, t, p, seq)
        assert len(seq) == fast.mstar(g, t, p), f"{g.name}: 長さが M* と違う"


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
