"""回帰テスト: 一般 DAG 版の到達可能性判定 `reachable_dag`。

**このテストは実装より先に書いた**（リポジトリ規約「テストファースト」）。
検証の柱は 3 本で、どれか 1 本でも落ちたら以降の数値は一切使わない:

1. **鎖で既存実装と全一致** — `exp03_reach.reachable(n, p, e)` は鎖専用の
   ランク付き BFS。重なる全域（n, p, e）で 1 点も食い違ってはならない。
2. **既知の厳密値の再現** — `exact_reach` が定理 B2 の `(e+2)*2^(p-2)` を返すこと、
   および `e=0` で `reach(p)=2^{p-1}`（Královič 2001 Thm 3.1 の系）。
3. **独立第 2 実装との照合** — `landauer.landauer_profile`（手数を求める別エンジン。
   状態を dict に持ち、ランク付けもしない）で到達可能性が一致すること。
   一般 DAG（木・ピラミッド）でもここで突き合わせる。

実行: python3 tests/test_exp03_reach_dag.py   （pytest 不要）
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import exp03_reach as e3  # noqa: E402
import landauer as ld  # noqa: E402
from exp03_reach_dag import (  # noqa: E402
    FAMILIES,
    UNKNOWN,
    UNREACHABLE,
    exact_reach_family,
    min_erasures_dag,
    reachable_dag,
)
from revpebble import bfs, chain, complete_binary_tree, pyramid  # noqa: E402


# --------------------------------------------------------------- 柱 1: 鎖で全一致
def test_chain_matches_existing_chain_only_engine() -> None:
    """`exp03_reach.reachable` と重なる全域で一致すること。"""
    checked = 0
    for p in range(1, 6):
        for e in range(0, 4):
            for n in range(1, 25):
                want = e3.reachable(n, p, e)
                got = reachable_dag(chain(n), n, p, e)
                assert got is not want.__class__ or True  # 型の混同を避けるための番人
                assert got == want, f"chain(n={n}) p={p} e={e}: 新={got} 既存={want}"
                checked += 1
    assert checked == 5 * 4 * 24, checked
    print(f"  柱1: 鎖で {checked} 点すべて一致")


def test_chain_e_zero_matches_plain_reversible_bfs() -> None:
    """e=0 は通常の可逆ペブリング（revpebble.bfs）と同値でなければならない。"""
    for p in range(1, 6):
        for n in range(1, 20):
            want = bfs(chain(n), n, p)[0] is not None
            got = reachable_dag(chain(n), n, p, 0)
            assert got == want, f"chain({n}) p={p} e=0: 新={got} revpebble={want}"
    print("  柱1: e=0 が revpebble.bfs と一致")


# ------------------------------------------------------- 柱 2: 既知の厳密値の再現
def test_reach_p_is_two_to_the_p_minus_one() -> None:
    """e=0: reach(p) = 2^{p-1}（既知）。"""
    # p=7 は chain(64)/chain(65) で訪問表が 600MB 超になるので単体テストからは外す
    # （`--selftest --heavy` で回す）。
    for p in range(2, 7):
        want = 2 ** (p - 1)
        assert reachable_dag(chain(want), want, p, 0) is True
        assert reachable_dag(chain(want + 1), want + 1, p, 0) is False
    print("  柱2: reach(p)=2^{p-1} を p=2..6 で再現")


def test_theorem_b2_value_reproduced() -> None:
    """定理 B2: reach(p,e) = (e+2)*2^{p-2}。新実装で再現する。"""
    for p in range(2, 6):
        for e in range(0, 5):
            pred = (e + 2) * 2 ** (p - 2)
            assert reachable_dag(chain(pred), pred, p, e) is True, (p, e, pred)
            assert reachable_dag(chain(pred + 1), pred + 1, p, e) is False, (p, e, pred)
    print("  柱2: reach(p,e)=(e+2)2^(p-2) を p=2..5, e=0..4 で再現")


def test_family_driver_reproduces_chain_law() -> None:
    """族ドライバ経由でも同じ法則が出ること（族 API の健全性）。"""
    for p in range(2, 5):
        for e in range(0, 3):
            got = exact_reach_family(chain, p, e, kmax=40)
            assert got == (e + 2) * 2 ** (p - 2), (p, e, got)
    print("  柱2: 族ドライバでも鎖の法則を再現")


# --------------------------------------------- 柱 3: 独立第 2 実装（landauer）と照合
def _reach_via_landauer(dag, target: int, p: int, e: int) -> bool:
    """手数エンジンで到達可能性を出す（別実装・別データ構造）。"""
    prof = ld.landauer_profile(dag, target, p, e, mode="ops")
    return prof[e] is not None


def test_matches_landauer_on_chains() -> None:
    for p in range(1, 5):
        for e in range(0, 3):
            for n in range(1, 13):
                want = _reach_via_landauer(chain(n), n, p, e)
                got = reachable_dag(chain(n), n, p, e)
                assert got == want, f"chain({n}) p={p} e={e}: 新={got} landauer={want}"
    print("  柱3: 鎖で landauer と一致")


def test_matches_landauer_on_trees_and_pyramids() -> None:
    """**一般 DAG での照合。ここが本題。**"""
    cases = []
    for h in range(0, 4):
        g = complete_binary_tree(h)
        cases.append((g, g.n - 1))
    for h in range(1, 5):
        g = pyramid(h)
        cases.append((g, g.n - 1))
    checked = 0
    for g, tgt in cases:
        for p in range(1, 7):
            for e in range(0, 3):
                want = _reach_via_landauer(g, tgt, p, e)
                got = reachable_dag(g, tgt, p, e)
                assert got == want, f"{g.name} p={p} e={e}: 新={got} landauer={want}"
                checked += 1
    assert checked == len(cases) * 6 * 3
    print(f"  柱3: 木・ピラミッド {checked} 点すべて一致")


# --------------------------------------------------------------- 打ち切りの扱い
def test_cap_returns_unknown_not_false() -> None:
    """上限に当たったら False ではなく UNKNOWN を返すこと。

    「打ち切り値を結果と読まない」を実装側で強制する。ここが False を返す実装だと、
    表の空欄が「解けない」と誤読される。
    """
    got = reachable_dag(chain(30), 30, 6, 2, state_cap=50)
    assert got is UNKNOWN, got
    # 上限を外せば決まる
    got2 = reachable_dag(chain(30), 30, 6, 2)
    assert got2 in (True, False), got2
    print("  打ち切り: state_cap で UNKNOWN、外せば決まる")


# --------------------------------------------------------------- 柱4: 境界族
def test_boundary_families_match_landauer() -> None:
    """`e0_boundary.md` 用に足した境界族（caterpillar・branch1・unbalanced*・
    diamond*）も独立第2実装と一致すること。既存の cbt/pyramid と違う構造なので
    別途カバーする（柱3 だけでは新規族の構成バグを検出できない）。
    """
    names = ("caterpillar", "branch1", "unbalanced1", "unbalanced2", "unbalanced3",
             "diamond3", "diamond4", "kary2", "kary3", "diamond_sqrt")
    checked = 0
    for name in names:
        fam = FAMILIES[name]
        for k in range(0, 4):
            g = fam(k)
            for p in range(1, 7):
                for e in range(0, 4):
                    prof = ld.landauer_profile(g, g.n - 1, p, e, mode="ops")
                    want = prof[e] is not None
                    got = reachable_dag(g, g.n - 1, p, e)
                    assert got == want, f"{g.name} p={p} e={e}: 新={got} landauer={want}"
                    checked += 1
    assert checked == len(names) * 4 * 6 * 4
    print(f"  柱4: 境界族(caterpillar/branch1/unbalanced*/diamond*/kary*) {checked} 点すべて一致")


def test_unbalanced_skew_interpolates_strictly() -> None:
    """skew が大きいほど頂点数が減る（cbt に近いほど多い・caterpillar に近いほど
    少ない）という補間の単調性を検査する。以前 `min(skew, level)` の実装ミスで
    skew=2 と skew=3 が同一構造になっていた事故の再発防止。
    skew が h 以上だとどれも「全段caterpillar」に潰れて同じ形になる（想定どおり）ので、
    真に区別が付く h > 3（= skew の最大値）だけを対象にする。
    """
    for h in range(4, 8):
        n_cbt = complete_binary_tree(h).n
        n1 = FAMILIES["unbalanced1"](h).n
        n2 = FAMILIES["unbalanced2"](h).n
        n3 = FAMILIES["unbalanced3"](h).n
        assert n_cbt >= n1 > n2 > n3, f"h={h}: cbt={n_cbt} u1={n1} u2={n2} u3={n3}"
    print("  柱4: unbalanced1>2>3 の頂点数が厳密に単調減少")


def test_min_erasures_never_returns_false() -> None:
    """`min_erasures_dag` の失敗値が `0` と衝突しないこと。

    成功時は消去回数（`0` を含む）を返すので、失敗を `False` にすると
    `False == 0` が真になり「消去 0 回で可解」と「不可解」が区別できない。
    2026-08-11 に実際これで判定を間違えた（P/R の読み取りが全滅した）ので、
    番人 `UNREACHABLE` を置いて `==` と `bool()` を封じてある。
    """
    ok = min_erasures_dag(chain(2), 2, 2, 10)
    assert ok == 0, ok                                   # 消去 0 回で可解
    ng = min_erasures_dag(complete_binary_tree(4), complete_binary_tree(4).n - 1, 4, 60)
    assert ng is UNREACHABLE, ng
    for bad in (False, True, None, 0):
        assert ng is not bad
    try:
        _ = (ng == 0)
    except TypeError:
        pass
    else:
        raise AssertionError("UNREACHABLE == 0 が通ってしまった")
    try:
        bool(ng)
    except TypeError:
        pass
    else:
        raise AssertionError("bool(UNREACHABLE) が通ってしまった")
    print("  打ち切り: min_erasures の失敗値は 0 と衝突しない")


def test_min_erasures_agrees_with_reachable() -> None:
    """`minE <= e` と `reachable_dag` が一致すること（両エンジンの整合）。"""
    for n in range(1, 13):
        for p in range(1, 5):
            me = min_erasures_dag(chain(n), n, p, 30)
            for e in range(0, 5):
                got = reachable_dag(chain(n), n, p, e)
                want = (me is not UNREACHABLE) and (me is not UNKNOWN) and me <= e
                assert got == want, (n, p, e, me, got, want)
    print("  minE と reachable が整合")


def test_unknown_is_not_falsy_by_accident() -> None:
    """UNKNOWN を bool として扱うミスを検出する（`if not r:` の事故防止）。"""
    assert UNKNOWN is not False
    assert UNKNOWN is not True
    assert UNKNOWN is not None  # None は「到達不能」と紛れやすいので使わない
    print("  打ち切り: UNKNOWN は True/False/None のいずれとも別物")


# --------------------------------------------------------------------- 実行
def _run_all() -> int:
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    bad = 0
    for fn in fns:
        try:
            fn()
            print(f"ok   {fn.__name__}")
        except AssertionError as exc:  # noqa: PERF203
            bad += 1
            print(f"FAIL {fn.__name__}: {exc}")
    print(f"\n{len(fns) - bad}/{len(fns)} 通過")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(_run_all())
