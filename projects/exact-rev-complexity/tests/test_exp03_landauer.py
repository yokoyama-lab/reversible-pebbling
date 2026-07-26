"""候補3（$e$-Landauer ペブリングゲーム）の回帰テスト。pytest 不要。

    python3 tests/test_exp03_landauer.py

テストファースト方針: まず「両端の整合性」を固定する。
  - $e=0$ で `revpebble.bfs` の可逆ペブリング $M^*$ に一致
  - $e$ 十分大で標準ペブリング（取り除き自由）の clean 最小手数に一致
これが崩れていれば実装バグであり、以降の数値は一切使わない。
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import revpebble as rp  # noqa: E402
import landauer as ld  # noqa: E402

FAILURES: list[str] = []


def check(cond: bool, msg: str) -> None:
    if cond:
        print(f"  ok   {msg}")
    else:
        print(f"  FAIL {msg}")
        FAILURES.append(msg)


def eq(actual, expected, msg: str) -> None:
    check(actual == expected, f"{msg}: {actual!r} == {expected!r}")


# ---------------------------------------------------------------------------


def test_e0_matches_reversible() -> None:
    """e=0 は通常の可逆ペブリングに一致（両端の整合性・下端）。"""
    print("test_e0_matches_reversible")
    for n in range(1, 13):
        pm = rp.pmin(rp.chain(n), n)
        assert pm is not None
        for p in range(1, pm + 3):
            want, _ = rp.bfs(rp.chain(n), n, p)
            for mode in ld.MODES:
                got = ld.landauer_profile(rp.chain(n), n, p, 0, mode=mode)[0]
                eq(got, want, f"chain({n}) p={p} e=0 mode={mode}")
    for h in range(1, 4):
        g = rp.complete_binary_tree(h)
        root = g.n - 1
        pm = rp.pmin(g, root)
        assert pm is not None
        want, _ = rp.bfs(g, root, pm)
        eq(ld.landauer_profile(g, root, pm, 0)[0], want, f"cbt({h}) p=p_min e=0")
    for h in range(1, 4):
        g = rp.pyramid(h)
        top = g.n - 1
        pm = rp.pmin(g, top)
        assert pm is not None
        want, _ = rp.bfs(g, top, pm)
        eq(ld.landauer_profile(g, top, pm, 0)[0], want, f"pyr({h}) p=p_min e=0")


def test_large_e_matches_standard() -> None:
    """e が十分大きいとき標準ペブリングに一致（両端の整合性・上端）。"""
    print("test_large_e_matches_standard")
    for n in range(1, 11):
        for p in range(2, 6):
            big = 2 * n + 4
            for mode in ld.MODES:
                want = ld.standard_bfs(rp.chain(n), n, p, bulk=(mode == "bits"))
                prof = ld.landauer_profile(rp.chain(n), n, p, big, mode=mode)
                eq(prof[big], want, f"chain({n}) p={p} e={big} mode={mode} = standard")
    for h in range(1, 4):
        for g in (rp.complete_binary_tree(h), rp.pyramid(h)):
            t = g.n - 1
            pm = rp.pmin(g, t)
            assert pm is not None
            for p in (pm, pm + 1):
                big = 2 * g.n
                for mode in ld.MODES:
                    want = ld.standard_bfs(g, t, p, bulk=(mode == "bits"))
                    got = ld.landauer_profile(g, t, p, big, mode=mode)[big]
                    eq(got, want, f"{g.name} p={p} e={big} mode={mode} = standard")


def test_standard_chain_closed_form() -> None:
    """標準ペブリングの clean 最小手数は鎖で $2n-1$（$p\\ge2$）。独立な検算。"""
    print("test_standard_chain_closed_form")
    for n in range(1, 13):
        for p in range(2, 6):
            eq(ld.standard_bfs(rp.chain(n), n, p), 2 * n - 1, f"standard chain({n}) p={p}")
    eq(ld.standard_bfs(rp.chain(1), 1, 1), 1, "standard chain(1) p=1")
    eq(ld.standard_bfs(rp.chain(2), 2, 1), None, "standard chain(2) p=1 は不能")
    # 一括取り除きを許した標準ペブリングは鎖で n + ceil((n-1)/(p-1))
    for n in range(2, 13):
        for p in range(2, 6):
            want = n + -(-(n - 1) // (p - 1))
            eq(
                ld.standard_bfs(rp.chain(n), n, p, bulk=True),
                want,
                f"standard bulk chain({n}) p={p}",
            )


def test_profile_vs_naive() -> None:
    """主実装（1 回の BFS で全 e）と素朴実装（e ごとに独立 BFS）の二重照合。"""
    print("test_profile_vs_naive")
    emax = 4
    for n in range(1, 9):
        pm = rp.pmin(rp.chain(n), n)
        assert pm is not None
        for p in range(1, pm + 2):
            for mode in ld.MODES:
                prof = ld.landauer_profile(rp.chain(n), n, p, emax, mode=mode)
                naive = [ld.landauer_bfs(rp.chain(n), n, p, e, mode=mode) for e in range(emax + 1)]
                # 素朴版は「予算 e 以内」の最短なので単調化は不要（BFS が直接最短を返す）
                eq(prof, naive, f"chain({n}) p={p} mode={mode} profile==naive")
    for h in (1, 2):
        for g in (rp.complete_binary_tree(h), rp.pyramid(h)):
            t = g.n - 1
            pm = rp.pmin(g, t)
            assert pm is not None
            prof = ld.landauer_profile(g, t, pm, 3)
            naive = [ld.landauer_bfs(g, t, pm, e) for e in range(4)]
            eq(prof, naive, f"{g.name} p={pm} profile==naive")


def test_monotone_in_e() -> None:
    """$M^*$ は $e$ について単調非増加（そうでなければバグ）。"""
    print("test_monotone_in_e")
    for n in range(1, 15):
        pm = rp.pmin(rp.chain(n), n)
        assert pm is not None
        for p in range(pm, pm + 3):
            for mode in ld.MODES:
                prof = ld.landauer_profile(rp.chain(n), n, p, 6, mode=mode)
                check(ld.is_monotone(prof), f"chain({n}) p={p} mode={mode} monotone {prof}")


def test_bits_le_ops() -> None:
    """一括消去を許す bits 変種は ops 変種以下の手数（同じビット予算で）。"""
    print("test_bits_le_ops")
    for n in range(1, 13):
        pm = rp.pmin(rp.chain(n), n)
        assert pm is not None
        for p in range(pm, pm + 3):
            ops = ld.landauer_profile(rp.chain(n), n, p, 6, mode="ops")
            bits = ld.landauer_profile(rp.chain(n), n, p, 6, mode="bits")
            ok = all(
                b is not None and o is not None and b <= o
                for o, b in zip(ops, bits)
                if o is not None
            )
            check(ok, f"chain({n}) p={p} bits<=ops {bits} <= {ops}")


def test_reach_e0_known() -> None:
    """$e=0$ の到達長は既知の $2^{p-1}$（Královič 2001 Thm 3.1 の系）。"""
    print("test_reach_e0_known")
    for p in range(1, 6):
        eq(ld.reach_e(p, 0, nmax=40), 2 ** (p - 1), f"reach_e(p={p}, e=0)")


def test_saturation_helper() -> None:
    """飽和点ヘルパの境界動作。"""
    print("test_saturation_helper")
    eq(ld.saturation([9, 7, 5, 5, 5]), 2, "saturation 基本")
    eq(ld.saturation([5, 5, 5]), 0, "saturation は最小の e を返す")
    eq(ld.saturation([None, None, None]), None, "全 None")
    check(ld.is_monotone([None, 9, 7, 7]), "None → 値の順は単調扱い")
    check(not ld.is_monotone([7, 9]), "増加は非単調")
    check(not ld.is_monotone([7, None]), "値 → None は非単調")


def test_exact_values_locked() -> None:
    """厳密値の固定（回帰検出）。値は `data/exp03_*.csv` の生成元と同一。"""
    print("test_exact_values_locked")
    # 先行プロジェクトの確定値（e=0, p=p_min）を再現していること
    eq(
        [ld.landauer_profile(rp.chain(n), n, rp.pmin(rp.chain(n), n), 0)[0] for n in range(1, 17)],
        [1, 3, 5, 9, 11, 15, 19, 25, 25, 29, 33, 39, 45, 53, 61, 71],
        "e=0 p=p_min n=1..16",
    )
    # 見せ場: n=16, p=5 の e=0..4
    eq(
        ld.landauer_profile(rp.chain(16), 16, 5, 4),
        [71, 45, 37, 31, 31],
        "chain(16) p=5 e=0..4",
    )
    eq(
        ld.landauer_profile(rp.chain(20), 20, 6, 4),
        [77, 57, 47, 39, 39],
        "chain(20) p=6 e=0..4",
    )
    # p_min 未満（消去が p_min を下げる）
    eq(
        ld.landauer_profile(rp.chain(20), 20, 5, 6),
        [None, 65, 53, 45, 39, 39, 39],
        "chain(20) p=5(<p_min=6) e=0..6",
    )
    # bits 変種
    eq(
        ld.landauer_profile(rp.chain(12), 12, 5, 6, mode="bits"),
        [39, 29, 22, 21, 20, 20, 19],
        "chain(12) p=5 e=0..6 mode=bits",
    )


def test_conjecture_esat_ops() -> None:
    """予想 A: $e^*_{\\mathrm{ops}}(n,p) = \\lceil (n-1)/(p-1)\\rceil - 1$、飽和値は $2n-1$。

    $p < p_{\\min}(n,0)$（到達に消去が必要な領域）も含めて検査する。
    """
    print("test_conjecture_esat_ops")
    for n in range(2, 15):
        for p in range(2, 9):
            budget = n + 1
            prof = ld.landauer_profile(rp.chain(n), n, p, budget)
            if prof[budget] is None:
                continue
            pred = -(-(n - 1) // (p - 1)) - 1
            eq(ld.saturation(prof), pred, f"e*_ops chain({n}) p={p}")
            eq(prof[budget], 2 * n - 1, f"飽和値 chain({n}) p={p} = 2n-1")


def test_conjecture_reach_and_pmin() -> None:
    """予想 B: $\\mathrm{reach}(p,e)=(e+2)2^{p-2}$、系として $p_{\\min}(n,e)=2+\\lceil\\log_2(n/(e+2))\\rceil$。

    LTV Lemma 1 の構成は $(e+1)2^{p-2}$ しか保証しない（= 厳密値は 1 ブロック分だけ強い）。
    """
    print("test_conjecture_reach_and_pmin")
    import math

    for p in range(2, 5):
        for e in range(0, 4):
            pred = (e + 2) * 2 ** (p - 2)
            got = ld.reach_e(p, e, nmax=pred + 4)
            eq(got, pred, f"reach(p={p}, e={e})")
            check(got >= (e + 1) * 2 ** (p - 2), f"reach(p={p},e={e}) は LTV Lemma 1 以上")
    for n in (8, 12, 16):
        for e in range(0, 5):
            pred = 2 + math.ceil(math.log2(n / (e + 2))) if n > e + 2 else 2
            eq(ld.pmin_e(rp.chain(n), n, e), pred, f"p_min(n={n}, e={e})")


def main() -> int:
    for fn in (
        test_saturation_helper,
        test_standard_chain_closed_form,
        test_e0_matches_reversible,
        test_large_e_matches_standard,
        test_profile_vs_naive,
        test_monotone_in_e,
        test_bits_le_ops,
        test_reach_e0_known,
        test_exact_values_locked,
        test_conjecture_esat_ops,
        test_conjecture_reach_and_pmin,
    ):
        fn()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} 件")
        for m in FAILURES:
            print("  -", m)
        return 1
    print("all tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
