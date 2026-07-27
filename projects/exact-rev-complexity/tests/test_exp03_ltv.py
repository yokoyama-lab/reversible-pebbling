"""LTV Procedure A の実装が原文どおりであることと、検証器の健全性を検査する。

    python3 tests/test_exp03_ltv.py

**この検査が本質的な理由**: 「定理 B1 は LTV Lemma 1 を改良する」という主張は、
LTV の構成を我々のモデルで走らせた実測値に依拠する。したがって
(a) `ltv_pebble` が LTV Cor 2 の $2^n-1$ を実際に達成すること、
(b) 我々のモデルの非 clean 版 reach が $2^p-1$ に一致すること（= 両モデルは終端条件だけが違う）、
(c) 検証器が不正な手順を確実に落とすこと、
の 3 点を固定しないと、比較そのものが無意味になる。
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import exp03_ltv as L  # noqa: E402
import exp03_reach as R  # noqa: E402

FAILURES: list[str] = []


def check(cond: bool, msg: str) -> None:
    if cond:
        print(f"  ok   {msg}")
    else:
        print(f"  FAIL {msg}")
        FAILURES.append(msg)


def eq(actual, expected, msg: str) -> None:
    check(actual == expected, f"{msg}: {actual!r} == {expected!r}")


def test_verifier_rejects_bad_schedules() -> None:
    """検証器が不正な手順を落とすこと（検証器が甘いと全ての比較が無意味になる）。"""
    print("test_verifier_rejects_bad_schedules")
    # 先行点が無いのに put
    r = L.verify_schedule([("put", 3)], 3)
    check(not r["ok"], f"先行点なしの put を拒否: {r.get('why','')}")
    # clean でない終端
    r = L.verify_schedule([("put", 1), ("put", 2)], 2, require_clean=True)
    check(not r["ok"], f"clean でない終端を拒否: {r.get('why','')}")
    # 非 clean モードなら同じ手順が通る
    r = L.verify_schedule([("put", 1), ("put", 2)], 2, require_clean=False)
    check(r["ok"], "非 clean モードでは同じ手順が通る")
    # 可逆な取り除きを erase と称するのを拒否
    r = L.verify_schedule([("put", 1), ("erase", 1)], 1)
    check(not r["ok"], f"可逆な取り除きの erase を拒否: {r.get('why','')}")
    # 正しい手順は通り、消去回数・ピークが実測される
    r = L.verify_schedule([("put", 1), ("put", 2), ("erase", 2)], 1, require_clean=True)
    check(not r["ok"], "erase(2) は先行点 1 が載っているので可逆 → 拒否")
    r = L.verify_schedule(
        [("put", 1), ("put", 2), ("take", 1), ("put", 3), ("erase", 2)], 3, require_clean=True
    )
    check(r["ok"], "正しい手順は通る")
    if r["ok"]:
        eq(r["peak"], 2, "ピークの実測")
        eq(r["erasures"], 1, "消去回数の実測")
        eq(r["moves"], 5, "手数の実測")


def test_ltv_pebble_reaches_2n_minus_1() -> None:
    """LTV `pebble(0,n)` は $2^n-1$ に到達し、$n$ 本を置いたまま終わる（Cor 2・非 clean）。"""
    print("test_ltv_pebble_reaches_2n_minus_1")
    for n in range(1, 9):
        seq = L.ltv_pebble(0, n)
        target = 2**n - 1
        r = L.verify_schedule(seq, target, require_clean=False)
        check(r["ok"], f"pebble(0,{n}) が規則を満たす（{r.get('why','')}）")
        if r["ok"]:
            eq(r["peak"], n, f"pebble(0,{n}) のピーク = n")
            eq(r["erasures"], 0, f"pebble(0,{n}) は消去 0")
            eq(len(r["final"]), n, f"pebble(0,{n}) は n 本を置いたまま終わる（非 clean）")
            eq(max(r["final"]), target, f"pebble(0,{n}) の最大到達節点 = 2^n-1")
            # 2 進階段の位置になっているか
            want = []
            acc = 0
            for i in range(n - 1, -1, -1):
                acc += 2**i
                want.append(acc)
            eq(r["final"], sorted(want), f"pebble(0,{n}) の終端配置は 2 進階段")


def test_ltv_unpebble_is_inverse() -> None:
    """`unpebble(s,n)` は `pebble(s,n)` の逆（合成すると空に戻る・消去 0）。"""
    print("test_ltv_unpebble_is_inverse")
    for n in range(1, 8):
        seq = L.ltv_pebble(0, n) + L.ltv_unpebble(0, n)
        # 終端が空なので target を持たない。空状態を許す形で検査する。
        state: set[int] = set()
        peak = 0
        er = 0
        ok = True
        for act, v in seq:
            ready = (v - 1) == 0 or (v - 1) in state
            if act == "put":
                ok = ok and ready and v not in state
                state.add(v)
                peak = max(peak, len(state))
            elif act == "take":
                ok = ok and ready and v in state
                state.discard(v)
            else:
                er += 1
                state.discard(v)
        check(ok and state == set() and er == 0,
              f"pebble(0,{n})+unpebble(0,{n}) は空に戻る（消去 {er}, peak {peak}）")
        eq(peak, n, f"合成のピーク = n（n={n}）")


def test_nonclean_reach_matches_ltv_cor2() -> None:
    """我々のモデルの非 clean reach が $2^p-1$（LTV Cor 2）に一致する。

    これが**両モデルは終端条件だけが違う**ことの決定的な証拠。
    """
    print("test_nonclean_reach_matches_ltv_cor2")
    # p=7 以上は到達可能配置が ~2^{p(p-1)/2} 個あり素朴探索では重い（p=6 で約 9 秒）。
    # 回帰テストとしては p<=6 に留め、p=7 は scripts/exp03_ltv.py --nonclean 7 で別途確認する。
    for p in range(1, 7):
        eq(L.nonclean_reach(p, 0, nmax=2 ** (p + 1)), 2**p - 1,
           f"非 clean reach(p={p}, e=0) = 2^p-1")


def test_procedure_a_meets_its_claim() -> None:
    """Procedure A が主張どおり「$n+2$ ペブル・$m-1$ 消去で $m2^n$」を我々のモデルで達成する。"""
    print("test_procedure_a_meets_its_claim")
    for n in range(0, 6):
        for m in range(1, 7):
            target = m * 2**n
            seq = L.ltv_procedure_a(n, m, finish_clean=True)
            r = L.verify_schedule(seq, target, require_clean=True)
            check(r["ok"], f"A(n={n},m={m}) が clean で成立（{r.get('why','')}）")
            if r["ok"]:
                check(r["peak"] <= n + 2, f"A(n={n},m={m}) ピーク {r['peak']} <= n+2={n+2}")
                check(r["erasures"] <= max(m - 1, 0),
                      f"A(n={n},m={m}) 消去 {r['erasures']} <= m-1={m-1}")


def test_ours_beats_ltv_at_same_budget() -> None:
    """同じ (ピーク, 消去) 予算で、我々の構成の到達長が Procedure A 以上であること。"""
    print("test_ours_beats_ltv_at_same_budget")
    for p in range(2, 9):
        for e in range(0, 6):
            n, m = p - 2, e + 1
            ltv_target = m * 2**n
            r = L.verify_schedule(L.ltv_procedure_a(n, m, finish_clean=True),
                                  ltv_target, require_clean=True)
            if not r["ok"] or r["peak"] > p or r["erasures"] > e:
                continue
            ours = (e + 2) * 2 ** (p - 2)
            ok, why = R.simulate(ours, p, R.construction(p, e))
            check(ok, f"我々の構成 p={p} e={e} が成立（{why}）")
            check(ours >= ltv_target,
                  f"p={p} e={e}: 我々 {ours} >= LTV-A {ltv_target}")


def main() -> int:
    for fn in (
        test_verifier_rejects_bad_schedules,
        test_ltv_pebble_reaches_2n_minus_1,
        test_ltv_unpebble_is_inverse,
        test_nonclean_reach_matches_ltv_cor2,
        test_procedure_a_meets_its_claim,
        test_ours_beats_ltv_at_same_budget,
    ):
        fn()
    print()
    if FAILURES:
        print(f"FAILED: {len(FAILURES)} 件")
        for m in FAILURES[:25]:
            print("  -", m)
        return 1
    print("all tests passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
