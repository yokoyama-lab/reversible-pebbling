"""台帳の証書から読み取った**再計算の構造**を固定する（U3d）。

`data/families/findings.md` §3.5 で見つけた「$p$ を固定すると公差 $4k$ の等差になる」は、
証書を数えると次の形になっている:

  等差領域では **どの頂点も高々 2 回しか置かれない**。
  1 回だけ置かれる頂点がちょうど $p$ 個、残り $N-p$ 個が 2 回置かれる。

このとき置いた回数の総数は $A = p + 2(N-p) = 2N-p$ であり、$M^*=2A-1$ から

  $$M^* = 4N - 2p - 1$$

が従う。**族にもパラメタにも依らず、$N$ と $p$ だけで決まる。** 公差 $4k$ は
「1 段増えると $N$ が $k$ 増える」ことの帰結である。

等差が崩れる位置は、**3 回以上置かれる頂点が現れる位置**と一致する。

## 留保（誇張しないこと）

$A$ は $M^*$ から一意に決まる（$A=(M^*+1)/2$）が、**置いた回数の分布は
スケジュールに依存する**。ここで固定するのは
「BFS の距離表から復元した正準なスケジュールについての性質」であり、
**全ての最適スケジュールについての主張ではない**。
一方 $M^* = 4N-2p-1$ のほうは台帳の値そのものなので、スケジュールに依らない。

実行: python3 tests/test_families_atlas.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from family_atlas import placement_profile  # noqa: E402

#: 等差領域（`findings.md` §3.5 の表で公差が $4k$ のまま続いている範囲）
ARITHMETIC = [
    (2, 11, range(9, 17)),
    (2, 9, range(5, 12)),
    (3, 10, range(6, 8)),
]

#: 崩れた領域（同じ $k,p$ で $h$ を伸ばした先）
BROKEN = [
    (2, 9, range(12, 17)),
    (3, 10, range(8, 11)),
]


def test_arithmetic_region_has_multiplicity_at_most_two() -> None:
    for k, p, hs in ARITHMETIC:
        for h in hs:
            prof, n, _m = placement_profile("cylinder", (k, h), p)
            assert max(prof) <= 2, (
                f"cyl({k},{h}) p={p}: 3 回以上置かれた頂点がある {dict(prof)}"
            )
            assert sum(prof.values()) == n, f"cyl({k},{h}) p={p}: 頂点数が合わない"


def test_arithmetic_region_places_exactly_p_vertices_once() -> None:
    """1 回だけ置かれる頂点の個数が**ピーク上限 $p$ に一致する**。"""
    for k, p, hs in ARITHMETIC:
        for h in hs:
            prof, n, _m = placement_profile("cylinder", (k, h), p)
            assert prof[1] == p, (
                f"cyl({k},{h}) p={p}: 1 回組が {prof[1]} 個（p={p} のはず）"
            )
            assert prof[2] == n - p, f"cyl({k},{h}) p={p}: 2 回組が n-p でない"


def test_arithmetic_region_matches_the_closed_form() -> None:
    """等差領域では $M^* = 4N-2p-1$。**台帳の値そのものなのでスケジュールに依らない。**"""
    for k, p, hs in ARITHMETIC:
        for h in hs:
            _prof, n, m = placement_profile("cylinder", (k, h), p)
            assert m == 4 * n - 2 * p - 1, (
                f"cyl({k},{h}) p={p}: M*={m} != 4*{n}-2*{p}-1={4 * n - 2 * p - 1}"
            )


def test_break_coincides_with_a_third_placement() -> None:
    """等差が崩れる位置は、3 回以上置かれる頂点が現れる位置と一致する。"""
    for k, p, hs in BROKEN:
        for h in hs:
            prof, n, m = placement_profile("cylinder", (k, h), p)
            assert max(prof) >= 3, (
                f"cyl({k},{h}) p={p}: 崩れた領域なのに高々 2 回 {dict(prof)}"
            )
            assert m > 4 * n - 2 * p - 1, (
                f"cyl({k},{h}) p={p}: M*={m} が等差領域の値を上回っていない"
            )


def test_closed_form_holds_on_every_qualifying_row_of_the_ledger() -> None:
    """**台帳の全行**で、高々 2 回の行は例外なく閉形式に乗る（3 族すべて）。

    $r$ = 1 回だけ置かれた頂点の個数とすると $A = r + 2(N-r) = 2N-r$ なので
    $M^* = 4N-2r-1$ は恒等式である。**内容は $r=\\min(p,N)$ のほう**で、
    これは 3 族（円筒・$k$ 分木・ビット反転）に共通して成り立っている。

    $\\min$ が要るのは $p>N$（ペブルが頂点数より多い）ときで、そこでは
    全頂点が 1 回ずつ置かれて飽和し $M^*=2N-1$ になる。
    """
    from family_atlas import read_rows

    checked = 0
    for row in read_rows():
        if row["status"] != "exhaustive":
            continue
        params = tuple(int(x) for x in row["params"].split(":"))
        p = int(row["p"])
        prof, n, m = placement_profile(row["family"], params, p)
        if max(prof) > 2:
            continue
        want = min(p, n)
        assert prof[1] == want, (
            f"{row['family']}{params} p={p} N={n}: 1 回組が {prof[1]}（min(p,N)={want} のはず）"
        )
        assert m == 4 * n - 2 * want - 1, (
            f"{row['family']}{params} p={p}: M*={m} != 4N-2min(p,N)-1={4 * n - 2 * want - 1}"
        )
        checked += 1
    assert checked >= 131, f"検査した行が {checked} 件しかない（131 件以上のはず）"


def test_pmin_formula_for_width_two_cylinder() -> None:
    """$p_{\\min}(\\mathrm{cyl}(2,h)) = 2\\lfloor\\log_2(h-1)\\rfloor+3$（`findings.md` §3.8.1）。

    **これは予想であって定理ではない。** ここが固定するのは
    「台帳の $k=2$ の行がこの式と矛盾しない」ことだけである:

      - `exhaustive` の行では**等号**を要求する（15 点）
      - `pmin_lb` の行では**下界が式を超えない**ことだけを要求する
        （$h=17$ で $p_{\\min}\\ge11$ が証明されており、式の予言も 11。
        ただし上界は取れていないので真値が 12 以上の可能性は残る）

    式が破れたらこのテストが落ちる。それがこのテストの役目である。
    """
    import csv
    import math
    from family_atlas import CSV_PATH

    exact = lb = 0
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        for row in csv.DictReader(fh):
            if row["family"] != "cylinder":
                continue
            k, h = (int(x) for x in row["params"].split(":"))
            if k != 2 or h < 2:
                continue
            pred = 2 * int(math.log2(h - 1)) + 3
            if row["status"] == "exhaustive" and row["p"] == row["pmin"]:
                assert int(row["pmin"]) == pred, (
                    f"cyl(2,{h}): p_min={row['pmin']} != 予想 {pred}"
                )
                exact += 1
            elif row["status"] == "pmin_lb":
                assert int(row["pmin"]) <= pred, (
                    f"cyl(2,{h}): 下界 {row['pmin']} が予想 {pred} を超えた（式が偽）"
                )
                lb += 1
    assert exact >= 17, f"等号で確認した点が {exact} 個しかない"
    # **`lb` の個数は要求しない。** U5b 時点では下界行が 1 つあり
    # `assert lb >= 1` と書いたが、U6b で cap を上げたら $h=17,18$ が
    # 等号で確定して下界行が消え、この検査だけが落ちた。
    # 下界行は「まだ届いていない」ことの記録であって、**減るのは前進**である。
    # 数学的な主張（等号・不等号）は上の 2 つの assert が持っている。
    assert lb >= 0


def test_bitrev_pmin_respects_de_rezende_et_al_upper_bound() -> None:
    """文献の上界と突き合わせる（KF-28。arXiv:2001.02481 Theorem 4.26 item 1）。

    「$2n$ 頂点のビット反転置換グラフの**可逆**ペブリング価は高々 $2\\log n+2$」。
    我々の `bitrev(k)` は $2\\cdot2^k$ 頂点なので上界は $2k+2$。
    実測は $p_{\\min}=2k+1$ で、**上界の 1 つ下**である（矛盾せず、かつ厳密なぶん鋭い）。

    ⚠️ この族が**可逆側で未研究だと書かないこと**。空間の上界と時空トレードオフは
    既にある。空白は厳密値の側だけである。
    """
    import csv

    from family_atlas import CSV_PATH

    checked = 0
    with CSV_PATH.open(encoding="utf-8", newline="") as fh:
        for row in csv.DictReader(fh):
            if row["family"] != "bitrev" or row["status"] != "exhaustive":
                continue
            if row["p"] != row["pmin"]:
                continue
            k = int(row["params"])
            pmin = int(row["pmin"])
            assert pmin <= 2 * k + 2, (
                f"BR_{k}: p_min={pmin} が文献の上界 {2 * k + 2} を超えた（実装かモデルが違う）"
            )
            assert pmin == 2 * k + 1, f"BR_{k}: p_min={pmin} が 2k+1 でない"
            checked += 1
    assert checked >= 4, f"検査した k が {checked} 個しかない"


def test_excess_is_zero_exactly_when_no_vertex_is_placed_three_times() -> None:
    """**超過 $E$ が 0 になるのは「どの頂点も高々 2 回」のとき、そのときに限る**（U10）。

    $$E := \\frac{M^* - (4N - 2\\min(p,N) - 1)}{2}$$

    は「2 回ずつの予算を超えて置いた回数」である（$M^*=2A-1$ より
    $E = A - (2N-\\min(p,N))$）。台帳の**全 `exhaustive` 行**で

        $E = 0 \\iff$ 正準な最適スケジュールの最大配置回数 $\\le 2$

    が成り立つ（反例ゼロ）。$p$ を 1 上げたときの $M^*$ の落差は、
    **この $E$ が減る量そのもの**である（`findings.md` §3.17）。

    ⚠️ 分布はスケジュール依存なので、固定されるのは
    「BFS の距離表から復元した正準な 1 本について」である。
    $M^*$ と $E$ のほうはスケジュールに依らない。
    """
    from family_atlas import read_rows

    checked = 0
    for row in read_rows():
        if row["status"] != "exhaustive":
            continue
        params = tuple(int(x) for x in row["params"].split(":"))
        p = int(row["p"])
        prof, n, m = placement_profile(row["family"], params, p)
        excess = (m - (4 * n - 2 * min(p, n) - 1)) // 2
        assert (excess == 0) == (max(prof) <= 2), (
            f"{row['family']}{params} p={p}: 超過 E={excess} だが最大回数 {max(prof)}"
        )
        assert excess >= 0, f"{row['family']}{params} p={p}: E={excess} が負（床を割った）"
        checked += 1
    assert checked >= 203, f"検査した行が {checked} 件しかない"


def test_once_count_equals_min_p_n_only_inside_the_regime() -> None:
    """$r=\\min(p,N)$ は**$\\le2$ 領域の性質**であって、領域外では破れうる（U10 の精密化）。

    U3d は $\\le2$ 領域で $r=\\min(p,N)$ を固定した。台帳全体で見ると
    203 行中 193 行で成り立ち、**破れる 10 行はすべて最大配置回数 $\\ge3$** である。
    つまり「$r=\\min(p,N)$ は領域内では常に成り立ち、領域外では保証されない」。
    """
    from family_atlas import read_rows

    outside_and_broken = 0
    for row in read_rows():
        if row["status"] != "exhaustive":
            continue
        params = tuple(int(x) for x in row["params"].split(":"))
        p = int(row["p"])
        prof, n, _m = placement_profile(row["family"], params, p)
        if prof[1] != min(p, n):
            assert max(prof) >= 3, (
                f"{row['family']}{params} p={p}: 高々 2 回なのに r={prof[1]} != min(p,N)={min(p, n)}"
            )
            outside_and_broken += 1
    assert outside_and_broken >= 10, f"破れた行が {outside_and_broken} 件しかない"


def test_A_is_determined_by_mstar() -> None:
    """$A=(M^*+1)/2$（$M^*=2A-1$ の言い換え）。分布に依らず成り立つ健全性検査。"""
    for k, p, hs in ARITHMETIC + BROKEN:
        for h in hs:
            prof, _n, m = placement_profile("cylinder", (k, h), p)
            a = sum(mult * cnt for mult, cnt in prof.items())
            assert 2 * a - 1 == m, f"cyl({k},{h}) p={p}: 2A-1={2 * a - 1} != M*={m}"


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


def test_cyl2_construction_verifies_and_bounds_pmin() -> None:
    """幅 2 円筒の構成が検証器を通り、上界 $2\\lceil\\log_2 h\\rceil+2$ を達成する（V2）。

    構成は「レベルを超頂点と見ると幅 2 円筒は長さ $h$ の鎖」という観察から、
    **鎖の最適スケジュールを持ち上げた**もの。鎖の $\\mathrm{reach}(P)=2^{P-1}$ は
    既知（KF-03）なので、この上界は**すべての $h$ について**従う。

    ⚠️ **実測の $p_{\\min}$ より 1 大きい。** 予想 $2\\lceil\\log_2 h\\rceil+1$ の
    上界側はこれでは閉じない。差がちょうど 1 であることを固定しておく
    （縮んだら、より良い構成が見つかったということ）。
    """
    import sys
    from pathlib import Path

    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
    from cyl2_construct import check, upper_bound

    from family_atlas import read_rows

    ledger = {
        int(r["params"].split(":")[1]): int(r["pmin"])
        for r in read_rows()
        if r["family"] == "cylinder"
        and r["status"] == "exhaustive"
        and r["params"].split(":")[0] == "2"
        and r["p"] == r["pmin"]
    }
    checked = 0
    for h in range(2, 25):
        r = check(h)  # 検証器を通らなければ AssertionError
        assert r["ok"], f"h={h}: {r.get('why')}"
        assert r["peak"] == upper_bound(h), f"h={h}: ピーク {r['peak']} != {upper_bound(h)}"
        if h in ledger:
            gap = r["peak"] - ledger[h]
            assert gap in (0, 1), f"h={h}: 実測との差が {gap}（0 か 1 のはず）"
            assert r["peak"] >= ledger[h], f"h={h}: 構成が実測の p_min を下回った"
        checked += 1
    assert checked == 23, f"検査した h が {checked} 個"
