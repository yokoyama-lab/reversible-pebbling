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
