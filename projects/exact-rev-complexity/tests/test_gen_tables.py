"""erasure-pebbling 論文の表 reach.tex の生成器の回帰テスト（テストファースト）。

査読 2026-09-18 の必須 1・2（出口台帳 X-erasure-pebbling-01）:
p=1 の行で LTV の保証 (e+1)2^{p-2} が厳密値 reach(1,e)=1 を上回る偽の値（2,3,4）を
印字していた。定理 B1 は p>=2、LTV Lemma 1 は p>=2 かつ e>=1 でしか主張されないので、
適用範囲外のセルは n/a にする。下界の列が厳密値を超えたら生成を止める。

    python3 tests/test_gen_tables.py
"""

from __future__ import annotations

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from gen_tables import main, reach, rows  # noqa: E402

NA = "n/a"


def body(tex: str) -> list[list[str]]:
    lines = tex.splitlines()
    start = lines.index(r"\midrule") + 1
    end = lines.index(r"\bottomrule")
    return [[c.strip() for c in ln.removesuffix(r"\\").split("&")] for ln in lines[start:end]]


def table() -> list[list[str]]:
    return body(reach())


def test_lower_bounds_never_exceed_exact_value() -> None:
    """下界の列（定理 B1・LTV）は厳密値 reach(p,e) を超えない。"""
    for p, e, r, ours, ltv in table():
        for cell in (ours, ltv):
            if cell != NA:
                assert int(cell) <= int(r), (p, e, r, ours, ltv)


def test_p1_rows_are_out_of_scope() -> None:
    """定理 B1 も LTV Lemma 1 も p>=2 の主張。p=1 の行は両方 n/a。"""
    got = [row for row in table() if row[0] == "1"]
    assert got, "p=1 の行が無い"
    for p, e, r, ours, ltv in got:
        assert r == "1", (p, e, r)
        assert ours == NA and ltv == NA, (p, e, ours, ltv)


def test_ltv_is_na_at_e0() -> None:
    """LTV Lemma 1 は e>=1 の主張（本文 Prop. ltv）。e=0 の LTV 欄は n/a。"""
    for p, e, r, ours, ltv in table():
        if e == "0":
            assert ltv == NA, (p, e, ltv)


def test_in_scope_cells_follow_closed_forms() -> None:
    n = 0
    for p, e, r, ours, ltv in table():
        p_, e_ = int(p), int(e)
        if p_ >= 2:
            assert ours == str((e_ + 2) * 2 ** (p_ - 2)), (p, e, ours)
            n += 1
        if p_ >= 2 and e_ >= 1:
            assert ltv == str((e_ + 1) * 2 ** (p_ - 2)), (p, e, ltv)
    assert n == 16, n  # p=2..5, e=0..3


def test_rows_cover_p1_to_5_e0_to_3() -> None:
    got = {(int(r[0]), int(r[1])) for r in table()}
    assert got == {(p, e) for p in range(1, 6) for e in range(4)}, sorted(got)


# --- 変異注入: 壊れた入力を拒否する ------------------------------------------


def _mutated(**patch) -> list[dict]:
    data = [dict(r) for r in rows("exp03_reach.csv")]
    for r in data:
        if (int(r["p"]), int(r["e"])) == patch["at"]:
            r[patch["col"]] = patch["val"]
    return data


def _raises(data: list[dict]) -> bool:
    try:
        reach(data)
    except (AssertionError, ValueError):
        return True
    return False


def test_rejects_reach_below_construction() -> None:
    """厳密値が定理 B1 の構成を下回るデータ（あり得ない）は拒否する。"""
    assert _raises(_mutated(at=(3, 1), col="reach", val="5"))  # 構成は 6


def test_rejects_csv_formula_disagreeing_with_closed_form() -> None:
    assert _raises(_mutated(at=(4, 2), col="formula", val="17"))


def test_accepts_unmutated_data() -> None:
    assert not _raises([dict(r) for r in rows("exp03_reach.csv")])


def test_main_writes_into_given_directory_only() -> None:
    with tempfile.TemporaryDirectory() as d:
        main(["--out", d])
        assert (Path(d) / "reach.tex").read_text() == reach()


def _run() -> int:
    tests = [(k, v) for k, v in globals().items() if k.startswith("test_") and callable(v)]
    bad = 0
    for name, fn in tests:
        try:
            fn()
            print(f"ok   {name}")
        except Exception as ex:  # noqa: BLE001
            bad += 1
            print(f"FAIL {name}: {type(ex).__name__}: {ex}")
    print(f"{len(tests) - bad}/{len(tests)} passed")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(_run())
