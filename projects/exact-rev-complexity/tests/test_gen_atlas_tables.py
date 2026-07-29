"""JSSST レター（アトラス Phase 4）の表生成の回帰テスト。

**テストファースト**（`docs/82_jssst_letter_outline.md` §8-2）。表は手打ち禁止であり、
生成物が `data/atlas/*.csv` と findings の値を正確に再現することをここで固定する。

    python3 tests/test_gen_atlas_tables.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from gen_atlas_tables import (  # noqa: E402
    HEAD,
    baseline_table,
    category_table,
    scaling_table,
)


def body(tex: str) -> list[list[str]]:
    """tabular の本体行（\\midrule と \\bottomrule の間）をセルに分解する。"""
    lines = [ln.strip() for ln in tex.splitlines()]
    start = lines.index(r"\midrule") + 1
    end = lines.index(r"\bottomrule")
    out = []
    for ln in lines[start:end]:
        if not ln or ln.startswith("%") or ln.startswith("\\"):
            continue
        out.append([c.strip() for c in ln.removesuffix(r"\\").split("&")])
    return out


def spec_columns(tex: str) -> int:
    """\\begin{tabular}{...} の列指定から列数を数える。"""
    line = next(ln for ln in tex.splitlines() if ln.startswith(r"\begin{tabular}"))
    spec = line[line.index("{", len(r"\begin{tabular}")) + 1 : line.rindex("}")]
    return sum(1 for ch in spec if ch in "lcr")


# --- 表1: カテゴリ別（findings_phase1 §2 の値） -------------------------------


def test_category_table_matches_phase1_findings() -> None:
    got = {r[0]: r[1:] for r in body(category_table())}
    assert got["アルゴリズム"] == ["69", "159", "30/69", "26"], got["アルゴリズム"]
    assert got["単射関数"] == ["15", "94", "1/15", "19"], got["単射関数"]
    assert got["jana"] == ["7", "52", "2/7", "9"], got["jana"]
    assert got["メモ化"] == ["7", "279", "3/7", "46"], got["メモ化"]
    assert got["構造体"] == ["13", "7", "0/13", "17"], got["構造体"]


def test_category_table_covers_all_111_programs() -> None:
    """区分の本数の合計が母数 111 に一致する（取りこぼしの検出）。"""
    assert sum(int(r[1]) for r in body(category_table())) == 111


# --- 表2: スケーリング（findings_phase2 §1 の値） ----------------------------


def test_scaling_table_reproduces_measured_series() -> None:
    got = {r[0]: r[1:] for r in body(scaling_table())}
    # 列は 族 & steps 列 & 隣接比 & stack_peak
    fib = got[r"fib\_iter"]
    assert fib[0].startswith("25") and fib[0].endswith("125"), fib
    assert fib[1] == r"1.80 $\to$ 1.19", fib
    # 急成長群: 隣接比が 4.00 に張り付く
    assert got["factorial"][1] == r"4.48 $\to$ 4.00", got["factorial"]
    # スタック等式の 2 件は最終点の値がそのまま読める
    assert got[r"gcd\_fib"][2].endswith("14"), got[r"gcd\_fib"]      # = k (n=14)
    assert got[r"bubble\_sort"][2].endswith("91"), got[r"bubble\_sort"]  # = n(n-1)/2, n=14


def test_scaling_table_has_all_nine_families() -> None:
    assert len(body(scaling_table())) == 9


# --- 表3: 基準線（findings_phase3 §1 の主表） --------------------------------


def test_baseline_table_matches_phase3_main_table() -> None:
    got = {r[0]: r[1:] for r in body(baseline_table())}
    # family, n, N, 床 2N-1, M*, p_min, 実装の手数, 実装のピーク
    assert got[r"fib\_pairs"] == ["13", "7", "13", "19", "4", "7", "7"], got[r"fib\_pairs"]
    assert got[r"edit\_distance"] == ["5", "25", "49", "117", "10", "35", "35"]
    assert got["lcs"] == ["5", "25", "49", "117", "10", "24", "24"]
    assert got["knapsack"] == ["3", "18", "35", "17", "5", "13", "13"]


def test_baseline_table_flags_invalid_cutrod_row() -> None:
    """cutrod はモデル対応が無効（impl peak 10 < p_min 14）。印を付けて残す。"""
    rows = body(baseline_table())
    cut = next(r for r in rows if r[0].startswith(r"cutrod\_linear"))
    assert r"$\dagger$" in cut[0], cut
    assert cut[1:] == ["14", "14", "27", "27", "14", "1246", "10"], cut
    assert rows[-1] is cut or rows.index(cut) == len(rows) - 1, "無効行は最後に置く"


def test_baseline_table_is_one_row_per_family_at_largest_n() -> None:
    rows = body(baseline_table())
    assert len(rows) == 5, rows


# --- 全表に共通の規約 ---------------------------------------------------------


def test_all_tables_are_marked_generated() -> None:
    for tex in (category_table(), scaling_table(), baseline_table()):
        assert tex.startswith(HEAD), tex[:80]


def test_all_tables_have_consistent_column_counts() -> None:
    for name, tex in [
        ("category", category_table()),
        ("scaling", scaling_table()),
        ("baseline", baseline_table()),
    ]:
        n = spec_columns(tex)
        for row in body(tex):
            assert len(row) == n, (name, n, row)


def test_underscores_are_escaped() -> None:
    """族名の `_` を生で出すと platex が落ちる。

    コメント行と数式（`$...$` の中の下付き）は対象外。
    """
    for tex in (category_table(), scaling_table(), baseline_table()):
        for line in tex.splitlines():
            if line.startswith("%"):
                continue
            text = "".join(seg for i, seg in enumerate(line.split("$")) if i % 2 == 0)
            for i, ch in enumerate(text):
                if ch == "_":
                    assert i and text[i - 1] == "\\", line


def test_headers_are_japanese_not_raw_column_names() -> None:
    """和文論文の表なので，見出しに CSV の列名（impl 等）を残さない。"""
    for tex in (category_table(), scaling_table(), baseline_table()):
        header = tex.splitlines()[3]
        assert "impl" not in header, header


def test_no_em_dash_in_output() -> None:
    """`---` は全言語の原稿で禁止（overleaf/CLAUDE.md）。"""
    for tex in (category_table(), scaling_table(), baseline_table()):
        assert "---" not in tex


if __name__ == "__main__":
    failures = 0
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            try:
                fn(); print(f"ok   {name}")
            except AssertionError as exc:
                failures += 1; print(f"FAIL {name}: {exc}")
            except Exception as exc:
                failures += 1; print(f"ERROR {name}: {type(exc).__name__}: {exc}")
    sys.exit(1 if failures else 0)
