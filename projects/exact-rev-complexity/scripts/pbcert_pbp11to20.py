#!/usr/bin/env python3
"""Exact の **VeriPB 証明フォーマット 1.1** を **2.0** に書き換える（2026-09-05）。

**なぜ要るか（実測 2026-09-05）**: `~/dev/TOOLS.md` の **VeriPB 3.0.2 は
バージョン 2.0 と 3.0 の証明しか受理しない**（`veripb-parser/src/pbp_parser/parser.rs:402`
「Only proof version `3.0` (and `2.0`) are supported」）。一方、手元で唯一の
擬似ブール証明**生成器**である **Exact 2.2.1**（PyPI, 2025-07）が書くのは
**バージョン 1.1** である。そのままでは繋がらない。

**この変換器はごまかしにならない。** 変換に誤りがあれば VeriPB が**拒否**する側に倒れる
（受理される嘘は作れない）。ただしそれは、VeriPB に渡す OPB が我々の主張したい系である
ことが別に保証されている場合に限る —— その確認は `pbcert_measure.py` の
`formula ⊆ 我々の OPB` 検査が行う。

対応（1.1 → 2.0）:

| 1.1 | 2.0 | 備考 |
|---|---|---|
| `pseudo-Boolean proof version 1.1` | `pseudo-Boolean proof version 2.0` ＋ `f <n>` | `f` が式全体を読み込む |
| `l <i>` | （出力しない） | `f` が済ませているので id を対応づけるだけ |
| `rup <制約> ;` | `u <制約> ;` | |
| `pol <逆ポーランド>` | `p <逆ポーランド>` | 制約 id を張り替える |
| `c <id>` | `conclusion UNSAT : <id>` | |

**知らない規則が出たら止まる**（fail-closed）。黙って読み飛ばさない。
"""
from __future__ import annotations

import argparse
import sys


class TranslationError(Exception):
    pass


def _is_int(tok: str) -> bool:
    return tok.lstrip("-").isdigit()


def translate(src: str, n_formula: int) -> str:
    out: list[str] = ["pseudo-Boolean proof version 2.0", f"f {n_formula}"]
    v1_to_v2: dict[int, int] = {}
    next_v1 = 1
    next_v2 = n_formula + 1
    conclusion_v1: int | None = None

    for lineno, raw in enumerate(src.splitlines(), start=1):
        ln = raw.strip()
        if not ln:
            continue
        if lineno == 1:
            if not ln.startswith("pseudo-Boolean proof version 1."):
                raise TranslationError(f"1 行目が 1.x の見出しでない: {ln!r}")
            continue
        if ln.startswith("*"):                      # コメント
            out.append(ln)
            continue

        head, _, rest = ln.partition(" ")

        if head == "l":                             # 式からの読み込み
            i = int(rest.strip())
            if not 1 <= i <= n_formula:
                raise TranslationError(f"{lineno} 行: l {i} が式の範囲外（式は {n_formula} 本）")
            v1_to_v2[next_v1] = i
            next_v1 += 1

        elif head == "rup":                         # 逆単位伝播
            out.append(f"u {rest}")
            v1_to_v2[next_v1] = next_v2
            next_v1 += 1
            next_v2 += 1

        elif head in ("pol", "p"):                  # 切除平面（逆ポーランド）
            toks = rest.split()
            new: list[str] = []
            for i, tok in enumerate(toks):
                nxt = toks[i + 1] if i + 1 < len(toks) else None
                if _is_int(tok):
                    if nxt in ("*", "d"):           # 乗数・除数はスカラ。id ではない
                        new.append(tok)
                    else:
                        v1 = int(tok)
                        if v1 not in v1_to_v2:
                            raise TranslationError(
                                f"{lineno} 行: 未定義の制約 id {v1} を参照している")
                        new.append(str(v1_to_v2[v1]))
                elif tok.startswith("x") or tok.startswith("~x"):
                    new.append(tok)                 # リテラル公理
                elif tok in ("+", "*", "d", "s", "w"):
                    new.append(tok)
                else:
                    raise TranslationError(f"{lineno} 行: pol の中に知らない字句 {tok!r}")
            out.append("p " + " ".join(new))
            v1_to_v2[next_v1] = next_v2
            next_v1 += 1
            next_v2 += 1

        elif head == "c":                           # 矛盾（結論）
            conclusion_v1 = int(rest.strip())

        else:
            raise TranslationError(
                f"{lineno} 行: 知らない規則 {head!r}（fail-closed で停止する）: {ln[:60]!r}")

    out.append("output NONE")
    if conclusion_v1 is None:
        out.append("conclusion NONE")
    else:
        if conclusion_v1 not in v1_to_v2:
            raise TranslationError(f"結論が参照する id {conclusion_v1} が未定義")
        out.append(f"conclusion UNSAT : {v1_to_v2[conclusion_v1]}")
    out.append("end pseudo-Boolean proof")
    return "\n".join(out) + "\n"


def count_constraints(opb_path: str) -> int:
    n = 0
    for ln in open(opb_path):
        s = ln.strip()
        if s and not s.startswith("*") and not s.startswith("min:"):
            n += 1
    return n


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--proof", required=True, help="Exact が書いた 1.1 形式の証明")
    ap.add_argument("--formula", required=True, help="Exact が書いた OPB（制約数を数える）")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    n = count_constraints(a.formula)
    try:
        res = translate(open(a.proof).read(), n)
    except TranslationError as e:
        print(f"**変換できない**: {e}", file=sys.stderr)
        return 1
    open(a.out, "w").write(res)
    print(f"{a.out}: {len(res.splitlines())} 行 / {len(res)} バイト（式 {n} 制約）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
