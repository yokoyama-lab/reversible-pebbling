"""既知事実の台帳（`docs/22_known_facts_ledger.md`）と候補ファイルの整合を強制する。

台帳は**探索の負のフィルタ**なので、腐ると害になる（既知を新規と誤認する）。
そこで書式・ID の実在・候補側からの参照を機械で保つ。

    python3 tests/test_known_facts.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

DOCS = Path(__file__).resolve().parents[1] / "docs"
LEDGER = DOCS / "22_known_facts_ledger.md"

#: 1 件のブロックに必ずある欄
REQUIRED = ("種別", "主張", "出典", "一次確認", "含意", "関係候補")
#: 種別に使ってよい語（`docs/22` の表と一致させる）
KINDS = {"既知", "注意", "要確認"}


def blocks() -> dict[str, dict[str, str]]:
    """`### KF-NN — 見出し` ごとに欄を辞書化する。"""
    text = LEDGER.read_text(encoding="utf-8")
    out: dict[str, dict[str, str]] = {}
    parts = re.split(r"^### (KF-\d+) — (.+)$", text, flags=re.M)
    for i in range(1, len(parts), 3):
        kid, title, body = parts[i], parts[i + 1], parts[i + 2]
        # 欄は複数行にまたがる（続きは 2 スペース字下げ）。1 行目だけ見ると
        # 出典の書誌が途中で切れるので、続きを連結してから判定する。
        fields: dict[str, str] = {}
        current: str | None = None
        for line in body.splitlines():
            m = re.match(r"- \*\*(\w+?)\*\*: (.*)$", line)
            if m:
                current = m.group(1)
                fields[current] = m.group(2)
            elif current and line.startswith("  ") and line.strip():
                fields[current] += " " + line.strip()
            elif not line.strip():
                current = None
        fields["_title"] = title.strip()
        out[kid] = fields
    return out


def idea_files() -> list[Path]:
    return sorted(DOCS.glob("idea??_*.md"))


def refs_of(path: Path) -> set[str]:
    """候補ファイルが宣言している KF の ID。"""
    text = path.read_text(encoding="utf-8")
    m = re.search(r"探索前に必読.*?$", text, flags=re.M | re.S)
    if not m:
        return set()
    head = m.group(0).split("\n\n")[0]
    return set(re.findall(r"KF-\d+", head))


# --- 台帳そのものの健全性 ------------------------------------------------------


def test_ledger_has_entries() -> None:
    assert len(blocks()) >= 20, len(blocks())


def test_every_block_has_required_fields() -> None:
    for kid, f in blocks().items():
        missing = [k for k in REQUIRED if k not in f]
        assert not missing, (kid, missing)


def test_kinds_are_from_the_documented_set() -> None:
    for kid, f in blocks().items():
        assert f["種別"] in KINDS, (kid, f["種別"])


def test_ids_are_unique_and_contiguous() -> None:
    ids = sorted(int(k.split("-")[1]) for k in blocks())
    assert len(ids) == len(set(ids)), ids
    assert ids == list(range(1, len(ids) + 1)), ids


def test_unverified_entries_are_marked_要確認() -> None:
    """一次確認が「未」なら種別は 要確認 でなければならない。

    未確認のものを「既知」と書くと、正しい主張を誤って棄却する。
    """
    for kid, f in blocks().items():
        if f["一次確認"].startswith("未"):
            assert f["種別"] == "要確認", (kid, f["種別"], f["一次確認"])


def test_known_entries_cite_a_source() -> None:
    """種別が 既知 なら出典は具体的でなければならない（未特定は不可）。"""
    for kid, f in blocks().items():
        if f["種別"] == "既知":
            assert "未特定" not in f["出典"], (kid, f["出典"])
            assert re.search(r"\d{4}", f["出典"]), (kid, f["出典"])


# --- 候補ファイルとの整合 ------------------------------------------------------


def test_every_idea_declares_known_facts() -> None:
    """全候補が「探索前に必読」の参照行を持つ（撤退済みの候補も持つ）。"""
    for p in idea_files():
        assert refs_of(p), p.name


def test_declared_ids_exist_in_the_ledger() -> None:
    known = set(blocks())
    for p in idea_files():
        unknown = refs_of(p) - known
        assert not unknown, (p.name, sorted(unknown))


def test_ledger_related_candidates_match_idea_references() -> None:
    """台帳の「関係候補」と候補ファイル側の宣言が双方向で一致する。

    片側だけ更新すると負のフィルタに穴が開くので，両方向を検査する。
    """
    ledger = blocks()
    for p in idea_files():
        num = int(re.match(r"idea(\d+)_", p.name).group(1))
        declared = refs_of(p)
        for kid, f in ledger.items():
            listed = {int(x) for x in re.findall(r"\d+", f["関係候補"])}
            if num in listed:
                assert kid in declared, f"{p.name} が {kid} を宣言していない"
            else:
                assert kid not in declared, f"{p.name} の {kid} が台帳の関係候補に無い"


def test_all_ten_candidates_are_covered() -> None:
    assert len(idea_files()) == 10, [p.name for p in idea_files()]


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
