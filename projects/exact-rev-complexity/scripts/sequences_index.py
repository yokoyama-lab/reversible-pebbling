"""リポジトリ内の**厳密値の表**を全部拾って数列の一覧にする。

出力: `data/sequences_index.md`（自動生成・手編集禁止）

## なぜ必要か

厳密値の表は `data/atlas/*.csv`・`data/families/*.csv`・`data/exp*.csv`・`tests/` に
散在しており、**どれが厳密でどれが上界・打ち切りかが表ごとに違う列で表現されている**。
混ぜて数列にすると、打ち切り値を結果と読む事故（`~/.claude` の記憶
`cutoff-reading-as-result`）が起きる。ここで一度に集め、**種別を明示**する。

## 種別（kind）

| kind | 意味 | 数列に使ってよいか |
|---|---|---|
| `exact` | 全数探索・最適性が確定 | ✅ |
| `upper` | 上界のみ（構成が見つかっただけ） | ❌ |
| `lower` | 下界のみ | ❌ |
| `cutoff` | 打ち切り（timeout / cap に当たった） | ❌ |

**`exact` だけを OEIS 照合と holonomic guessing に回す。**
さらに、添字が飛んでいる数列は「最小添字からの連続部分」だけを採る
（飛びを詰めると別の数列になってしまうため）。

    python3 scripts/sequences_index.py          # data/sequences_index.md を生成
    python3 scripts/sequences_index.py --list   # 一覧だけ標準出力へ
"""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from dataclasses import dataclass, asdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

DATA = ROOT / "data"


@dataclass
class Seq:
    key: str
    title: str
    source: str
    index_name: str
    index_from: int
    values: list[int]
    kind: str
    category: str          # optimum / measurement / known / bb
    note: str = ""
    dropped: int = 0       # 連続性のために落とした項数
    already: bool = False  # 既に holonomic_guess.md で扱われているか
    closed: bool = False   # 切片が閉じている（次の添字は別の切片に属する）

    @property
    def n(self) -> int:
        return len(self.values)


def _contiguous(pairs: list[tuple[int, int]]) -> tuple[int, list[int], int]:
    """(index, value) の列から、最小添字からの連続部分を取り出す。"""
    if not pairs:
        return 0, [], 0
    pairs = sorted(pairs)
    start = pairs[0][0]
    vals = [pairs[0][1]]
    i = 1
    while i < len(pairs) and pairs[i][0] == start + len(vals):
        vals.append(pairs[i][1])
        i += 1
    return start, vals, len(pairs) - len(vals)


# ---------------------------------------------------------------------------
# 収集器


def from_families_atlas() -> list[Seq]:
    """data/families/atlas.csv — 族 × p オフセットごとの M*。status で種別を決める。"""
    path = DATA / "families" / "atlas.csv"
    if not path.exists():
        return []
    rows = list(csv.DictReader(path.open()))
    out: list[Seq] = []
    # params を整数添字に落とす（族ごとに規約が違う）
    def idx_of(fam: str, params: str) -> tuple[str, int] | None:
        if fam == "bitrev":
            return ("k", int(params))
        if fam == "cylinder":            # "幅:長さ"
            a, b = params.split(":")
            return (f"k[w={a}]", int(b))
        if fam == "kary_tree":           # "arity:height"
            a, b = params.split(":")
            return (f"h[ary={a}]", int(b))
        return None

    groups: dict[tuple[str, str, int], list[tuple[int, int, str]]] = {}
    for r in rows:
        fam = r["family"]
        got = idx_of(fam, r["params"])
        if got is None:
            continue
        iname, i = got
        try:
            off = int(r["p"]) - int(r["pmin"])
            v = int(r["mstar"])
        except (ValueError, KeyError):
            continue
        groups.setdefault((fam, iname, off), []).append((i, v, r["status"]))

    for (fam, iname, off), items in sorted(groups.items()):
        kinds = {s for _, _, s in items}
        exact_items = [(i, v) for i, v, s in items if s == "exhaustive"]
        start, vals, dropped = _contiguous(exact_items)
        if len(vals) < 3:
            continue
        kind = "exact"
        note = ""
        if kinds - {"exhaustive"}:
            note = f"同じ族に {sorted(kinds - {'exhaustive'})} の行があるが除外した"
        out.append(Seq(
            key=f"fam:{fam}:{iname}:off{off}",
            title=f"{fam} ({iname}) の $M^*(p_{{\\min}}+{off})$",
            source="data/families/atlas.csv",
            index_name=iname, index_from=start, values=vals,
            kind=kind, category="optimum", note=note, dropped=dropped,
        ))
    return out


def from_families_pmin_slices() -> list[Seq]:
    """`data/families/atlas.csv` にも $p_{\\min}$ 固定の切片を作る。

    2026-08-11: `fam:cylinder:k[w=2]:off2` の末尾パターン予想が k=17 で反証された。
    原因は **k=17 で $p_{\\min}$ が 9→11 に上がったこと**であり、
    段差をまたぐ数列を 1 本の数列として扱っていたのが誤りだった。
    `exp04_*` と同じく、ここでも切片に割る。
    """
    path = DATA / "families" / "atlas.csv"
    if not path.exists():
        return []
    rows = [r for r in csv.DictReader(path.open()) if r.get("status") == "exhaustive"]
    groups: dict[tuple[str, str, int, int], list[tuple[int, int]]] = {}
    for r in rows:
        fam, params = r["family"], r["params"]
        try:
            pm, p = int(r["pmin"]), int(r["p"])
            v = int(r["mstar"])
        except (ValueError, KeyError):
            continue
        off = p - pm
        if fam == "bitrev":
            iname, i = "k", int(params)
        elif fam == "cylinder":
            a, b = params.split(":")
            iname, i = f"k[w={a}]", int(b)
        elif fam == "kary_tree":
            a, b = params.split(":")
            iname, i = f"h[ary={a}]", int(b)
        else:
            continue
        groups.setdefault((fam, iname, off, pm), []).append((i, v))
    out: list[Seq] = []
    allp: dict[tuple[str, str, int], list[int]] = {}
    for (fam, iname, off, pm) in groups:
        allp.setdefault((fam, iname, off), []).append(pm)
    for (fam, iname, off, pm), items in sorted(groups.items()):
        start, vals, dropped = _contiguous(items)
        if len(vals) < 4:
            continue
        closed = any(q > pm for q in allp[(fam, iname, off)])
        out.append(Seq(
            key=f"slice:fam:{fam}:{iname}:off{off}:p{pm}",
            title=f"{fam} ({iname}) の $M^*(p_{{\\min}}+{off})$ の "
                  f"$p_{{\\min}}={pm}$ 切片",
            source="data/families/atlas.csv", index_name=iname,
            index_from=start, values=vals, kind="exact", category="optimum",
            dropped=dropped, closed=closed,
            note=f"$p_{{\\min}}={pm}$ の区間だけ"
                 + ("。**閉じている**" if closed else "。まだ開いている")))
    return out


def from_families_cpsat() -> list[Seq]:
    """data/families/cpsat.csv — OPTIMAL かつ cap に当たっていないものだけ exact。"""
    path = DATA / "families" / "cpsat.csv"
    if not path.exists():
        return []
    rows = list(csv.DictReader(path.open()))
    n_opt = sum(1 for r in rows if r["status"] == "OPTIMAL" and r["cap_tight"] == "0")
    n_cut = sum(1 for r in rows if r["cap_tight"] == "1")
    n_unk = sum(1 for r in rows if r["status"] == "UNKNOWN")
    return [Seq(
        key="cpsat:summary", title="（CP-SAT の M*: 数列化せず内訳のみ）",
        source="data/families/cpsat.csv", index_name="-", index_from=0, values=[],
        kind="mixed", category="optimum",
        note=f"OPTIMAL かつ cap 非到達 {n_opt} 行 / **cap 到達 {n_cut} 行（打ち切り）** / "
             f"UNKNOWN {n_unk} 行。BFS 側（families/atlas.csv）と重複するので数列には使わない",
    )]


def from_simple_tree_csv() -> list[Seq]:
    """exp01_trees / exp04_fib / exp04_grid / exp04_pascal — name(param) 形式。"""
    specs = [
        ("data/exp01_trees.csv", "chain", r"chain\((\d+)\)", "n", "鎖"),
        ("data/exp01_trees.csv", "cbt", r"cbt\((\d+)\)", "h", "完全二分木"),
        ("data/exp01_trees.csv", "pyramid", r"pyramid\((\d+)\)", "h", "ピラミッド"),
        ("data/exp01_trees.csv", "spinal", r"spinal\((\d+)\)", "k", "spinal tree"),
        ("data/exp04_fib.csv", "fib", r"fib\((\d+)\)", "n", "Fibonacci 型メモ化 DAG"),
        ("data/exp04_pascal.csv", "pascal", r"pascal\((\d+)\)", "n", "Pascal 型メモ化 DAG"),
    ]
    cols = [("M*_p_min+0", "p_{\\min}"), ("M*_p_min+1", "p_{\\min}+1"),
            ("M*_p_min+2", "p_{\\min}+2")]
    out: list[Seq] = []
    for rel, tag, pat, iname, label in specs:
        path = ROOT / rel
        if not path.exists():
            continue
        rows = list(csv.DictReader(path.open()))
        rx = re.compile("^" + pat + "$")
        for col, clabel in cols:
            items: list[tuple[int, int]] = []
            for r in rows:
                m = rx.match(r.get("name", "").strip('"'))
                if not m:
                    continue
                v = r.get(col, "")
                if not v or v == "None":
                    continue
                items.append((int(m.group(1)), int(v)))
            start, vals, dropped = _contiguous(items)
            if len(vals) < 4:
                continue
            out.append(Seq(
                key=f"{tag}:{col}",
                title=f"{label}の $M^*({clabel})$",
                source=rel, index_name=iname, index_from=start, values=vals,
                kind="exact", category="optimum", dropped=dropped,
                note="$p_{\\min}$ の段差で区分的になりうる（値が減る点に注意）",
            ))
    return out


def from_fixed_pmin_slices() -> list[Seq]:
    """**$p_{\\min}$ が一定の区間だけを切り出した数列**。

    `scripts/exp_guess_sequences.py` の設計メモが指摘しているとおり、
    $M^*(G, p_{\\min})$ は $p_{\\min}$ が上がる位置で**不連続に落ちる**ので、
    単一の漸化式が成り立つ理由が無い。$p_{\\min}$ を固定した切片のほうが自然な候補である。
    ここでは `p_min` 列を持つ表から、その切片を機械的に取り出す。
    """
    specs = [
        ("data/exp01_trees.csv", "chain", r"chain\((\d+)\)", "n", "鎖"),
        ("data/exp01_trees.csv", "cbt", r"cbt\((\d+)\)", "h", "完全二分木"),
        ("data/exp01_trees.csv", "pyramid", r"pyramid\((\d+)\)", "h", "ピラミッド"),
        ("data/exp01_trees.csv", "spinal", r"spinal\((\d+)\)", "k", "spinal tree"),
        ("data/exp04_fib.csv", "fib", r"fib\((\d+)\)", "n", "Fibonacci 型メモ化 DAG"),
        ("data/exp04_pascal.csv", "pascal", r"pascal\((\d+)\)", "n", "Pascal 型メモ化 DAG"),
    ]
    cols = [("M*_p_min+0", "p_{\\min}"), ("M*_p_min+1", "p_{\\min}+1"),
            ("M*_p_min+2", "p_{\\min}+2")]
    out: list[Seq] = []
    for rel, tag, pat, iname, label in specs:
        path = ROOT / rel
        if not path.exists():
            continue
        rows = list(csv.DictReader(path.open()))
        rx = re.compile("^" + pat + "$")
        for col, clabel in cols:
            byp: dict[int, list[tuple[int, int]]] = {}
            for r in rows:
                m = rx.match(r.get("name", "").strip('"'))
                if not m or r.get("p_min") in ("", None):
                    continue
                v = r.get(col, "")
                if not v or v == "None":
                    continue
                byp.setdefault(int(r["p_min"]), []).append((int(m.group(1)), int(v)))
            pmins = sorted(byp)
            for pmin, items in sorted(byp.items()):
                start, vals, dropped = _contiguous(items)
                if len(vals) < 5:
                    continue
                # 後ろに別の p_min の切片があるなら、この切片は閉じている
                closed = any(q > pmin for q in pmins)
                out.append(Seq(
                    key=f"slice:{tag}:{col}:p{pmin}",
                    title=f"{label}の $M^*({clabel})$ の $p_{{\\min}}={pmin}$ 切片",
                    source=rel, index_name=iname, index_from=start, values=vals,
                    kind="exact", category="optimum", dropped=dropped,
                    closed=closed,
                    note=f"$p_{{\\min}}={pmin}$ が続く区間だけを取り出した"
                         "（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）"
                         + ("。**この切片は閉じている**（次の添字は別の $p_{\\min}$ に属する）"
                            "ので、次の 1 点を計算しても検証にならない" if closed else "")))
    return out


def from_butterfly_saturation() -> list[Seq]:
    out: list[Seq] = []
    p = DATA / "exp01b_butterfly.csv"
    if p.exists():
        rows = list(csv.DictReader(p.open()))
        for col, label in [("M*_p0", "p_{\\min}"), ("M*_p1", "p_{\\min}+1"),
                           ("M*_p2", "p_{\\min}+2")]:
            items = [(int(r["k"]), int(r[col])) for r in rows
                     if r.get(col) not in ("", "None", None)]
            start, vals, dropped = _contiguous(items)
            if len(vals) >= 4:
                out.append(Seq(
                    key=f"butterfly:{col}", title=f"バタフライの $M^*({label})$",
                    source="data/exp01b_butterfly.csv", index_name="k",
                    index_from=start, values=vals, kind="exact",
                    category="optimum", dropped=dropped))
    p = DATA / "exp01b_saturation.csv"
    if p.exists():
        rows = list(csv.DictReader(p.open()))
        for col, label in [("M*_p_min", "M^*(p_{\\min})"), ("p_min", "p_{\\min}")]:
            items = [(int(r["k"]), int(r[col])) for r in rows
                     if r.get(col) not in ("", "None", None)]
            start, vals, dropped = _contiguous(items)
            if len(vals) >= 4:
                out.append(Seq(
                    key=f"saturation:{col}", title=f"飽和族の ${label}$",
                    source="data/exp01b_saturation.csv", index_name="k",
                    index_from=start, values=vals, kind="exact",
                    category="optimum", dropped=dropped))
    return out


def from_reach() -> list[Seq]:
    """exp03_reach.csv — reach(p,e)。**定理 B2 で閉形式が確定済み**（対照用）。"""
    path = DATA / "exp03_reach.csv"
    if not path.exists():
        return []
    rows = list(csv.DictReader(path.open()))
    out: list[Seq] = []
    for e in sorted({int(r["e"]) for r in rows}):
        items = [(int(r["p"]), int(r["reach"])) for r in rows if int(r["e"]) == e]
        start, vals, dropped = _contiguous(items)
        if len(vals) >= 4:
            out.append(Seq(
                key=f"reach:e{e}", title=f"$\\mathrm{{reach}}(p, e={e})$",
                source="data/exp03_reach.csv", index_name="p", index_from=start,
                values=vals, kind="exact", category="known", dropped=dropped,
                note="**閉形式は確定済み**（定理 B2 $=(e+2)2^{p-2}$、"
                     "`lean/Revgarbage/PebbleB1.lean` で機械証明）。健全性の対照に使う"))
    return out


def from_pmin_e() -> list[Seq]:
    path = DATA / "exp03_pmin_e.csv"
    if not path.exists():
        return []
    rows = list(csv.DictReader(path.open()))
    out: list[Seq] = []
    for e in sorted({int(r["e"]) for r in rows}):
        items = [(int(r["n"]), int(r["p_min_e"])) for r in rows if int(r["e"]) == e]
        start, vals, dropped = _contiguous(items)
        if len(vals) >= 4:
            out.append(Seq(
                key=f"pmin_e:e{e}", title=f"$p_{{\\min}}(n, e={e})$",
                source="data/exp03_pmin_e.csv", index_name="n", index_from=start,
                values=vals, kind="exact", category="optimum", dropped=dropped))
    return out


def from_atlas_scaling() -> list[Seq]:
    """atlas/scaling.csv — 実プログラムの実測（**最適値ではない**）。"""
    path = DATA / "atlas" / "scaling.csv"
    if not path.exists():
        return []
    rows = [r for r in csv.DictReader(path.open()) if not r.get("error")]
    out: list[Seq] = []
    for fam in sorted({r["family"] for r in rows}):
        for col in ("steps", "stack_peak", "final_live_bits"):
            items = [(int(r["n"]), int(r[col])) for r in rows
                     if r["family"] == fam and r.get(col) not in ("", None)]
            start, vals, dropped = _contiguous(items)
            if len(vals) >= 5 and len(set(vals)) > 1:
                out.append(Seq(
                    key=f"scaling:{fam}:{col}", title=f"{fam} の {col}",
                    source="data/atlas/scaling.csv", index_name="n",
                    index_from=start, values=vals, kind="exact",
                    category="measurement", dropped=dropped,
                    note="**実プログラムの実測値であって最適値ではない**。"
                         "閉形式が出ても『そのプログラムの計算量』の主張にしかならない"))
    return out


def from_atlas_baselines() -> list[Seq]:
    path = DATA / "atlas" / "baselines.csv"
    if not path.exists():
        return []
    rows = [r for r in csv.DictReader(path.open()) if not r.get("error")]
    out: list[Seq] = []
    for fam in sorted({r["family"] for r in rows}):
        for col, kind, cat in (("mstar", "exact", "optimum"),
                               ("floor", "lower", "optimum"),
                               ("impl_moves", "upper", "measurement")):
            items = []
            for r in rows:
                if r["family"] != fam:
                    continue
                v = r.get(col, "")
                if v in ("", None, "None"):
                    continue
                items.append((int(r["n"]), int(v)))
            start, vals, dropped = _contiguous(items)
            if len(vals) >= 4 and len(set(vals)) > 1:
                out.append(Seq(
                    key=f"baseline:{fam}:{col}", title=f"{fam} の {col}",
                    source="data/atlas/baselines.csv", index_name="n",
                    index_from=start, values=vals, kind=kind,
                    category=cat, dropped=dropped))
    return out


def _extended_points() -> dict[str, list[tuple[int, int]]]:
    """`scripts/extend_sequences.py` が計算した追加点（key → [(添字, 値)]）。

    `off{k}` を含む非切片キーからは、記録された `p` 列を使って
    **切片キーも合成する**（$p_{\\min} = p - \text{off}$）。
    こうしておかないと「新しい $p_{\\min}$ の点は計算したのに、
    前の切片が閉じたことに気づかない」という取りこぼしが起きる
    （2026-08-11 に `cylinder off2:p9` で実際に起きた）。
    """
    path = DATA / "sequences_extended.csv"
    out: dict[str, list[tuple[int, int]]] = {}
    if not path.exists():
        return out
    for r in csv.DictReader(path.open()):
        try:
            idx, val = int(r["index"]), int(r["value"])
        except (ValueError, KeyError):
            continue
        key = r["key"]
        out.setdefault(key, []).append((idx, val))
        if not key.startswith("slice:") and ":off" in key:
            try:
                off = int(key.rsplit(":off", 1)[1])
                pmin = int(r["p"]) - off
            except (ValueError, KeyError, IndexError):
                continue
            out.setdefault(f"slice:{key}:p{pmin}", []).append((idx, val))
    return out


def merge_extended(seqs: list[Seq]) -> list[Seq]:
    """表から作った数列に、計算で足した点を合流させる。

    **同じ添字の値が食い違ったら合流しない**（どちらかが誤りなので、黙って上書きしない）。
    """
    ext = _extended_points()
    if not ext:
        return seqs
    by_key = {s.key: s for s in seqs}
    # 追加計算で新しい p_min の切片が見つかったら、前の切片は閉じたと分かる
    for key in list(ext):
        if not key.startswith("slice:"):
            continue
        head, _, ptag = key.rpartition(":p")
        if not ptag.isdigit():
            continue
        q = int(ptag)
        for s in seqs:
            if not s.key.startswith(head + ":p"):
                continue
            try:
                mine = int(s.key.rsplit(":p", 1)[1])
            except (IndexError, ValueError):
                continue
            if mine < q and not s.closed:
                s.closed = True
                s.note += ("  （追加計算で $p_{\\min}$ の次の段が見つかったので、"
                           "**この切片は閉じている**）")
    # 追加計算だけで存在する切片（表にはまだ無い新しい p_min の切片）を作る
    for key, pts in ext.items():
        if key in by_key or not key.startswith("slice:"):
            continue
        start, vals, dropped = _contiguous(sorted(pts))
        if len(vals) < 2:
            continue
        tag = key.rsplit(":p", 1)[1] if ":p" in key else "?"
        fam = key.split(":")[1] if len(key.split(":")) > 1 else "?"
        newseq = Seq(
            key=key, title=f"{fam} の {key.split(':')[2]} の $p_{{\\min}}={tag}$ 切片",
            source="data/sequences_extended.csv（追加計算）", index_name="n",
            index_from=start, values=vals, kind="exact", category="optimum",
            dropped=dropped,
            note="**追加計算だけで得た新しい切片**（表にはまだ無い）")
        seqs.append(newseq)
        by_key[key] = newseq
    for key, pts in ext.items():
        s = by_key.get(key)
        if s is None:
            continue
        base = {s.index_from + i: v for i, v in enumerate(s.values)}
        conflict = [(i, v, base[i]) for i, v in pts if i in base and base[i] != v]
        if conflict:
            s.note += (f"  ⚠ 追加計算と表の値が食い違う: {conflict[:3]} → 合流しない")
            continue
        base.update(dict(pts))
        start, vals, dropped = _contiguous(sorted(base.items()))
        added = len(vals) - s.n
        if added > 0:
            s.values = vals
            s.index_from = start
            s.dropped = dropped
            s.note += f"  （`scripts/extend_sequences.py` で {added} 点を追加計算）"
    return seqs


def from_hardcoded() -> list[Seq]:
    """`scripts/exp_guess_sequences.py` が既に持っている出典つき数列。"""
    from exp_guess_sequences import SEQUENCES  # noqa: PLC0415
    out: list[Seq] = []
    for i, (title, seq, prov) in enumerate(SEQUENCES):
        cat = "bb" if "BB" in title or "Sigma" in title or "\\Sigma" in title else "optimum"
        known = "既知値" in prov
        out.append(Seq(
            key=f"hard:{i}", title=title, source="scripts/exp_guess_sequences.py",
            index_name="n", index_from=1, values=seq,
            kind="exact", category="known" if known else cat,
            note=prov, already=True))
    return out


COLLECTORS = [
    from_hardcoded, from_families_atlas, from_families_pmin_slices,
    from_families_cpsat, from_simple_tree_csv,
    from_fixed_pmin_slices, from_butterfly_saturation, from_reach, from_pmin_e,
    from_atlas_scaling, from_atlas_baselines,
]


def all_sequences() -> list[Seq]:
    out: list[Seq] = []
    for c in COLLECTORS:
        try:
            out.extend(c())
        except Exception as exc:  # noqa: BLE001
            print(f"  ⚠ 収集器 {c.__name__} が失敗: {exc}", file=sys.stderr)
    return merge_extended(out)


def exact_sequences(min_terms: int = 4) -> list[Seq]:
    return [s for s in all_sequences()
            if s.kind == "exact" and s.n >= min_terms]


# ---------------------------------------------------------------------------


def render(seqs: list[Seq]) -> str:
    L = ["# 厳密値の数列 索引（自動生成・手編集禁止）", "",
         "生成: `python3 scripts/sequences_index.py`", "",
         "**種別**: `exact`=全数探索で最適性が確定 / `upper`=上界のみ / "
         "`lower`=下界のみ / `cutoff`=打ち切り / `mixed`=混在。",
         "**`exact` だけ**を OEIS 照合（`scripts/oeis_check.py`）と "
         "holonomic guessing（`scripts/conjecture_queue.py`）に回す。", "",
         "添字に飛びがある表は**最小添字からの連続部分だけ**を採った"
         "（`落` 列がその際に捨てた点数）。", ""]
    kinds = {}
    for s in seqs:
        kinds.setdefault(s.kind, 0)
        kinds[s.kind] += 1
    L.append(f"**要約**: {len(seqs)} 本（" +
             " / ".join(f"{k} {v}" for k, v in sorted(kinds.items())) + "）。"
             f"うち `exact` かつ 4 項以上が {len(exact_sequences())} 本。")
    L.append("")
    for cat, label in [("optimum", "最適値（$M^*$・$p_{\\min}$ など）"),
                       ("known", "閉形式が既知／既知値の再現（対照）"),
                       ("bb", "可逆 Busy Beaver"),
                       ("measurement", "実プログラムの実測（最適値ではない）")]:
        rows = [s for s in seqs if s.category == cat]
        if not rows:
            continue
        L += [f"## {label}", "",
              "| key | 数列 | 出典 | 添字 | 項数 | 種別 | 落 | 先頭 |",
              "|---|---|---|---|---:|---|---:|---|"]
        for s in sorted(rows, key=lambda x: (-x.n, x.key)):
            head = ", ".join(str(v) for v in s.values[:8])
            if s.n > 8:
                head += ", …"
            mark = "★" if s.already else ""
            L.append(f"| `{s.key}`{mark} | {s.title} | `{s.source}` | "
                     f"{s.index_name} から {s.index_from} | {s.n} | {s.kind} | "
                     f"{s.dropped} | {head} |")
        L.append("")
    L += ["★ = `data/holonomic_guess.md` で既に扱っている数列。", "",
          "## 数列に使わなかったもの（注意書き）", ""]
    for s in seqs:
        if s.kind != "exact" and s.note:
            L.append(f"- **{s.title}**（`{s.key}`, {s.kind}）: {s.note}")
    L.append("")
    L += ["## 各数列の全項", ""]
    for s in sorted(seqs, key=lambda x: x.key):
        if not s.values:
            continue
        L.append(f"### `{s.key}` — {s.title}")
        L.append("")
        L.append(f"- 出典: `{s.source}`、添字 {s.index_name} = "
                 f"{s.index_from}..{s.index_from + s.n - 1}、種別 **{s.kind}**")
        if s.note:
            L.append(f"- 注: {s.note}")
        L.append(f"- 値: `{s.values}`")
        L.append("")
    return "\n".join(L)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    seqs = all_sequences()
    if args.json:
        print(json.dumps([asdict(s) for s in seqs], ensure_ascii=False))
        return 0
    if args.list:
        for s in sorted(seqs, key=lambda x: (-x.n, x.key)):
            print(f"{s.kind:7s} {s.n:3d} {s.key:34s} {s.title}")
        return 0
    out = DATA / "sequences_index.md"
    out.write_text(render(seqs))
    print(f"{len(seqs)} 本 → {out.relative_to(ROOT)}")
    print(f"うち exact かつ 4 項以上: {len(exact_sequences())} 本")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
