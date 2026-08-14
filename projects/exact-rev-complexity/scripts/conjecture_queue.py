"""厳密数列から漸化式を推測し、**次の未計算点の予測値**つきで予想キューを作る。

出力: `data/conjecture_queue.md`（自動生成・手編集禁止）

## 設計

推測そのものは `scripts/holonomic.py` に任せる（held-out 検証つき。**当てはめない**安全弁が
入っているのが唯一の理由）。ここがやるのは次の 3 つ:

1. `scripts/sequences_index.py` の `exact` な数列すべてに holonomic guessing を掛ける。
2. 見つかった漸化式で **次の 1 点を予測する**。これが検証手段になる
   （「次の 1 点を計算すれば真偽が決まる」形に落とす）。
3. **検証費用の安い順**に並べる。費用は、元の表に記録された実測秒数
   （`data/families/atlas.csv` の `seconds` 等）から、直近 2 点の比で外挿する。

## 読み方（重要）

- ここに出るのは**すべて層3（予想）**である。held-out 検証を通っていても証明ではない。
- **層の昇格は人間が判断する。**このスクリプトは昇格しない。
- 「漸化式なし」も結果である。特に**区分的な数列**（$p_{\\min}$ が段差で変わる族）は
  単一の漸化式が成り立つ理由が無い。段差の内側を切り出した数列のほうが候補になる。

    python3 scripts/conjecture_queue.py
    python3 scripts/conjecture_queue.py --max-order 5 --max-degree 5   # 探索を広げる
"""

from __future__ import annotations

import argparse
import csv
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from fractions import Fraction  # noqa: E402

from holonomic import Recurrence, affordable, guess, min_terms_needed  # noqa: E402
from sequences_index import Seq, all_sequences, exact_sequences  # noqa: E402

OUT = ROOT / "data" / "conjecture_queue.md"


def predict_next(rec: Recurrence, seq: list[int]) -> tuple[int | None, str]:
    """漸化式から**次の 1 項**を解く。

    `Recurrence.apply` は左辺の値を返す**検証用**であって予測ではない
    （`seq[n+order]` を参照するので、次項の予測には使えない）。ここで解く:

        p_order(n)·a(n+order) = -sum_{i<order} p_i(n)·a(n+i),   n = N - order

    先頭係数が 0（特異点）や、割り切れない場合は予測しない。
    **割り切れないこと自体が情報**（その漸化式は次の点で整数を返さない）なので理由を返す。
    """
    N = len(seq)
    n = N - rec.order
    if n < 0:
        return None, "項数が order に満たない"
    lead = sum(rec.coeffs.get((rec.order, j), 0) * (n ** j)
               for j in range(rec.degree + 1))
    if lead == 0:
        return None, f"先頭係数が n={n} で 0（特異点）。この漸化式では次項が決まらない"
    rhs = 0
    for i in range(rec.order):
        pi = sum(rec.coeffs.get((i, j), 0) * (n ** j) for j in range(rec.degree + 1))
        rhs -= pi * seq[n + i]
    val = Fraction(rhs, lead)
    if val.denominator != 1:
        return None, f"次項が整数にならない（{val}）。漸化式が次の点で破綻している"
    return int(val), ""


# --- 末尾パターン検出（holonomic が届かない区分的な数列向け） -----------------


def _diff(seq: list[int], k: int) -> list[int]:
    out = list(seq)
    for _ in range(k):
        out = [b - a for a, b in zip(out, out[1:])]
    return out


def tail_pattern(seq: list[int], *, min_tail: int = 5, holdout: int = 2
                 ) -> tuple[int | None, str]:
    """**末尾で**成り立つ規則を探し、次の 1 項を予測する。

    holonomic が「大域的な漸化式」を探すのに対し、こちらは
    「$p_{\\min}$ の段差より後ろでは規則的」という区分的な数列を狙う。
    見つかるのは*末尾についての*主張であって、数列全体の閉形式ではない。

    安全弁（当てはめ崩壊の再発防止）:
      - **末尾 `holdout` 項を隠して当て、隠した項を正しく予測できたものだけ採用する。**
      - 末尾で規則が成り立つ長さが `min_tail` 未満なら採用しない。

    返り値: (次項の予測, 規則の説明)。見つからなければ (None, "")。
    """

    def fit(s: list[int]) -> tuple[int | None, str]:
        # (1) k 階差が末尾で一定
        for k in range(1, 5):
            d = _diff(s, k)
            if len(d) < min_tail:
                break
            c = d[-1]
            t = 0
            for v in reversed(d):
                if v == c:
                    t += 1
                else:
                    break
            if t >= min_tail:
                nxt = s[-1]
                # k 階差が c で続くとして 1 項伸ばす
                tail = [s[-i] for i in range(1, k + 2)][::-1]
                cur = list(tail)
                for j in range(k, 0, -1):
                    pass
                # 逆差分で復元
                ds = [_diff(s, i)[-1] for i in range(1, k)]
                nxt = s[-1]
                acc = c
                for v in reversed(ds):
                    acc = v + acc
                nxt = s[-1] + (acc if k > 1 else c)
                return nxt, (f"末尾 {t} 項で **{k} 階差が {c} 一定**"
                             f"（{k}階差の末尾: `{d[-min(t, 8):]}`）")
        # (2) 1 階差が末尾で周期 q
        d1 = _diff(s, 1)
        for q in range(2, 7):
            if len(d1) < 3 * q:
                break
            per = d1[-q:]
            t = 0
            i = len(d1)
            while i - q >= 0 and d1[i - q:i] == per:
                t += q
                i -= q
            if t >= max(min_tail, 2 * q + 2):
                return s[-1] + per[0], (f"末尾 {t} 項で **1 階差が周期 {q}** "
                                        f"（周期: `{per}`）")
        return None, ""

    # held-out: 末尾 holdout 項を隠して当て、隠した項を予測できるか
    if len(seq) < holdout + min_tail + 1:
        return None, ""
    pred_hidden, _ = fit(seq[:-holdout])
    if pred_hidden is None or pred_hidden != seq[-holdout]:
        return None, ""
    nxt, why = fit(seq)
    if nxt is None:
        return None, ""
    return nxt, why + f"（末尾 {holdout} 項を隠した held-out 予測も的中）"


def run_history(seq: list[int]) -> dict:
    """1 階差の「連（同じ値が続く区間）」の履歴を返す。

    **末尾を隠す held-out は、連の内側を当てているだけで
    『連がいつ終わるか』を一切検定していない。**破れは定義上データの外で起きるので、
    末尾を隠す検定はこの型の誤りに原理的に盲目である（監視側の指摘、2026-08-10）。
    そこで、その数列**自身の履歴**にある破れを数える。

    返り値:
      runs        : [(値, 開始位置, 長さ)]（1 階差の連）
      broken      : 途中で終わった連（＝破れの実例）の長さのリスト
      max_broken  : そのうち最長。**現在の連がこれ以下なら、同じ長さの連が
                    既に破れた前科がある**ことになるので外挿してはいけない。
      tail_run    : 末尾の連の長さ
    """
    d = _diff(seq, 1)
    runs: list[tuple[int, int, int]] = []
    if not d:
        return {"runs": [], "broken": [], "max_broken": 0, "tail_run": 0}
    cur, start = d[0], 0
    for i in range(1, len(d)):
        if d[i] != cur:
            runs.append((cur, start, i - start))
            cur, start = d[i], i
    runs.append((cur, start, len(d) - start))
    broken = [ln for (_v, _st, ln) in runs[:-1]]      # 末尾以外＝実際に終わった連
    return {"runs": runs, "broken": broken,
            "max_broken": max(broken) if broken else 0,
            "tail_run": runs[-1][2]}


def retro_break_test(seq: list[int], predictor) -> list[dict]:
    """**遡及破れ検定**: 既知の破れ点の直前までのデータだけを手法に与え、外さないか見る。

    各破れ点 $i$（1 階差が変わる位置）について、そこまでの接頭辞を `predictor` に渡し、
    予測が出たならその値と実測を比べる。**1 つでも外したら、その手法で
    その数列の外挿を出さない。**
    """
    d = _diff(seq, 1)
    out = []
    for i in range(1, len(d)):
        if d[i] == d[i - 1]:
            continue
        prefix = seq[:i + 1]          # 破れの直前までの値
        truth = seq[i + 1]            # 破れた先の値
        pred, why = predictor(prefix)
        out.append({"at": i + 1, "prefix_len": len(prefix), "pred": pred,
                    "truth": truth, "ok": (pred is None or pred == truth),
                    "why": why})
    return out


def cross_slice(seqs: list[Seq]) -> list[dict]:
    """**同じ族・同じ列の複数の切片で同じ規則が成り立つか**を見る。

    1 本の切片だけで見つけた規則は、その切片限りの偶然かもしれない。
    切片をまたいで同じ規則（ここでは「切片の中では公差 $d$ の等差」）が成り立てば、
    それは族の構造についての主張になり、**次の切片で検証できる**。

    切片が閉じていても、*別の切片*が検証手段になるのがこの検出器の要点である。
    """
    groups: dict[tuple[str, str], list[Seq]] = {}
    for s in seqs:
        if not s.key.startswith("slice:"):
            continue
        head, _, ptag = s.key.rpartition(":p")
        if not ptag.isdigit():
            continue
        groups.setdefault((head, ptag and ""), []).append(s)
    out = []
    for (head, _), members in sorted(groups.items()):
        members = sorted(members, key=lambda x: int(x.key.rsplit(":p", 1)[1]))
        usable = [m for m in members if m.n >= 5]   # 証拠に使う切片
        if len(usable) < 2:
            continue
        # 2026-08-11: 切片が短いと構造が見えない。実例として fib の p8/p9 切片は
        # ちょうど 8 項で公差 4 のまま終わっており、16 項ある p10 切片で初めて
        # 公差が 4→6→8 と変わることが分かった（反証 3）。
        # **最長の切片が短いうちは切片横断の一致を根拠にしない。**
        if max(m.n for m in usable) < 12:
            continue
        diffs = []
        ok = True
        for m in usable:
            d = _diff(m.values, 1)
            if len(set(d)) != 1:
                ok = False
                break
            diffs.append(d[0])
        if not ok or len(set(diffs)) != 1:
            continue
        d = diffs[0]
        # 検証の的は「まだ閉じていない切片」。全部閉じているなら検証不能と書く。
        openers = [m for m in members if not m.closed and m.n >= 1]
        if openers:
            tgt = openers[-1]
            out.append({
                "head": head, "d": d, "members": usable, "target": tgt,
                "testable": True,
                "next_index": tgt.index_from + tgt.n,
                "next_value": tgt.values[-1] + d,
            })
        else:
            out.append({"head": head, "d": d, "members": usable, "target": None,
                        "testable": False, "next_index": None, "next_value": None})
    return out


# --- 検証費用の見積もり ------------------------------------------------------


def _seconds_table() -> dict[str, list[tuple[int, float]]]:
    """族ごとの (添字, 実測秒) を集める。次の点の費用を外挿するのに使う。"""
    out: dict[str, list[tuple[int, float]]] = {}
    p = ROOT / "data" / "families" / "atlas.csv"
    if p.exists():
        for r in csv.DictReader(p.open()):
            if r.get("status") != "exhaustive":
                continue
            fam, params = r["family"], r["params"]
            try:
                sec = float(r["seconds"])
                off = int(r["p"]) - int(r["pmin"])
            except (ValueError, KeyError):
                continue
            if fam == "bitrev":
                key, i = f"fam:bitrev:k:off{off}", int(params)
            elif fam == "cylinder":
                a, b = params.split(":")
                key, i = f"fam:cylinder:k[w={a}]:off{off}", int(b)
            elif fam == "kary_tree":
                a, b = params.split(":")
                key, i = f"fam:kary_tree:h[ary={a}]:off{off}", int(b)
            else:
                continue
            out.setdefault(key, []).append((i, sec))
    for rel, keys, icol, seccol in [
        ("data/exp01b_butterfly.csv",
         ["butterfly:M*_p0", "butterfly:M*_p1", "butterfly:M*_p2"], "k", "sec"),
        ("data/exp01b_saturation.csv",
         ["saturation:M*_p_min", "saturation:p_min"], "k", "sec"),
    ]:
        path = ROOT / rel
        if not path.exists():
            continue
        for r in csv.DictReader(path.open()):
            try:
                pt = (int(r[icol]), float(r[seccol]))
            except (ValueError, KeyError):
                continue
            for k in keys:
                out.setdefault(k, []).append(pt)
    # 追加計算の実測秒（scripts/extend_sequences.py が記録したもの）
    path = ROOT / "data" / "sequences_extended.csv"
    if path.exists():
        for r in csv.DictReader(path.open()):
            try:
                out.setdefault(r["key"], []).append((int(r["index"]),
                                                     float(r["seconds"])))
            except (ValueError, KeyError):
                continue
    return out


def estimate_cost(seq: Seq, table: dict[str, list[tuple[int, float]]]) -> tuple[float, str]:
    """次の 1 点の計算費用（秒）を外挿する。返り値 (秒, 根拠)。不明なら (inf, 理由)。"""
    # キーは完全一致で照合する（前方一致にすると別の族の秒数を拾う）
    cand = sorted(table.get(seq.key, []))
    if not cand or len(cand) < 2:
        return (float("inf"), "実測秒が表に無い（費用不明）")
    last, prev = cand[-1], cand[-2]
    if prev[1] <= 0:
        return (max(last[1] * 4, 1.0), f"直近 {last[1]:.2f}s（比が取れないので 4 倍と仮定）")
    ratio = max(last[1] / prev[1], 1.5)
    est = last[1] * ratio
    return (est, f"直近 {last[1]:.2f}s、比 {ratio:.1f}× から外挿")


# --- 本体 -------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-order", type=int, default=4)
    ap.add_argument("--max-degree", type=int, default=4)
    ap.add_argument("--min-slack", type=int, default=3)
    args = ap.parse_args()

    table = _seconds_table()
    seqs = exact_sequences(min_terms=5)
    # 切片版が存在する数列は「区分的だと分かっている」ので、
    # 非切片版からは予想を出さない（2026-08-11 の cylinder off2 の反証と同型の誤りを防ぐ）。
    sliced_heads = {k[len("slice:"):].rsplit(":p", 1)[0]
                    for k in {x.key for x in all_sequences()} if k.startswith("slice:")}

    found: list[tuple[float, Seq, str, int, str, str]] = []
    unresolved: list[tuple[Seq, str]] = []
    for s in seqs:
        if s.key in sliced_heads:
            unresolved.append((s, "**区分的だと分かっている**（$p_{\\min}$ 切片が"
                                  "存在する）ので、この数列からは予想を出さない。"
                                  "切片版を見ること"))
            continue
        rec = guess(s.values, max_order=args.max_order,
                    max_degree=args.max_degree, min_slack=args.min_slack)
        cost, why = estimate_cost(s, table)
        if rec is None:
            tnxt, twhy = tail_pattern(s.values)
            if tnxt is not None and not getattr(s, "closed", False):
                # --- 遡及破れ検定（監視側の指摘に基づく追加の関門） ---------
                hist = run_history(s.values)
                retro = retro_break_test(s.values, tail_pattern)
                bad = [r for r in retro if not r["ok"]]
                if bad:
                    unresolved.append((s,
                        f"末尾パターンは出たが**遡及破れ検定で外した**"
                        f"（{len(bad)}/{len(retro)} 箇所。例: 添字 {bad[0]['at']} で "
                        f"予測 {bad[0]['pred']} 実測 {bad[0]['truth']}）。"
                        "この数列にこの手法の外挿を出さない"))
                    continue
                if hist["tail_run"] <= hist["max_broken"]:
                    unresolved.append((s,
                        f"末尾パターンは出たが、**同じ長さの連が既に破れている前科**がある"
                        f"（末尾の連 {hist['tail_run']} 項 ≤ 過去に破れた最長の連 "
                        f"{hist['max_broken']} 項）。外挿しない"))
                    continue
                twhy += (f"。**前科**: この数列の 1 階差は "
                         f"{[(v, ln) for v, _st, ln in hist['runs']]} と連が変わっており、"
                         f"過去に最長 {hist['max_broken']} 項の連が破れている"
                         f"（現在の連は {hist['tail_run']} 項）。"
                         f"遡及破れ検定 {len(retro)} 箇所は全て通過"
                         f"（うち手法が予測を出したのは "
                         f"{sum(1 for r in retro if r['pred'] is not None)} 箇所）")
                found.append((cost, s, twhy, tnxt, why, "末尾パターン"))
                continue
            pairs = affordable(s.n, max_order=args.max_order, max_degree=args.max_degree)
            if not pairs:
                unresolved.append((s, f"**判定不能**（項数 {s.n} では確証つきで評価できる "
                                      f"$(order,degree)$ が 1 組も無い）→ 数列を伸ばす"))
            else:
                maxo = max(o for o, _ in pairs)
                maxd = max(d for _, d in pairs)
                unresolved.append((s, f"漸化式なし（$order\\le{maxo}$, $degree\\le{maxd}$ "
                                      f"の {len(pairs)} 組を確証つきで排除）"))
            continue
        if getattr(s, "closed", False):
            unresolved.append((s, "切片が**閉じている**ため次の点が存在しない"
                                  "（予想は出せても 1 点計算では検証できない）。"
                                  "検証するなら**次の切片で同じ形が成り立つか**を見る"))
            continue
        nxt, why_no = predict_next(rec, s.values)
        if nxt is None:
            unresolved.append((s, f"漸化式は出た（`{rec}`）が次項を予測できない: {why_no}"))
            continue
        found.append((cost, s, str(rec), nxt, why, "holonomic"))

    found.sort(key=lambda t: (t[0], -t[1].n))

    L = ["# 予想キュー（自動生成・手編集禁止）", "",
         "生成: `python3 scripts/conjecture_queue.py`／推測は `scripts/holonomic.py`",
         "（held-out 検証を通らない推測は出さない。当てはめ崩壊の再発防止）", "",
         "> **ここに出るのはすべて 層3（予想）である。** held-out を通っていても証明ではない。",
         "> **層の昇格は人間が判断する。**このスクリプトは昇格しない。", "",
         "**使い方**: 表は**検証費用の安い順**。各行の「次の点」を計算して予測値と比べれば、",
         "その予想の真偽がその場で決まる。外れたら予想を捨てる（それも成果）。", ""]

    L += [f"**要約**: `exact` かつ 5 項以上の {len(seqs)} 本のうち、"
          f"**{len(found)} 本で漸化式が見つかった**（＝予想 {len(found)} 本）。"
          f"残り {len(unresolved)} 本は漸化式なし・判定不能。", ""]

    L += ["## 予想（費用の安い順）", "",
          "| # | 数列 | 項数 | 予測: 次の点 | 漸化式 | 検証に要る計算 | 費用 | 層 |",
          "|---:|---|---:|---|---|---|---|---|"]
    for i, (cost, s, rec, nxt, why, kind) in enumerate(found, 1):
        nxt_idx = s.index_from + s.n
        costs = "不明" if cost == float("inf") else (
            f"{cost:.1f}s" if cost < 3600 else f"{cost / 3600:.1f}h")
        L.append(f"| {i} | {s.title}<br/>`{s.key}` | {s.n} | "
                 f"**{s.index_name}={nxt_idx} で {nxt}** | {kind}: {rec} | "
                 f"{s.index_name}={nxt_idx} の値を計算（出典 `{s.source}` の続き） | "
                 f"{costs} | 3 |")
    L.append("")

    L += ["### 各予想の詳細", ""]
    for i, (cost, s, rec, nxt, why, kind) in enumerate(found, 1):
        nxt_idx = s.index_from + s.n
        L += [f"#### {i}. {s.title}（`{s.key}`） — {kind}", "",
              f"- 出典: `{s.source}`、添字 {s.index_name} = "
              f"{s.index_from}..{s.index_from + s.n - 1}（{s.n} 項）",
              f"- 値: `{s.values}`",
              f"- **規則（予想）**: {rec}",
              f"- **予測**: {s.index_name}={nxt_idx} のとき **{nxt}**",
              f"- 検証費用の見積: {why}", ""]
        if s.note:
            L.append(f"- 注: {s.note}")
            L.append("")

    L += ["## 漸化式が出なかったもの", "",
          "「漸化式なし」は holonomic でない証拠ではない（探索範囲と項数の問題）。",
          "**判定不能**は項数不足なので、数列を伸ばすのが次の手。", "",
          "| 数列 | 項数 | 判定 |", "|---|---:|---|"]
    for s, msg in sorted(unresolved, key=lambda t: -t[0].n):
        L.append(f"| {s.title}<br/>`{s.key}` | {s.n} | {msg} |")
    L.append("")

    # --- 切片横断の規則 -----------------------------------------------------
    xs = cross_slice(all_sequences())
    L += ["## 切片をまたぐ規則（1 本の切片より強い予想）", ""]
    if not xs:
        L.append("（該当なし）")
    else:
        L += ["同じ族・同じ列の**複数の $p_{\\min}$ 切片で同じ規則**が成り立つもの。",
              "1 本の切片だけの規則より強く、**次の切片で検証できる**。", "",
              "| 対象 | 切片 | 規則 | 次の検証点 | 予測 | 層 |",
              "|---|---|---|---|---|---|"]
        for x in xs:
            ms = "、".join(f"$p_{{\\min}}$={m.key.rsplit(':p', 1)[1]}"
                          f"({m.n}項)" for m in x["members"])
            if x["testable"]:
                t = x["target"]
                nxt = (f"{t.index_name}={x['next_index']}"
                       f"（$p_{{\\min}}$={t.key.rsplit(':p', 1)[1]} 切片、"
                       f"現在 {t.n} 項）")
                pred = f"**{x['next_value']}**"
            else:
                nxt = "**検証不能**（証拠の切片が全て閉じている）→ 次の切片を 2 点以上計算する"
                pred = "—"
            L.append(f"| `{x['head']}` | {ms} | 各切片の中で**公差 {x['d']} の等差** | "
                     f"{nxt} | {pred} | 3 |")
        L.append("")
    L.append("")

    # --- 所見と、次に計算すべき点 -------------------------------------------
    L += ["## 所見（なぜ予想が少ないのか）", "",
          "1. **この族の数列は本質的に区分的である。** $M^*(G,p_{\\min})$ は "
          "$p_{\\min}$ が上がる位置で**値が減る**（鎖 $n=9$、spinal $k=8,16$、"
          "fib $n=17,25$ など。段差は 2 冪の位置に来る）。"
          "区分をまたぐ数列に単一の漸化式が成り立つ理由は無いので、"
          "「漸化式なし」は失敗ではなく**構造の反映**である。",
          "2. **切片は短い。** 段差が 2 冪で来るため、$p_{\\min}$ を固定した切片の長さも "
          "2 冪でしか伸びない。holonomic は $(r{+}1)(d{+}1)+r+\\mathrm{slack}$ 項を要求するので、"
          "切片が 8 項では $(1,1)$ か $(2,0)$ 程度しか評価できない。",
          "3. したがって**律速は項数**であり、計算時間を使う先は"
          "「新しい族を増やす」ことより「既存の切片を伸ばす」ことである。", "",
          "### 末尾パターンの関門（2026-08-10 追加）", "",
          "末尾 2 項を隠す held-out は**連の内側**を当てているだけで、"
          "**連がいつ終わるか**を検定していない（破れは定義上データの外で起きる）。"
          "そこで次の 2 つを追加の関門にした:", "",
          "1. **遡及破れ検定**: その数列自身の既知の破れ点それぞれについて、"
          "直前までの接頭辞だけを手法に与え、外さないかを見る。1 つでも外したら出さない。",
          "2. **前科の検定**: 末尾の連の長さが、過去に破れた連の最長以下なら出さない"
          "（同じ長さの連が既に破れているのに外挿するのは筋が通らない）。", "",
          "通過した予想にも、連の履歴を「前科」として必ず併記する。", ""]

    L += ["## 次に計算すべき点（判定不能を解消するのに必要な項数）", "",
          "各行は「あと何項計算すれば、その $(order,degree)$ を**確証つきで**評価できるか」。",
          "`slack=3`（推測に使わない検証式を 3 本残す）で計算した。", "",
          "| 数列 | 現在 | (1,1) | (2,1) | (2,2) | (3,2) | (3,3) |",
          "|---|---:|---:|---:|---:|---:|---:|"]
    targets = [(1, 1), (2, 1), (2, 2), (3, 2), (3, 3)]
    need_rows = []
    for s, msg in unresolved:
        if "判定不能" not in msg and "漸化式なし" not in msg:
            continue
        needs = [min_terms_needed(o, d, args.min_slack) for o, d in targets]
        gaps = [max(0, nd - s.n) for nd in needs]
        pos = [g for g in gaps if g > 0]
        need_rows.append((min(pos) if pos else 999, s, gaps))
    need_rows.sort(key=lambda t: (t[0], -t[1].n))
    for gmin, s, gaps in need_rows[:28]:
        L.append(f"| {s.title}<br/>`{s.key}` | {s.n} | "
                 + " | ".join(f"**+{g}**" if 0 < g <= 2 else
                              (f"+{g}" if g else "✅") for g in gaps) + " |")
    L += ["", "**読み方**: 「✅」は既にその $(order,degree)$ を評価済み"
          "（＝その範囲に漸化式は無いと確証つきで言えた）。"
          "「+k」はあと k 項要る。**+1 か +2 の行が費用対効果の高い計算依頼**である。", ""]
    L += ["延長は `python3 scripts/extend_sequences.py fib --from A --to B` などで行い、"
          "結果は `data/sequences_extended.csv` に追記されて自動的にこの表へ合流する。", ""]
    OUT.write_text("\n".join(L) + "\n")
    print(f"予想 {len(found)} 本 / 未解決 {len(unresolved)} 本 → {OUT.relative_to(ROOT)}")
    for i, (cost, s, rec, nxt, _why, kind) in enumerate(found[:15], 1):
        costs = "不明" if cost == float("inf") else f"{cost:.1f}s"
        print(f"  {i:2d}. [{costs:>8s}] {s.key:34s} 次={nxt:6d}  ({kind}) {rec[:60]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
