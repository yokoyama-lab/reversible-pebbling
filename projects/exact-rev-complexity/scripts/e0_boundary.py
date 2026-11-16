"""飽和閾値 e0(F,p) := min{e : reach_F(p,e) = reach_F(p,infty)} を CSV から抽出する。

`scripts/exp03_reach_dag.py --out ...` が吐く `family,p,e,reach,status,reason` の
CSV 群を読み、族×p ごとに e0 を判定する。

**最大の罠（2段ある）**:

1. 「e を増やしても reach が変わらない」ことは飽和の必要条件だが十分条件ではない。
   kmax・state_cap・mem_cap による打ち切り（status=UNKNOWN）を「値が変わらなかった」と
   混同すると、単に探索が足りていないだけの e を「飽和した」と誤読する。
2. **末尾が数点フラットであっても、それだけでは飽和の証拠にならない**（指揮者
   2026-08-11 の指摘、`diamond5 p=6` が実例: `[4,5,5,5,5,6,6]` はフラット長4の
   後に増加があり、フラット長2でも飽和の証拠にはならない）。掃引の打ち切り位置
   `emax` は探索者が選んだ任意の値であり、「末尾が emax までフラット」は
   「emax を超えて伸ばしても本当にフラットか」を何も保証しない。

したがって、ここでは **`kind="flat_to_emax"`（旧称 saturated）を「飽和の確定」ではなく
「emax までは動かなかった候補」としてのみ報告する**。「動かなかった」という**必要条件**の
確認に留め、e をさらに伸ばして反証を試みるまでは飽和と断定しない立場を取る。

  - status が exact の行だけを使う。UNKNOWN の行がある e から先は
    「不明（打ち切りのため e0 未確定）」として扱い、断じて飽和と読まない。
  - `flat_to_emax` の判定は「末尾（検証した最大の e）まで途切れず confirm+1 個以上
    連続で同じ reach 値」を要求する（それでも「証拠」であって「証明」ではない）。
  - e の掃引が emax まで単調増加のまま終わった（一度も足踏みしていない）場合は
    「e0 > emax（未飽和 or 判定不能）」として reach_F(p,infty) 自体が未確定。

実行: python3 scripts/e0_boundary.py --out data/e0_boundary.md
"""

from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"

CONFIRM = 2  # e0 の後、これだけ連続して同じ値が exact で確認できないと飽和と認めない


def load(paths: list[Path]) -> dict[tuple[str, int], list[tuple[int, str, str]]]:
    """(family, p) -> [(e, status, reach_str), ...]（e 昇順）を返す。"""
    rows: dict[tuple[str, int], list[tuple[int, str, str]]] = defaultdict(list)
    for path in paths:
        if not path.exists():
            continue
        with path.open(encoding="utf-8") as fh:
            for row in csv.DictReader(fh):
                fam = row["family"]
                p = int(row["p"])
                e = int(row["e"])
                rows[(fam, p)].append((e, row["status"], row["reach"]))
    for key in rows:
        rows[key].sort()
    return rows


def classify(series: list[tuple[int, str, str]]) -> dict:
    """1つの (family, p) 系列から e0 を判定する。

    返り値: {"e0": str, "reach_inf": int|None, "kind": str, "note": str,
             "e_checked": str}
    kind は "flat_to_emax" / "unbounded_within_range" / "cutoff_before_e0" / "no_data"。
    **"e0" は常に文字列**（確定時は整数の文字列表現、掃引の端で足踏みせず終わった
    ときは指揮者の指示どおり ">{emax_checked}" と書く。これを飽和と読んではいけない）。
    """
    if not series:
        return {"e0": "-", "reach_inf": None, "kind": "no_data", "note": "行なし",
                "e_checked": "-"}

    exact_vals: dict[int, int] = {}
    unknown_es: list[int] = []
    for e, status, reach in series:
        if status == "exact":
            exact_vals[e] = int(reach)
        elif status == "UNKNOWN":
            unknown_es.append(e)
    first_unknown_e = min(unknown_es) if unknown_es else None
    all_checked_es = sorted(exact_vals) + unknown_es
    e_checked = f"0..{max(all_checked_es)}" if all_checked_es else "-"

    if not exact_vals:
        return {"e0": "-", "reach_inf": None, "kind": "no_data",
                "note": "全行 UNKNOWN（打ち切り、exact 行なし）", "e_checked": e_checked}

    es_sorted = sorted(exact_vals)

    # **e0 は「末尾まで途切れず一定」の区間の開始点として定義する**（一時的な足踏みを
    # 飽和と誤読しないため）。CONFIRM 個だけ先読みして一致すればよいという判定は
    # 罠がある: diamond_sqrt p=3 は e=2..5 で reach=4 のまま4回連続一致するが、
    # e=6 で 5 に上がる（幅がまた1段増えたため）。これは「幅の階段の踊り場」であって
    # 飽和ではない。したがって、末尾（掃引した最大 e、exact かつ連番でつながっている
    # 範囲）から遡って同じ値が続く区間の開始を e0 候補とし、かつその区間の長さが
    # 1+CONFIRM 以上あることを要求する。
    # 末尾の「連番かつ exact」な連続区間を求める。
    tail_run: list[int] = []
    for e in reversed(es_sorted):
        if not tail_run or e == tail_run[-1] - 1:
            tail_run.append(e)
        else:
            break
    tail_run.reverse()  # 昇順に戻す

    e0_int = None
    if tail_run:
        tail_v = exact_vals[tail_run[-1]]
        # tail_run 内で末尾の値と異なる箇所より後ろだけを飽和区間の候補にする
        plateau_start_idx = len(tail_run) - 1
        for i in range(len(tail_run) - 1, -1, -1):
            if exact_vals[tail_run[i]] == tail_v:
                plateau_start_idx = i
            else:
                break
        plateau_len = len(tail_run) - plateau_start_idx
        if plateau_len >= 1 + CONFIRM:
            e0_int = tail_run[plateau_start_idx]

    # 足踏み（一時的にだけ値が変わらない区間）が e0 候補より手前にあれば記録しておく
    # （幅の階段と reach の対応を見るのに使える。飽和とは呼ばない）。
    plateaus: list[tuple[int, int, int]] = []  # (start_e, end_e, value)
    run_start = es_sorted[0]
    run_val = exact_vals[run_start]
    prev_e = run_start
    for e in es_sorted[1:]:
        if e == prev_e + 1 and exact_vals[e] == run_val:
            prev_e = e
            continue
        if prev_e > run_start:
            plateaus.append((run_start, prev_e, run_val))
        run_start = e
        run_val = exact_vals[e]
        prev_e = e
    if prev_e > run_start:
        plateaus.append((run_start, prev_e, run_val))
    non_final_plateaus = [pl for pl in plateaus if e0_int is None or pl[0] < e0_int]

    plateau_note = ""
    if non_final_plateaus:
        parts = [f"e={s}..{en}で{v}のまま足踏み後に再上昇" for s, en, v in non_final_plateaus]
        plateau_note = "（踊り場あり: " + "、".join(parts) + "）"

    if e0_int is not None:
        reach_inf = exact_vals[e0_int]
        # e0 より前に UNKNOWN が挟まっていた場合は「その手前までは不明」と明記
        note = plateau_note
        if first_unknown_e is not None and first_unknown_e < e0_int:
            note += ("；" if note else "") + \
                f"e<{e0_int} の一部に UNKNOWN あり（打ち切り、飽和前の値は未確定な箇所を含む）"
        return {"e0": str(e0_int), "reach_inf": reach_inf, "kind": "flat_to_emax",
                "note": note, "e_checked": e_checked}

    # e0 が確定しなかった。理由を分ける。**ここで確定しない e0 を数値で書かない**
    # （指揮者 2026-08-11: 掃引の端で止まった行を飽和と誤読した事故の再発防止。
    #   一時的な足踏み＝踊り場を飽和と取り違えたのも同じ型の事故なので、
    #   末尾まで途切れず一定でなければ e0 を確定させない）。
    if first_unknown_e is not None:
        last_exact_before_cutoff = max((e for e in es_sorted if e < first_unknown_e),
                                        default=None)
        return {"e0": f">{last_exact_before_cutoff}" if last_exact_before_cutoff is not None
                       else "unknown",
                "reach_inf": None, "kind": "cutoff_before_e0",
                "note": (plateau_note + "；" if plateau_note else "") +
                        f"e={first_unknown_e} から UNKNOWN（打ち切り）。"
                        f"それまでの exact 値は単調増加のみで飽和未確認。"
                        f"「飽和した」とも「飽和しない」とも言えない",
                "e_checked": e_checked}
    # 全部 exact なのに値が変わり続けている = 掃引範囲内では飽和なし（鎖型の可能性）
    last_e = es_sorted[-1]
    return {"e0": f">{last_e}", "reach_inf": None, "kind": "unbounded_within_range",
            "note": (plateau_note + "；" if plateau_note else "") +
                    f"e=0..{last_e} 全て exact だが単調増加が続き飽和せず"
                    f"（reach(e={last_e})={exact_vals[last_e]}）。"
                    f"e0>{last_e} としか言えない（e0=∞ の鎖型か、掃引範囲が"
                    f"足りないだけかはこの表からは未判定）",
            "e_checked": e_checked}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--csv", nargs="*", default=None,
                     help="対象 CSV（省略時は data/e0_*.csv を自動収集）")
    ap.add_argument("--out", default=str(DATA / "e0_boundary.md"))
    args = ap.parse_args()

    if args.csv:
        paths = [Path(p) for p in args.csv]
    else:
        paths = sorted(DATA.glob("e0_*.csv"))

    print(f"入力 CSV: {[p.name for p in paths]}")
    rows = load(paths)

    by_family: dict[str, dict[int, dict]] = defaultdict(dict)
    for (fam, p), series in rows.items():
        by_family[fam][p] = classify(series)

    lines: list[str] = []
    lines.append("# e0(F,p) 飽和閾値表（自動生成）")
    lines.append("")
    lines.append("`e0(F,p) := min{e : reach_F(p,e) = reach_F(p,∞)}`。")
    lines.append(f"`flat_to_emax` 判定は「末尾（検証した最大の e）まで途切れず連続 "
                 f"{1 + CONFIRM} 個の e で exact 値が一致」を要求する"
                 "（打ち切り(UNKNOWN)や一時的な足踏み(踊り場)を飽和と誤認しないための下限）。")
    lines.append("")
    lines.append("**⚠ `flat_to_emax` は「飽和の確定」ではない。**"
                  "掃引の上限 `emax` は任意に選んだ値であり、`emax` まで動かなかったことは"
                  "`emax` を超えても動かない証拠にはならない"
                  "（`diamond5 p=6` が実例: `[4,5,5,5,5,6,6]` はフラット長4の後に増加があり、"
                  "フラット長2でも飽和の証拠にならなかった）。")
    lines.append("")
    lines.append("**`e0` 列の読み方**: 整数は「emax まで動かなかった」ことを意味する"
                  "（`flat_to_emax` の開始点。飽和の確定ではない）。`>N` は「e=N まで単調増加を"
                  "確認したが、その先は未検証（打ち切り or 掃引範囲外）」であり、"
                  "**`>N` を飽和とは読まない**（e0=∞ の可能性を含む）。")
    lines.append("")
    lines.append("## 族ごとの「検証した p の範囲」")
    lines.append("")
    lines.append("**p の値を検証範囲の外へ外挿しないこと**"
                  "（`reach_cbt(p,0)=p-2` が p=9 で崩れた事故が実例）。")
    lines.append("")
    lines.append("| family | 検証した p | 備考 |")
    lines.append("|---|---|---|")
    for fam in sorted(by_family):
        ps = sorted(by_family[fam])
        p_lo, p_hi = ps[0], ps[-1]
        p_range = f"{p_lo}..{p_hi}" if p_lo != p_hi else str(p_lo)
        note = "" if len(ps) == (p_hi - p_lo + 1) else f"（欠測あり: 実測 {ps}）"
        lines.append(f"| {fam} | {p_range} | {note} |")
    lines.append("")
    lines.append("## 族×p ごとの e0")
    lines.append("")
    lines.append("| family | p | e0 | reach(e0)（flat_to_emax のときのみ） | 検証した e | 判定 | 備考 |")
    lines.append("|---|---:|---|---:|---|---|---|")
    for fam in sorted(by_family):
        for p in sorted(by_family[fam]):
            r = by_family[fam][p]
            reach_inf = r["reach_inf"] if r["reach_inf"] is not None else "-"
            lines.append(f"| {fam} | {p} | {r['e0']} | {reach_inf} | {r['e_checked']} | "
                         f"{r['kind']} | {r['note']} |")
    lines.append("")
    lines.append("## 判定区分の意味")
    lines.append("")
    lines.append("- **flat_to_emax**: emax まで途切れず一定だった候補（e0 は整数）。"
                  "**飽和の確定ではない**——emax を超えて伸ばすまでは反証されていないだけ。")
    lines.append("- **unbounded_within_range**: 掃引範囲では一度も足踏みせず単調増加"
                  "（鎖のように無限に伸びる族の可能性。e0 は `>emax` 表記。"
                  "範囲を広げないと e0=∞ かどうかは確定しない）。")
    lines.append("- **cutoff_before_e0**: flat_to_emax が確認できる前に打ち切り(UNKNOWN)に"
                  "当たった。e0 は `>最後の exact な e` 表記。**「飽和していない」でも"
                  "「飽和した」でもなく、単に分からない**。")
    lines.append("- **no_data**: 対応する CSV 行が無い、または全行 UNKNOWN。")
    lines.append("")

    out_path = Path(args.out)
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"書き出し: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
