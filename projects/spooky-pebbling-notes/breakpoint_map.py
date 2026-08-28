#!/usr/bin/env python3
"""折れ目（増分が上がる n）の地図を、掃引の CSV と 1 点判定の結果から機械的に作る。

**なぜ手計算でやらないか**: 折れ目は「T(n) − T(n−1) が上がる点」なので、
1 点でも値を取り違えると以降の折れ目が全部ずれる。手で足し算すると誤りが混ざる
（知見 `machine-checkable-work-ladder`）。

**確定と推定を分ける。**

- `確定`: SAT(T) と UNSAT(T−1) の両方がある。仮定なしで T(n) が決まる
- `上界のみ` / `下界のみ`: 片側しかない
- `単調仮定`: 片側 ＋ **階差が非減少**という仮定で挟めた。⚠ これは層3

⚠ **`--selftest` を必ず通してから読むこと。** 判定規則自体を検定する。
"""
from __future__ import annotations

import argparse
import collections
import csv
import glob
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load_sweeps(paths: list[str]) -> dict[tuple[str, int], dict[int, int]]:
    """掃引 CSV（kind,s,n,T,sec,note）から**確定値**を読む。T が空の行は無視する。

    ⚠ **1 点判定の CSV を掃引として読んではいけない。** どちらも `T` 列を持つが
    意味が違う——掃引の `T` は**求まった厳密値**、1 点判定の `T` は**試した値**で、
    結果が SAT なら上界にすぎない。列名 `result` の有無で弾く。
    2026-08-28 にこれを混ぜて、`UP s=8 n=36` の SAT（上界）を確定値と読み、
    **三角数則が s=8 で成り立った**という誤った結論を一度出した。
    """
    out: dict[tuple[str, int], dict[int, int]] = collections.defaultdict(dict)
    for p in paths:
        with open(p, newline="") as fh:
            rd = csv.DictReader(fh)
            if rd.fieldnames and "result" in rd.fieldnames:
                continue  # 1 点判定の CSV。load_oneT の担当
            for r in rd:
                try:
                    if r.get("T"):
                        out[(r["kind"], int(r["s"]))][int(r["n"])] = int(r["T"])
                except (ValueError, TypeError, KeyError):
                    continue
    return out


def load_oneT(path: str) -> dict[tuple[str, int, int], dict[str, set[int]]]:
    """1 点判定を (kind,s,n) -> {"SAT": {T…}, "UNSAT": {T…}} にまとめる。

    ⚠ `不明(rc=…)` は SAT でも UNSAT でもない。**落とす**（知見 solver-abort-is-not-unsat）。
    """
    acc: dict[tuple[str, int, int], dict[str, set[int]]] = collections.defaultdict(
        lambda: {"SAT": set(), "UNSAT": set()})
    if not os.path.exists(path):
        return acc
    with open(path, newline="") as fh:
        for r in csv.DictReader(fh):
            res = (r.get("result") or "").strip()
            if res not in ("SAT", "UNSAT"):
                continue
            acc[(r["kind"], int(r["s"]), int(r["n"]))][res].add(int(r["T"]))
    return acc


def pin(sat: set[int], unsat: set[int]) -> tuple[int | None, str]:
    """SAT/UNSAT の集合から T(n) を決める。返すのは (値, 根拠)。"""
    lo = max(unsat) + 1 if unsat else None   # UNSAT(x) ⟹ T ≥ x+1
    hi = min(sat) if sat else None           # SAT(x)   ⟹ T ≤ x
    if lo is not None and hi is not None:
        if lo == hi:
            return lo, "確定"
        if lo > hi:
            return None, f"⚠ 矛盾（下界 {lo} > 上界 {hi}）"
        return None, f"未確定（{lo}..{hi}）"
    if hi is not None:
        return None, f"上界のみ（T ≤ {hi}）"
    if lo is not None:
        return None, f"下界のみ（T ≥ {lo}）"
    return None, "測定なし"


def breakpoints(vals: dict[int, int]) -> list[tuple[int, int, int]]:
    """連続する n だけを見て、階差が上がる n を返す。(n, 前の階差, 後の階差)。"""
    ns = sorted(vals)
    diffs = [(ns[i], vals[ns[i]] - vals[ns[i - 1]])
             for i in range(1, len(ns)) if ns[i] == ns[i - 1] + 1]
    out, prev = [], None
    for n, d in diffs:
        if prev is not None and d != prev:
            out.append((n, prev, d))
        prev = d
    return out


def formula_s3(k: int) -> int:
    """s=3 の折れ目の予測式（層3・実測 8 点からの帰納）。"""
    return (k + 1) * (k + 2) // 2 + 3


def formula_s4(k: int) -> int:
    """s=4 の折れ目の予測式（層3・実測 3 点からの二次あてはめ）。"""
    return 2 * k * k + 2 * k + 6


def selftest() -> int:
    bad = 0

    def chk(name, got, want):
        nonlocal bad
        if got != want:
            print(f"  ✗ {name}: {got!r} ≠ {want!r}")
            bad += 1

    # pin の 6 通り
    chk("両側で確定", pin({428}, {427}), (428, "確定"))
    chk("上界のみ", pin({428}, set())[1], "上界のみ（T ≤ 428）")
    chk("下界のみ", pin(set(), {427})[1], "下界のみ（T ≥ 428）")
    chk("測定なし", pin(set(), set())[1], "測定なし")
    chk("隙間あり", pin({430}, {427})[1], "未確定（428..430）")
    # ⚠ 矛盾を「確定」に化けさせない（検査器の検査）
    chk("矛盾", pin({427}, {428})[0], None)
    # ⚠ assert で書かない。`python3 -O` で消えて検査が黙って無くなる（知見 assert-vanishes-under-O）
    chk("矛盾の理由を書く", "矛盾" in pin({427}, {428})[1], True)
    # 複数の SAT/UNSAT があるときは最も強いものを採る
    chk("最強を採る", pin({428, 500}, {400, 427}), (428, "確定"))

    # breakpoints
    chk("折れ目なし", breakpoints({1: 1, 2: 3, 3: 5}), [])
    chk("折れ目 1 個", breakpoints({1: 1, 2: 3, 3: 7}), [(3, 2, 4)])
    # ⚠ n が飛んでいる区間をまたいで階差を計算しない
    chk("飛びをまたがない", breakpoints({1: 1, 2: 3, 5: 99}), [])

    # load_oneT が「不明(rc=…)」を落とすか。
    # ⚠ 2026-08-28 の変異注入で、この検定が無いと「不明を UNSAT に混ぜる」変異が
    #    生き残ることが分かった（知見 solver-abort-is-not-unsat / and-condition-needs-per-term-mutation）。
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".csv", delete=False, newline="") as fh:
        fh.write("host,kind,s,n,T,sec,result\n"
                 "h,UG,3,9,60,1,SAT\n"
                 "h,UG,3,9,59,1,不明(rc=137)\n"
                 "h,UG,3,9,58,1,UNSAT\n")
        tmp = fh.name
    acc = load_oneT(tmp)
    os.unlink(tmp)
    chk("不明は SAT に入らない", acc[("UG", 3, 9)]["SAT"], {60})
    chk("不明は UNSAT に入らない", acc[("UG", 3, 9)]["UNSAT"], {58})
    chk("不明を混ぜると値がずれる", pin(acc[("UG", 3, 9)]["SAT"], acc[("UG", 3, 9)]["UNSAT"]), (None, "未確定（59..60）"))

    # load_sweeps が 1 点判定の CSV を掃引として飲み込まないか
    with tempfile.NamedTemporaryFile("w", suffix=".csv", delete=False, newline="") as fh:
        fh.write("kind,s,n,T,sec,result\nUP,8,36,129,1,SAT\n")
        tmp2 = fh.name
    got = load_sweeps([tmp2])
    os.unlink(tmp2)
    chk("1 点判定を掃引と読まない", dict(got), {})

    # 予測式が既知の折れ目を再現するか（当てはめの検算）
    chk("s3 の式", [formula_s3(k) for k in range(1, 9)], [6, 9, 13, 18, 24, 31, 39, 48])
    chk("s4 の式", [formula_s4(k) for k in range(1, 4)], [10, 18, 30])
    print(f"selftest: {'🟢 合格' if bad == 0 else f'🔴 {bad} 件失敗'}")
    return 1 if bad else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--sweeps", nargs="*", default=None)
    ap.add_argument("--oneT", default=os.path.join(HERE, "oneT_results.csv"))
    a = ap.parse_args()
    if a.selftest:
        return selftest()

    paths = a.sweeps or sorted(glob.glob(os.path.join(HERE, "*.csv")))
    paths = [p for p in paths if not p.endswith("oneT_results.csv")]
    sweeps = load_sweeps(paths)
    ones = load_oneT(a.oneT)

    print("=== 掃引から出た折れ目（連続する n だけ） ===")
    for key in sorted(sweeps, key=lambda x: (x[1], x[0])):
        v = sweeps[key]
        ns = sorted(v)
        print(f"{key[0]} s={key[1]}: n={ns[0]}..{ns[-1]} {len(ns)} 点 "
              f"折れ目 {[b[0] for b in breakpoints(v)]}")

    print("\n=== 1 点判定（one_T）で決まったもの ===")
    for key in sorted(ones, key=lambda x: (x[1], x[0], x[2])):
        kind, s, n = key
        val, why = pin(ones[key]["SAT"], ones[key]["UNSAT"])
        base = sweeps.get((kind, s), {})
        note = ""
        if val is not None and n - 1 in base:
            note = f"  階差 {val - base[n - 1]}（T({n-1})={base[n-1]}）"
        print(f"{kind} s={s} n={n}: T={val if val is not None else '—'}  [{why}]{note}")

    print("\n=== 予測式との突き合わせ（層3） ===")
    for s, f, name in ((3, formula_s3, "(k+1)(k+2)/2 + 3"), (4, formula_s4, "2k²+2k+6")):
        preds = [f(k) for k in range(1, 11)]
        print(f"s={s}: b_k = {name} → {preds}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
