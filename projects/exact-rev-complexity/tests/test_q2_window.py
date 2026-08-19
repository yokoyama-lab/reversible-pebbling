#!/usr/bin/env python3
"""`q2_cnf.py --window` の検査（2026-08-14）。

`--window` は **Lean で機械証明した制約だけ**を CNF に足す:

| 制約 | Lean の定理（`lean/Revgarbage/ParPebbleWindow.lean`） | 適用範囲 |
|---|---|---|
| `dep(v)+1 ≤ t`（早すぎる配置の禁止） | `depth_bound_seg` | 任意の DAG |
| `t ≤ T-dep(v)-1`（遅すぎる存在の禁止・sink 以外） | `time_window_seg` | 任意の DAG |
| `x[v][dep(v)+1] = 1`（窓の左端で必ず存在） | `present_at_window_start` / `no_slack` | 鎖 |
| `x[v][T-dep(v)-1] = 1`（窓の右端で必ず存在） | `present_at_window_end` / `no_slack` | 鎖 |
| `x[sink][t] = 1`（`t ≥ dep(sink)+1`） | `chain_sink_stays` | 鎖 |

**すべて任意の合法ペブリングで成り立つので、SAT 側にも UNSAT 側にも使ってよい。**
（充足可能性を保つ含意節を足しているだけなので、`--window` の UNSAT は素の CNF の
UNSAT を意味する。）

この検査が守るのは 1 点: **素の CNF と `--window` の判定が全点で一致すること**。
片方でも食い違えば制約が誤りなので、数値を使ってはならない。
"""
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import q2_cnf  # noqa: E402

# (family, n, p, 期待する結果)。T は常に 2*depth+1（時間最適）。
CASES = [
    ("line", 2, 1, "UNSAT"),
    ("line", 2, 2, "SAT"),
    ("line", 4, 2, "UNSAT"),
    ("line", 4, 3, "SAT"),      # 手で作った列（ピーク3）と一致する点
    ("line", 7, 4, "SAT"),      # n*(4) = 7
    ("line", 8, 4, "UNSAT"),
    ("line", 11, 5, "SAT"),     # n*(5) = 11
    ("line", 12, 5, "UNSAT"),
    ("line", 17, 6, "SAT"),     # n*(6) = 17
    ("line", 18, 6, "UNSAT"),
    ("line", 25, 7, "SAT"),     # n*(7) = 25
    ("line", 26, 7, "UNSAT"),
    ("pyramid", 3, 5, "UNSAT"),
    ("pyramid", 3, 6, "SAT"),   # p_min(pyr 3) = 6
    ("pyramid", 4, 7, "UNSAT"),
    ("pyramid", 4, 8, "SAT"),   # p_min(pyr 4) = 8
    ("pyramid", 6, 12, "UNSAT"),
    ("pyramid", 6, 13, "SAT"),  # p_min(pyr 6) = 13
]


def solve(par, sink, p, T, **kw):
    c = q2_cnf.build(par, sink, p, T, **kw)
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        path = f.name
    c.dump(path)
    try:
        r = subprocess.run(["cadical", path, "-q"], capture_output=True,
                           text=True, timeout=3600)
        out = [ln for ln in r.stdout.splitlines() if ln.startswith("s ")]
        if not out:
            return "打ち切り", len(c.cls), c.n
        return ("SAT" if "SATISFIABLE" in out[0] and "UNSAT" not in out[0]
                else "UNSAT"), len(c.cls), c.n
    finally:
        os.unlink(path)


# 含意そのものを検定する対象（小さいものだけ。1 単位節につき SAT を 1 回呼ぶ）
IMPLIED_CASES = [("line", 4, 3), ("line", 5, 4), ("line", 6, 4),
                 ("line", 7, 4), ("pyramid", 3, 6), ("pyramid", 4, 8)]


def sat(cls, nvars) -> bool:
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as f:
        path = f.name
        f.write(f"p cnf {nvars} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    try:
        r = subprocess.run(["cadical", path, "-q"], capture_output=True,
                           text=True, timeout=600)
        return any(ln.startswith("s SATISFIABLE") for ln in r.stdout.splitlines())
    finally:
        os.unlink(path)


def check_implied() -> int:
    """**`--window` が足す単位節が、素の CNF から本当に含意されるか**を1本ずつ検定する。

    「素の CNF ∧ ¬（その単位節）」が UNSAT なら含意されている。SAT なら、その制約を
    満たさない合法なペブリングが存在するので**制約は誤り**。

    判定の一致だけを見る検査は、過剰な制約が SAT を UNSAT に変えなければ素通りする
    （実際 2026-08-14 の変異注入で 3 件素通りした）ので、この一段深い検査を置く。
    """
    bad = 0
    print("\n--- 単位節が素の CNF から含意されるかの直接検定 ---")
    for fam, n, p in IMPLIED_CASES:
        par, sink = q2_cnf.FAMILIES[fam](n)
        dep = q2_cnf.depths(par)
        T = 2 * dep[sink] + 1
        nx = len(par) * (T + 1)          # x 変数の番号は両者で一致する
        plain = q2_cnf.build(par, sink, p, T)
        win = q2_cnf.build(par, sink, p, T, window=True)
        pu = {c[0] for c in plain.cls if len(c) == 1}
        extra = sorted({c[0] for c in win.cls if len(c) == 1} - pu,
                       key=abs)
        extra = [lt for lt in extra if abs(lt) <= nx]
        ng = []
        for lit in extra:
            if sat(plain.cls + [[-lit]], plain.n):
                v, t = divmod(abs(lit) - 1, T + 1)
                ng.append(f"x[{v}][{t}]={'1' if lit > 0 else '0'}")
        bad += len(ng)
        mark = "✔" if not ng else "✖"
        print(f"  {mark} {fam} {n} p={p}: 単位節 {len(extra)} 本中 "
              f"{len(ng)} 本が含意されていない"
              + (f"  → {', '.join(ng[:6])}" if ng else ""))
    return bad


def main() -> int:
    fails = 0
    print(f"{'族':>8} {'n/h':>4} {'p':>3} {'期待':>6} {'素':>6} {'窓':>6} "
          f"{'節(素)':>9} {'節(窓)':>9} {'削減':>6}")
    for fam, n, p, want in CASES:
        par, sink = q2_cnf.FAMILIES[fam](n)
        dep = q2_cnf.depths(par)
        T = 2 * dep[sink] + 1
        r_plain, cl_plain, _ = solve(par, sink, p, T)
        r_win, cl_win, _ = solve(par, sink, p, T, window=True)
        red = f"{100 * (1 - cl_win / cl_plain):.0f}%"
        ok = (r_plain == want == r_win)
        if not ok:
            fails += 1
        print(f"{fam:>8} {n:>4} {p:>3} {want:>6} {r_plain:>6} {r_win:>6} "
              f"{cl_plain:>9} {cl_win:>9} {red:>6}  {'' if ok else '✖ 不一致'}")
    if fails:
        print(f"\n✖ {fails} 件が不一致。--window の制約が誤っている。数値を使ってはならない。")
        return 1
    bad = check_implied()
    if bad:
        print(f"\n✖ 含意されていない単位節が {bad} 本。--window は使ってはならない。")
        return 1
    print(f"\n✔ {len(CASES)} 件すべて一致（期待値・素の CNF・窓つき CNF）")
    print("✔ 追加した単位節はすべて素の CNF から含意される（1本ずつ検定）")
    return 0


def test_window_units_are_implied():
    """pytest からも走らせる（main() だけだと 0 件収集になり、
    「走っていない検査」と「異常なし」が区別できなくなる）。"""
    assert main() == 0


if __name__ == "__main__":
    sys.exit(main())
