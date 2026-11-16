"""補題 A・B（コミット順序 DP の交換法則）を SMT で固定 p ごとに検証する。

`data/ic3_b2_tight_support.md` §8 の補題:
  W(S) = min_π Σ C(gap_i; p-(i-1))  （予想 U の DP。C は到達の階段）
  補題 A: 支持つきペブル x（x-1 ∈ S∪{0}）の除去で W は不変
          （追加方向 ≤ は C(1;·)=0 で自明。ここでは非自明な
            W(T∖{x}) ≤ W(T) を検証する）
  補題 B: 支持なしペブル x の除去で W は高々 +1

有限 N の全数検査（umin_dp.py 側、p≤8 で反例 0）と違い、ここでは
**ギャップを記号変数**（1 ≤ d_i ≤ 2^20）にした ∀ 命題の否定を UNSAT で示す。
固定するのは p・|T|・x の位置だけで、位置そのものは無制限に近い。
z3 と cvc5 の**2 つの独立ソルバ**で突き合わせる。

ミューテーション検査: 補題 B の「+1」を「+0」に弱めた偽命題が SAT
（反例発見）になることを確認し、検査が実際に効いていることを示す。

    python3 scripts/lemmaAB_smt.py --p 3
    python3 scripts/lemmaAB_smt.py --p 4 --solver both
    python3 scripts/lemmaAB_smt.py --mutation   # 検出力の確認
"""

from __future__ import annotations

import argparse
import itertools
import subprocess
import tempfile
from pathlib import Path

INF = 1 << 40
DMAX = 1 << 20


def c_term(g: str, q: int, *, mutate: str | None = None) -> str:
    """C(g;q) の SMT 式。mutate='b0' では変更なし（B 側で +1 を外す）。"""
    if q <= 0:
        return str(INF)
    if q == 1:
        return f"(ite (= {g} 1) 0 {INF})"
    half = 1 << (q - 1)
    quarter = 1 << (q - 2)
    if mutate == "thresh":
        half += 1
    return f"(ite (<= {g} {half}) 0 (div (+ (- {g} {half}) {quarter - 1}) {quarter}))"


def gap_expr(lo: int, hi: int) -> str:
    """位置 t_hi - t_lo（lo=0 なら t_hi）をギャップ変数の和で。"""
    terms = [f"d{i}" for i in range(lo + 1, hi + 1)]
    return terms[0] if len(terms) == 1 else "(+ " + " ".join(terms) + ")"


def min_cost_def(
    name: str,
    indices: list[int],
    p: int,
    lines: list[str],
    *,
    mutate: str | None = None,
    last: int | None = None,
) -> str:
    """全コミット順序の最小コストを中間変数で定義し、その変数名を返す。

    min を ite で畳み込むと式がテキスト的に指数複製される（|T|=4 で z3 が
    12GB 即死した実測）ので、順序ごとのコストを declare-const + assert で
    名前づけし、min は「≤ 全部 ∧ どれかに一致」で線形サイズにする。
    """
    orders = list(itertools.permutations(indices))
    if last is not None:
        orders = [o for o in orders if o[-1] == last]
    cost_names = []
    for oi, order in enumerate(orders):
        committed: list[int] = []
        terms = []
        for step, j in enumerate(order):
            below = [i for i in committed if i < j]
            lo = max(below) if below else 0
            q = p - step
            terms.append(c_term(gap_expr(lo, j), q, mutate=mutate))
            committed.append(j)
        body = "(+ " + " ".join(terms) + ")" if len(terms) > 1 else terms[0]
        cn = f"{name}c{oi}"
        lines.append(f"(declare-const {cn} Int)")
        lines.append(f"(assert (= {cn} {body}))")
        cost_names.append(cn)
    lines.append(f"(declare-const {name} Int)")
    for cn in cost_names:
        lines.append(f"(assert (<= {name} {cn}))")
    lines.append("(assert (or " + " ".join(f"(= {name} {cn})" for cn in cost_names) + "))")
    return name


def build_smt(
    p: int,
    m: int,
    ix: int,
    lemma: str,
    *,
    mutate: str | None = None,
    corner: bool = False,
) -> str:
    """T = {t_1<…<t_m}, x = t_ix。lemma='A': d_ix=1 で W(T∖x) ≤ W(T) の否定。
    lemma='B': d_ix≥2 で W(T∖x) ≤ W(T)+1 の否定。

    corner=True では T 側の順序を「紙の共同帰納法で閉じない残る角」に限定する
    （`data/conj_u_status.md` §2.5。A: 支持 t_{ix-1} が最後、B: 直上 t_{ix+1} が
    最後）。他のケースは紙で全 p について閉じているので、角の unsat がその p の
    補題全体を（紙と合わせて）与える。順序空間が (m-1)! に縮むので高い p が届く。
    """
    lines = ["(set-logic QF_LIA)"]
    for i in range(1, m + 1):
        lines.append(f"(declare-const d{i} Int)")
        lines.append(f"(assert (and (>= d{i} 1) (<= d{i} {DMAX})))")
    if lemma == "A":
        lines.append(f"(assert (= d{ix} 1))")
        slack = 0
        last = (ix - 1) if corner else None
    else:
        lines.append(f"(assert (>= d{ix} 2))")
        slack = 0 if mutate == "b0" else 1
        last = (ix + 1) if corner else None
    all_idx = list(range(1, m + 1))
    rest = [i for i in all_idx if i != ix]
    w_t = min_cost_def(
        "wt", all_idx, p, lines,
        mutate=mutate if mutate == "thresh" else None, last=last,
    )
    # corner='aprime' 相当（呼び出し側で s_last を渡す将来拡張用）:
    # A′ = S 側も x-1 を最後に固定した弱い十分条件（conj_u_status.md §2.5）
    s_last = (ix - 1) if (corner and lemma == "A" and mutate == "aprime") else None
    w_s = min_cost_def("ws", rest, p, lines, last=s_last) if rest else "0"
    # 否定: W(T∖x) > W(T) + slack
    lines.append(f"(assert (> {w_s} (+ {w_t} {slack})))")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def run_solver(smt: str, solver: str, timeout: int) -> str:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".smt2", delete=False, dir=tempfile.gettempdir()
    ) as f:
        f.write(smt)
        path = Path(f.name)
    cmd = {
        "z3": ["z3", f"-T:{timeout}", str(path)],
        "cvc5": ["cvc5", f"--tlimit={timeout*1000}", str(path)],
    }[solver]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout + 30)
        txt = out.stdout.strip().splitlines()
        return txt[-1] if txt else "(no output)"
    except subprocess.TimeoutExpired:
        return "timeout"
    finally:
        path.unlink(missing_ok=True)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, default=3)
    ap.add_argument("--solver", choices=["z3", "cvc5", "both"], default="both")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--mutation", action="store_true")
    ap.add_argument("--corner", action="store_true", help="§2.5 の残る角のみ検証")
    args = ap.parse_args()
    solvers = ["z3", "cvc5"] if args.solver == "both" else [args.solver]

    if args.mutation:
        print("== ミューテーション検査（偽命題が sat になることを確認）==")
        for name, kw in [
            ("補題B の +1 を +0 に弱める (p=3,m=2,ix=1)", dict(p=3, m=2, ix=1, lemma="B", mutate="b0")),
            ("C の閾値 2^{q-1} を +1 ずらす (p=4,m=3,ix=2, 補題A)", dict(p=4, m=3, ix=2, lemma="A", mutate="thresh")),
        ]:
            smt = build_smt(**kw)
            for s in solvers:
                r = run_solver(smt, s, args.timeout)
                mark = "ok（検出）" if r == "sat" else f"★検出失敗: {r}★"
                print(f"  {s:<5} {name}: {r} {mark}")
        return 0

    p = args.p
    fails = 0
    mode = "角限定（§2.5 の残るケースのみ）" if args.corner else "全ケース"
    print(f"== p={p}: 補題 A・B の SMT 検証（ギャップ 1..2^20、{mode}）==")
    for lemma in ["A", "B"]:
        for m in range(1 if lemma == "B" else 2, p + 1):
            lo = 2 if (args.corner and lemma == "A") else 1
            hi = (m - 1) if (args.corner and lemma == "B") else m
            for ix in range(lo, hi + 1):
                smt = build_smt(p, m, ix, lemma, corner=args.corner)
                results = {s: run_solver(smt, s, args.timeout) for s in solvers}
                ok = all(r == "unsat" for r in results.values())
                if not ok:
                    fails += 1
                print(
                    f"  補題{lemma} |T|={m} x=第{ix}要素: "
                    + "  ".join(f"{s}:{r}" for s, r in results.items())
                    + ("" if ok else "  ★"),
                    flush=True,
                )
    print(f"{'全件 unsat（補題成立）' if fails == 0 else f'未確定/反例 {fails} 件'}")
    return 1 if fails else 0


if __name__ == "__main__":
    raise SystemExit(main())
