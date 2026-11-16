#!/usr/bin/env python3
"""spooky pebbling の最短手数を SAT で決める（BFS の 3^n が効かない領域用）。

    python3 sat_spooky.py --calibrate          # BFS 既知値で符号化を校正（必須）
    python3 sat_spooky.py --exact 21 6 UP 73   # T=73 で SAT、T=72 で UNSAT を示す

**下界（非存在）側は DRAT 証明ログを出して drat-trim で検証する**
（`~/.claude/rules` の方針: 非存在の主張は証明ログか定理証明器で担保する）。

## 符号化

時刻 $t=0..T$、頂点 $v=1..n$ について状態変数 $P[t][v]$（ペブル）・$G[t][v]$（ゴースト）。
各時刻の遷移は **1 つの行動**（`pebble` / `unpebble` / `ghost` / `unghost` / `nop`）。
`nop` を入れてあるので「$T$ 手ちょうど」が「$T$ 手以内」と同じになり、
**UNSAT は「$T$ 手以内の解が無い」を意味する**（パリティで偶奇が飛ぶ問題を避けるため）。

- `pebble(v)`  前提 $\\lnot P\\land\\lnot G\\land(v{=}1\\lor P[v{-}1])$、効果 $P'$
- `unpebble(v)` 前提 $P\\land(v{=}1\\lor P[v{-}1])$、効果 $\\lnot P'$
- `ghost(v)`   前提 $P$、効果 $\\lnot P'\\land G'$
- `unghost(v)` 前提 $G\\land(v{=}1\\lor P[v{-}1])$、効果 $P'\\land\\lnot G'$
- フレーム: 触られていない頂点は状態を保つ
- 各時刻 $|P_t|\\le s$（逐次カウンタ）
"""
from __future__ import annotations

import argparse
import subprocess
import tempfile
from pathlib import Path

OPS = ("pebble", "unpebble", "ghost", "unghost", "nop")


class CNF:
    def __init__(self) -> None:
        self.n = 0
        self.cls: list[list[int]] = []

    def var(self) -> int:
        self.n += 1
        return self.n

    def add(self, *lits: int) -> None:
        self.cls.append(list(lits))

    def amo_pairwise(self, xs: list[int]) -> None:
        for i in range(len(xs)):
            for j in range(i + 1, len(xs)):
                self.add(-xs[i], -xs[j])

    def atmost_k(self, xs: list[int], k: int) -> None:
        """逐次カウンタ（Sinz 2005）。s[i][j] = 「x_1..x_i の真が j 個以上」。"""
        n = len(xs)
        if k >= n:
            return
        if k == 0:
            for x in xs:
                self.add(-x)
            return
        s = [[self.var() for _ in range(k)] for _ in range(n)]
        self.add(-xs[0], s[0][0])
        for j in range(1, k):
            self.add(-s[0][j])
        for i in range(1, n):
            self.add(-xs[i], s[i][0])
            self.add(-s[i - 1][0], s[i][0])
            for j in range(1, k):
                self.add(-xs[i], -s[i - 1][j - 1], s[i][j])
                self.add(-s[i - 1][j], s[i][j])
            self.add(-xs[i], -s[i - 1][k - 1])


def build(n: int, s: int, T: int, start: dict, goal: dict) -> tuple[CNF, dict]:
    """start / goal は {v: 'P'|'G'} の辞書（書かれていない頂点は空）。"""
    f = CNF()
    P = [[f.var() for _ in range(n + 1)] for _ in range(T + 1)]
    G = [[f.var() for _ in range(n + 1)] for _ in range(T + 1)]
    A = [{op: [f.var() for _ in range(n + 1)] for op in OPS} for _ in range(T)]

    for t in range(T + 1):
        for v in range(1, n + 1):
            f.add(-P[t][v], -G[t][v])
        f.atmost_k([P[t][v] for v in range(1, n + 1)], s)

    def fix(t: int, st: dict) -> None:
        for v in range(1, n + 1):
            want = st.get(v)
            f.add(P[t][v] if want == "P" else -P[t][v])
            f.add(G[t][v] if want == "G" else -G[t][v])

    fix(0, start)
    fix(T, goal)

    for t in range(T):
        acts = [A[t][op][v] for op in OPS for v in range(1, n + 1)
                if not (op == "nop" and v > 1)]
        f.add(*acts)                      # 少なくとも 1 つ
        f.amo_pairwise(acts)              # 高々 1 つ
        for v in range(2, n + 1):
            f.add(-A[t]["nop"][v])        # nop は v=1 の1本だけ使う

        def ready(v: int) -> int | None:
            return None if v == 1 else P[t][v - 1]

        for v in range(1, n + 1):
            r = ready(v)
            # pebble
            a = A[t]["pebble"][v]
            f.add(-a, -P[t][v])
            f.add(-a, -G[t][v])
            f.add(-a, P[t + 1][v])
            if r is not None:
                f.add(-a, r)
            # unpebble
            a = A[t]["unpebble"][v]
            f.add(-a, P[t][v])
            f.add(-a, -P[t + 1][v])
            if r is not None:
                f.add(-a, r)
            # ghost
            a = A[t]["ghost"][v]
            f.add(-a, P[t][v])
            f.add(-a, -P[t + 1][v])
            f.add(-a, G[t + 1][v])
            # unghost
            a = A[t]["unghost"][v]
            f.add(-a, G[t][v])
            f.add(-a, P[t + 1][v])
            f.add(-a, -G[t + 1][v])
            if r is not None:
                f.add(-a, r)
            # フレーム: v に触る行動が無ければ状態は不変
            touch = [A[t][op][v] for op in ("pebble", "unpebble", "ghost", "unghost")]
            for a, b in ((P[t][v], P[t + 1][v]), (G[t][v], G[t + 1][v])):
                f.add(*touch, -a, b)
                f.add(*touch, a, -b)
    return f, {"P": P, "G": G, "A": A}


def run(f: CNF, proof: Path | None) -> str:
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as fh:
        fh.write(f"p cnf {f.n} {len(f.cls)}\n")
        fh.write("".join(" ".join(map(str, c)) + " 0\n" for c in f.cls))
        cnf_path = Path(fh.name)
    cmd = ["cadical", "-q", str(cnf_path)] + ([str(proof)] if proof else [])
    p = subprocess.run(cmd, capture_output=True, text=True)
    out = p.stdout
    verdict = "SAT" if "s SATISFIABLE" in out else (
        "UNSAT" if "s UNSATISFIABLE" in out else f"不明(rc={p.returncode})")
    if verdict == "UNSAT" and proof:
        v = subprocess.run(["drat-trim", str(cnf_path), str(proof)],
                           capture_output=True, text=True, timeout=3600)
        ok = "s VERIFIED" in v.stdout
        verdict += " / DRAT " + ("検証済み" if ok else f"検証失敗: {v.stdout[-200:]}")
    cnf_path.unlink(missing_ok=True)
    return verdict


def states(n: int, kind: str) -> tuple[dict, dict]:
    if kind == "P":       # 空 → v_n にペブル
        return {}, {n: "P"}
    if kind == "UP":      # v_n にペブル → 空
        return {n: "P"}, {}
    if kind == "UG":      # v_n にゴースト → 空
        return {n: "G"}, {}
    raise SystemExit(f"kind は P/UP/UG: {kind}")


def exact(n: int, s: int, kind: str, T: int, proof_dir: Path | None) -> int:
    st, go = states(n, kind)
    print(f"n={n} s={s} {kind}: T={T} が SAT、T={T - 1} が UNSAT なら厳密値は {T}")
    f, _ = build(n, s, T, st, go)
    print(f"  T={T}:   変数 {f.n} 節 {len(f.cls)} … ", end="", flush=True)
    up = run(f, None)
    print(up, flush=True)
    f2, _ = build(n, s, T - 1, st, go)
    proof = (proof_dir / f"{kind}_{n}_{s}_{T - 1}.drat") if proof_dir else None
    print(f"  T={T - 1}: 変数 {f2.n} 節 {len(f2.cls)} … ", end="", flush=True)
    lo = run(f2, proof)
    print(lo, flush=True)
    ok = up == "SAT" and lo.startswith("UNSAT")
    print(f"  → {'厳密値 = ' + str(T) if ok else '⚠ 予測と一致しない'}")
    return 0 if ok else 1


def calibrate(proof_dir: Path | None) -> int:
    """BFS で確定している値で符号化を校正する。ここが緑でなければ以下は無効。"""
    cases = [(4, 3, "P", 9), (6, 3, "P", 27), (9, 4, "UP", 27), (9, 4, "UG", 28),
             (10, 4, "UP", 33), (10, 4, "UG", 32)]
    bad = 0
    for n, s, kind, T in cases:
        bad |= exact(n, s, kind, T, proof_dir)
    print("\n校正: " + ("すべて一致" if not bad else "⚠ 不一致あり。符号化を直すこと"))
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--calibrate", action="store_true")
    ap.add_argument("--exact", nargs=4, metavar=("N", "S", "KIND", "T"))
    ap.add_argument("--proofs", type=Path, default=None, help="DRAT の置き場")
    a = ap.parse_args()
    if a.proofs:
        a.proofs.mkdir(parents=True, exist_ok=True)
    if a.calibrate:
        return calibrate(a.proofs)
    if a.exact:
        n, s, kind, T = int(a.exact[0]), int(a.exact[1]), a.exact[2], int(a.exact[3])
        return exact(n, s, kind, T, a.proofs)
    ap.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
