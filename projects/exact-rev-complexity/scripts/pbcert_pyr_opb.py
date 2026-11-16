#!/usr/bin/env python3
"""ピラミッドのピーク下界を **OPB（擬似ブール）** と **CNF** の両方に落とす（2026-09-05）。

`q2_pyr_lower_cert.py` の抽象（層ごとの個数 `a_k(t)`・変化数 `c_k(t)` の順序符号化）を
**まったく同じ順序・同じ変数番号**で組み、最後の**ピーク制約だけ**を 2 通りに書き分ける:

| 経路 | ピーク制約 `Σ_{k,j} A[k][t][j] <= B` | 補助変数 |
|---|---|---|
| CNF | Sinz (2005) の逐次カウンタ | **要る**（`n·B` 個 × 各 t） |
| OPB | **そのまま基数制約 1 本** | 要らない |

これが「ピラミッドのピーク制約は基数制約そのものなので、擬似ブール証明にすれば
DRAT より証明が小さくなるはず」という仮説を測るための対である。

⚠ **この抽象は緩和**なので、「ピーク <= B が実行不能」は `p_min >= B+1` を意味する。
逆は言えない（実行可能でも本物のペブリングがあるとは限らない）。

`--check` は生成した CNF が `q2_pyr_lower_cert.build` の出力と**節単位で一致**することを
確かめる（二重実装での照合。ここがずれていたら以降の比較は無意味）。
"""
from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


class PB:
    """PB 制約の共通中間形。

    - `clause(*lits)`  : `Σ lit >= 1`
    - `atmost(lits, k)`: `Σ lit <= k`（OPB では基数制約 1 本、CNF では Sinz 展開）

    変数番号の払い出し順は `q2_cnf.Cnf` と揃えてある（照合のため）。
    """

    def __init__(self) -> None:
        self.n = 0
        self.items: list[tuple] = []          # ("cl", lits) / ("am", lits, k)

    def new(self) -> int:
        self.n += 1
        return self.n

    def clause(self, *lits: int) -> None:
        self.items.append(("cl", list(lits)))

    def atmost(self, lits: list[int], k: int) -> None:
        self.items.append(("am", list(lits), k))

    # ---- 出力 ----------------------------------------------------------
    def dump_opb(self, path: str) -> tuple[int, int]:
        """基数制約はそのまま 1 本で書く（補助変数ゼロ）。"""
        lines = []
        for it in self.items:
            if it[0] == "cl":
                terms = " ".join(_opb_term(l) for l in it[1])
                lines.append(f"{terms} >= 1 ;")
            else:
                _, lits, k = it
                # Σ lit <= k  ⇔  Σ ~lit >= |lits| - k
                terms = " ".join(_opb_term(-l) for l in lits)
                lines.append(f"{terms} >= {len(lits) - k} ;")
        with open(path, "w") as f:
            f.write(f"* #variable= {self.n} #constraint= {len(lines)}\n")
            f.write("\n".join(lines) + "\n")
        return self.n, len(lines)

    def to_cnf(self) -> tuple[int, list[list[int]]]:
        """Sinz の逐次カウンタで基数制約を展開する（`q2_cnf.Cnf.atmost` と同一）。"""
        n = self.n
        cls: list[list[int]] = []

        def new() -> int:
            nonlocal n
            n += 1
            return n

        for it in self.items:
            if it[0] == "cl":
                cls.append(list(it[1]))
                continue
            _, lits, k = it
            m = len(lits)
            if k >= m:
                continue
            if k == 0:
                for lit in lits:
                    cls.append([-lit])
                continue
            s = [[new() for _ in range(k)] for _ in range(m)]
            cls.append([-lits[0], s[0][0]])
            for j in range(1, k):
                cls.append([-s[0][j]])
            for i in range(1, m):
                cls.append([-lits[i], s[i][0]])
                cls.append([-s[i - 1][0], s[i][0]])
                for j in range(1, k):
                    cls.append([-lits[i], -s[i - 1][j - 1], s[i][j]])
                    cls.append([-s[i - 1][j], s[i][j]])
                cls.append([-lits[i], -s[i - 1][k - 1]])
        return n, cls

    def dump_cnf(self, path: str) -> tuple[int, int]:
        n, cls = self.to_cnf()
        with open(path, "w") as f:
            f.write(f"p cnf {n} {len(cls)}\n")
            for c in cls:
                f.write(" ".join(map(str, c)) + " 0\n")
        return n, len(cls)


def _opb_term(lit: int) -> str:
    return f"+1 x{lit}" if lit > 0 else f"+1 ~x{-lit}"


def build(h: int, B: int) -> PB:
    """「拡大性つき抽象でピーク <= B が実行可能」を表す制約系。

    `q2_pyr_lower_cert.build` と**同じ順序で同じ制約**を積む（節は節、
    ピークだけ `atmost` として残す）。
    """
    D = h - 1
    T = 2 * D + 1
    n = [h - k for k in range(h)]
    c = PB()
    A = [[[c.new() for _ in range(n[k] + 1)] for _ in range(T + 1)] for k in range(D + 1)]
    Cv = [[[c.new() for _ in range(n[k] + 1)] for _ in range(T)] for k in range(D + 1)]

    def ge(k, t, j):
        return A[k][t][j] if 1 <= j <= n[k] else None

    for k in range(D + 1):
        for t in range(T + 1):
            for j in range(2, n[k] + 1):                 # 単調性
                c.clause(-A[k][t][j], A[k][t][j - 1])
        for t in range(T):
            for j in range(2, n[k] + 1):
                c.clause(-Cv[k][t][j], Cv[k][t][j - 1])

    for k in range(D + 1):
        for t in range(T + 1):
            if k == D:                                    # sink
                if t < D + 1:
                    c.clause(-A[k][t][1])
                else:
                    c.clause(A[k][t][1])
            else:
                if t < k + 1 or t > 2 * D - k:             # 窓
                    c.clause(-A[k][t][1])
                if t in (k + 1, k + 2, 2 * D - k - 1, 2 * D - k):   # 両端強制
                    c.clause(A[k][t][n[k]])

    for k in range(D + 1):
        for t in range(T):
            for x in range(1, n[k] + 1):                   # c_k(t) >= |Δ a_k(t)|
                for y in range(0, x):
                    d = x - y
                    if d > n[k]:
                        continue
                    hi = ge(k, t + 1, y + 1)
                    c.clause(*([-A[k][t][x]] + ([hi] if hi else []) + [Cv[k][t][d]]))
                    hi2 = ge(k, t, y + 1)
                    c.clause(*([-A[k][t + 1][x]] + ([hi2] if hi2 else []) + [Cv[k][t][d]]))
            if k >= 1:                                     # 拡大性
                for j in range(1, n[k] + 1):
                    if j + 1 <= n[k - 1]:
                        c.clause(-Cv[k][t][j], A[k - 1][t][j + 1])
                        c.clause(-Cv[k][t][j], A[k - 1][t + 1][j + 1])
                    else:
                        c.clause(-Cv[k][t][j])

    for t in range(T + 1):                                 # ピーク <= B
        lits = [A[k][t][j] for k in range(D + 1) for j in range(1, n[k] + 1)]
        c.atmost(lits, B)
    return c


def check_identical(h: int, B: int) -> bool:
    """既存の DRAT 経路（`q2_pyr_lower_cert.build`）と節単位で一致するか。"""
    from q2_pyr_lower_cert import build as build_ref
    ref = build_ref(h, B)
    mine_n, mine_cls = build(h, B).to_cnf()
    ok = (ref.n == mine_n) and (ref.cls == mine_cls)
    if not ok:
        print(f"  h={h} B={B}: **不一致** 変数 {ref.n} vs {mine_n} / "
              f"節 {len(ref.cls)} vs {len(mine_cls)}")
        for i, (a, b) in enumerate(zip(ref.cls, mine_cls)):
            if a != b:
                print(f"    最初の食い違いは節 {i}: {a} vs {b}")
                break
    return ok


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int)
    ap.add_argument("--B", type=int)
    ap.add_argument("--opb")
    ap.add_argument("--cnf")
    ap.add_argument("--check", action="store_true",
                    help="既存の DRAT 経路の CNF と節単位で一致するか照合する")
    a = ap.parse_args()

    if a.check:
        bad = 0
        for h in range(2, 9):
            for B in (2 * h - 2, 2 * h, 2 * h + 2):
                if not check_identical(h, B):
                    bad += 1
        print("照合 OK（生成 CNF は q2_pyr_lower_cert.build と節単位で一致）" if bad == 0
              else f"**照合 NG: {bad} 件**")
        return 1 if bad else 0

    if a.h is None or a.B is None:
        ap.print_help()
        return 2
    c = build(a.h, a.B)
    if a.opb:
        nv, nc = c.dump_opb(a.opb)
        print(f"{a.opb}: {nv} 変数 / {nc} 制約")
    if a.cnf:
        nv, nc = c.dump_cnf(a.cnf)
        print(f"{a.cnf}: {nv} 変数 / {nc} 節")
    if not (a.opb or a.cnf):
        nv, nc = c.n, len(c.items)
        print(f"h={a.h} B={a.B}: OPB {nv} 変数 / {nc} 制約")
    return 0


if __name__ == "__main__":
    sys.exit(main())
