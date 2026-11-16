"""定理 A の下界を **機械検証可能な証明書つき**で確認する（SAT + DRAT）。

## なぜ CP-SAT では足りないのか

CP-SAT の `INFEASIBLE` は「ソルバがそう言った」であり、**第三者が検査できる証明ではない**。
`docs/31_tool_import.md` §10.4 の原則:

> 上界側（構成を見つける）は未成熟な道具でよい。検証器があるので嘘が排除できる。
> **下界側（存在しないことを示す）は成熟した道具が必須。証明ログか定理証明器を使う。**

SAT ソルバは UNSAT に対し **DRAT 証明**を出力でき、独立な検査器（drat-trim）が検証する。
本モジュールは「$2n-1$ 手のスケジュールが存在する」を CNF に符号化し、
UNSAT なら **証明書つきで下界が確定**する。

## 符号化

$M^*=2A-1$ かつ $A\\ge n$（各頂点は少なくとも1回置かれる）なので、
**「$2n-1$ 手で可能」⟺「各頂点をちょうど1回置くスケジュールが存在」**。
時刻 $t=0..T$（$T=2n-1$）で、毎ステップちょうど1手。

| 変数 | 意味 |
|---|---|
| `x[t][v]` | 時刻 $t$ に $v$ がペブル済み |
| `put[t][v]` / `take[t][v]` | ステップ $t$ で $v$ を置く / 外す |
| `av[t][v]` | 時刻 $t$ に $v$ の全先行点がペブル済み |
| `irr[t][v]` | その `take` が不可逆消去 |

濃度制約（ピーク $\\le p$、消去 $\\le e$）は **Sinz の逐次カウンタ**で符号化する。

使い方:
    python3 scripts/sat_lower_bound.py --n 20 --p 6 --e 2
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from revpebble import Dag, chain  # noqa: E402

CADICAL = "cadical"
DRAT_TRIM = Path.home() / "dev/infra/tools/drat-trim/drat-trim"


class Cnf:
    """最小限の CNF ビルダ（DIMACS 出力）。"""

    def __init__(self) -> None:
        self.n = 0
        self.clauses: list[list[int]] = []

    def var(self) -> int:
        self.n += 1
        return self.n

    def add(self, *lits: int) -> None:
        self.clauses.append(list(lits))

    def add_list(self, lits: list[int]) -> None:
        self.clauses.append(list(lits))

    def at_most_k(self, lits: list[int], k: int) -> None:
        """Sinz の逐次カウンタによる $\\sum lits \\le k$。"""
        if k >= len(lits):
            return
        if k == 0:
            for lit in lits:
                self.add(-lit)
            return
        n = len(lits)
        s = [[self.var() for _ in range(k)] for _ in range(n)]
        # s[i][j] = 「先頭 i+1 個のうち j+1 個以上が真」
        self.add(-lits[0], s[0][0])
        for j in range(1, k):
            self.add(-s[0][j])
        for i in range(1, n):
            self.add(-lits[i], s[i][0])
            self.add(-s[i - 1][0], s[i][0])
            for j in range(1, k):
                self.add(-lits[i], -s[i - 1][j - 1], s[i][j])
                self.add(-s[i - 1][j], s[i][j])
            self.add(-lits[i], -s[i - 1][k - 1])

    def exactly_one(self, lits: list[int]) -> None:
        self.add_list(lits)
        self.at_most_k(lits, 1)

    def dimacs(self) -> str:
        head = f"p cnf {self.n} {len(self.clauses)}\n"
        body = "".join(" ".join(map(str, c)) + " 0\n" for c in self.clauses)
        return head + body


def encode(dag: Dag, target: int, p: int, e: int, moves: int) -> Cnf:
    """「ピーク $\\le p$・消去 $\\le e$ で ちょうど `moves` 手」の充足可能性を CNF に。"""
    verts = list(dag.pebbleable())
    T = moves
    c = Cnf()
    x = {(t, v): c.var() for t in range(T + 1) for v in verts}
    put = {(t, v): c.var() for t in range(T) for v in verts}
    take = {(t, v): c.var() for t in range(T) for v in verts}
    av = {(t, v): c.var() for t in range(T + 1) for v in verts}
    irr = {(t, v): c.var() for t in range(T) for v in verts}

    # 初期・終端
    for v in verts:
        c.add(-x[0, v])
        c.add(x[T, v] if v == target else -x[T, v])

    # 可用性: av[t][v] <=> AND(x[t][u] for u in preds)
    for t in range(T + 1):
        for v in verts:
            need = [x[t, u] for u in dag.preds[v] if u not in dag.free]
            if not need:
                c.add(av[t, v])  # 常に可用
                continue
            for lit in need:  # av → 各 need
                c.add(-av[t, v], lit)
            c.add_list([av[t, v]] + [-lit for lit in need])  # 全 need → av

    for t in range(T):
        # 毎ステップちょうど1手
        c.exactly_one([put[t, v] for v in verts] + [take[t, v] for v in verts])
        for v in verts:
            # put: 0→1、take: 1→0
            c.add(-put[t, v], -x[t, v])
            c.add(-put[t, v], x[t + 1, v])
            c.add(-take[t, v], x[t, v])
            c.add(-take[t, v], -x[t + 1, v])
            # 変化しないなら値は保存
            c.add(put[t, v], take[t, v], -x[t, v], x[t + 1, v])
            c.add(put[t, v], take[t, v], x[t, v], -x[t + 1, v])
            # put は可用性を要求
            c.add(-put[t, v], av[t, v])
            # take ∧ ¬av → irr
            c.add(-take[t, v], av[t, v], irr[t, v])
            # irr → take かつ irr → ¬av（irr を必要最小限に）
            c.add(-irr[t, v], take[t, v])
            c.add(-irr[t, v], -av[t, v])

    # ピーク制約
    for t in range(T + 1):
        c.at_most_k([x[t, v] for v in verts], p)
    # 消去予算
    c.at_most_k([irr[t, v] for t in range(T) for v in verts], e)
    return c


def run(cnf: Cnf, workdir: Path, tag: str, *, timeout: float = 300.0) -> dict:
    """CaDiCaL で解き、UNSAT なら drat-trim で証明を独立検証する。"""
    workdir.mkdir(parents=True, exist_ok=True)
    f_cnf = workdir / f"{tag}.cnf"
    f_prf = workdir / f"{tag}.drat"
    f_cnf.write_text(cnf.dimacs())
    out = subprocess.run(
        [CADICAL, "--binary=false", "-q", str(f_cnf), str(f_prf)],
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    verdict = "UNKNOWN"
    for line in out.stdout.splitlines():
        if line.startswith("s "):
            verdict = line[2:].strip()
    res = {
        "verdict": verdict,
        "vars": cnf.n,
        "clauses": len(cnf.clauses),
        "proof_bytes": f_prf.stat().st_size if f_prf.exists() else 0,
        "checked": None,
    }
    if verdict == "UNSATISFIABLE" and DRAT_TRIM.exists():
        chk = subprocess.run(
            [str(DRAT_TRIM), str(f_cnf), str(f_prf)],
            capture_output=True,
            text=True,
            timeout=timeout * 4,
        )
        res["checked"] = "VERIFIED" if "s VERIFIED" in chk.stdout else "FAILED"
    return res


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--p", type=int, default=5)
    ap.add_argument("--e", type=int, default=None, help="省略時は e*-1 と e* の両方")
    ap.add_argument("--timeout", type=float, default=300.0)
    ap.add_argument(
        "--workdir",
        type=Path,
        default=Path("/tmp/claude-1000/-work-a-dev/sat_lb"),
    )
    args = ap.parse_args()

    from math import ceil

    estar = ceil((args.n - 1) / (args.p - 1)) - 1
    es = [args.e] if args.e is not None else [estar - 1, estar]
    print(f"鎖 n={args.n}, p={args.p}, 定理A の e* = {estar}、手数 = {2*args.n-1}")
    for e in es:
        cnf = encode(chain(args.n), args.n, args.p, e, 2 * args.n - 1)
        r = run(cnf, args.workdir, f"n{args.n}p{args.p}e{e}", timeout=args.timeout)
        note = "（下界が証明された）" if r["verdict"] == "UNSATISFIABLE" else ""
        print(
            f"  e={e}: {r['verdict']:<15} 変数 {r['vars']:>7} 節 {r['clauses']:>8} "
            f"証明 {r['proof_bytes']:>9} B  drat-trim: {r['checked']} {note}"
        )


if __name__ == "__main__":
    main()
