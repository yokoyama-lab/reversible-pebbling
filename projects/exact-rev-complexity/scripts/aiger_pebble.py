"""$e$-消去ペブリングを AIGER で出力し、ABC の PDR で**帰納的不変量**を取り出す。

## なぜ自前で AIGER を書くのか

`data/ic3_b2_findings.md` §3 のとおり:
- nuXmv の `check_invar_ic3` は**不変量をダンプしない**。
- ABC の `pdr -I <file>` は書き出せるが、nuXmv の `write_aiger_model` が出す AIGER には
  **liveness property が含まれ** ABC が拒否する。

→ 自前で AIGER を出せば ABC に直接渡せる。**不変量は「なぜ先へ進めないか」を述べる述語**で、
人間が一般 $n$・一般 $p$ の証明に育てる素材になる（予想 B2 の証明への最短路）。

## 設計の要点: 加算器を使わない

ピーク制約には「ペブル数 $< p$」の判定が要るが、**AIGER で population count を作ると重い**。
本実装は次の観察で回避する:

> 毎ステップちょうど 1 個のペブルが増減するので、
> ペブル数は**ユニタリのシフトレジスタ**で保持できる。

- `v_1..v_p`（$v_i$ = 「ペブル数 $\\ge i$」、単調減少に保つ）: put で左シフト、take で右シフト。
  ピーク制約は $\\lnot v_p$ の一本で済む。
- 消去数も同様に `u_1..u_e` のシフトレジスタ。予算判定は $\\lnot u_e$。

これで**全遷移が単純なゲートだけ**になる（加算器・比較器が不要）。

## AIGER の約束

- 変数 $v$ のリテラルは $2v$、否定は $2v+1$。定数 false = 0、true = 1。
- ヘッダ `aag M I L O A`、入力→ラッチ→出力→AND の順。ラッチの初期値は既定 0。
- 出力は **bad state**（1 になったら性質違反）。ABC の `pdr` はこれが到達不能かを判定する。

使い方:
    python3 scripts/aiger_pebble.py --p 3 --e 0 --n 5 --invariant
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

ABC = Path.home() / "dev/infra/tools/abc/abc"

TRUE = 1
FALSE = 0


class Aig:
    """最小限の AIGER ビルダ（ASCII .aag）。"""

    def __init__(self) -> None:
        self.next_var = 1
        self.inputs: list[int] = []
        self.latches: list[tuple[int, int | None]] = []  # (cur_lit, next_lit)
        self.ands: list[tuple[int, int, int]] = []
        self.outputs: list[int] = []

    def _new(self) -> int:
        lit = 2 * self.next_var
        self.next_var += 1
        return lit

    def input(self) -> int:
        lit = self._new()
        self.inputs.append(lit)
        return lit

    def latch(self) -> int:
        lit = self._new()
        self.latches.append((lit, None))
        return lit

    def set_next(self, cur: int, nxt: int) -> None:
        for i, (c, _) in enumerate(self.latches):
            if c == cur:
                self.latches[i] = (c, nxt)
                return
        raise KeyError(f"ラッチが見つからない: {cur}")

    @staticmethod
    def neg(lit: int) -> int:
        return lit ^ 1

    def and_(self, a: int, b: int) -> int:
        if a == FALSE or b == FALSE:
            return FALSE
        if a == TRUE:
            return b
        if b == TRUE:
            return a
        if a == b:
            return a
        if a == self.neg(b):
            return FALSE
        lit = self._new()
        self.ands.append((lit, a, b))
        return lit

    def or_(self, a: int, b: int) -> int:
        return self.neg(self.and_(self.neg(a), self.neg(b)))

    def and_all(self, lits: list[int]) -> int:
        acc = TRUE
        for lit in lits:
            acc = self.and_(acc, lit)
        return acc

    def or_all(self, lits: list[int]) -> int:
        acc = FALSE
        for lit in lits:
            acc = self.or_(acc, lit)
        return acc

    def mux(self, cond: int, then_lit: int, else_lit: int) -> int:
        return self.or_(
            self.and_(cond, then_lit), self.and_(self.neg(cond), else_lit)
        )

    def output(self, lit: int) -> None:
        self.outputs.append(lit)

    def binary(self) -> bytes:
        """バイナリ AIGER（`.aig`）を出力する。**ABC の `read_aiger` は ASCII を受け付けない。**

        バイナリ形式の要点:
        - AND ゲートの lhs は入力・ラッチの後に**連番**で並ぶ必要がある
          （本ビルダは inputs → latches → ands の順に変数を割り当てるので満たされる）。
        - 各 AND は `rhs0 >= rhs1` に正規化し、`delta0 = lhs-rhs0`, `delta1 = rhs0-rhs1` を
          **可変長符号**（7 ビット/バイト、MSB が継続ビット）で書く。
        """

        def varint(x: int) -> bytes:
            out = bytearray()
            while x & ~0x7F:
                out.append((x & 0x7F) | 0x80)
                x >>= 7
            out.append(x)
            return bytes(out)

        m = self.next_var - 1
        head = (
            f"aig {m} {len(self.inputs)} {len(self.latches)} "
            f"{len(self.outputs)} {len(self.ands)}\n"
        ).encode()
        body = bytearray()
        for cur, nxt in self.latches:
            if nxt is None:
                raise ValueError(f"ラッチ {cur} の next が未設定")
            body += f"{nxt}\n".encode()
        for o in self.outputs:
            body += f"{o}\n".encode()
        for lhs, a, b in self.ands:
            r0, r1 = (a, b) if a >= b else (b, a)
            assert lhs > r0 >= r1, f"AND の順序が不正: {lhs} {r0} {r1}"
            body += varint(lhs - r0) + varint(r0 - r1)
        return head + bytes(body)

    def aag(self, names: dict[int, str] | None = None) -> str:
        m = self.next_var - 1
        head = (
            f"aag {m} {len(self.inputs)} {len(self.latches)} "
            f"{len(self.outputs)} {len(self.ands)}"
        )
        lines = [head]
        lines += [str(i) for i in self.inputs]
        for cur, nxt in self.latches:
            if nxt is None:
                raise ValueError(f"ラッチ {cur} の next が未設定")
            lines.append(f"{cur} {nxt}")
        lines += [str(o) for o in self.outputs]
        lines += [f"{lhs} {a} {b}" for lhs, a, b in self.ands]
        if names:
            for lit, nm in sorted(names.items()):
                kind = None
                if lit in self.inputs:
                    kind = f"i{self.inputs.index(lit)}"
                else:
                    for k, (c, _) in enumerate(self.latches):
                        if c == lit:
                            kind = f"l{k}"
                            break
                if kind:
                    lines.append(f"{kind} {nm}")
        return "\n".join(lines) + "\n"


def build(n: int, p: int, e: int) -> tuple[Aig, dict[int, str]]:
    """鎖 $0..n$（節点 0 は常時可用な源）の $e$-消去ペブリングを AIGER にする。"""
    g = Aig()
    names: dict[int, str] = {}

    sel = []
    for i in range(1, n + 1):
        lit = g.input()
        names[lit] = f"sel{i}"
        sel.append(lit)
    act = g.input()
    names[act] = "act_is_put"

    x = {}
    for i in range(1, n + 1):
        x[i] = g.latch()
        names[x[i]] = f"x{i}"
    v = {}
    for i in range(1, p + 1):
        v[i] = g.latch()
        names[v[i]] = f"cnt_ge{i}"
    u = {}
    for i in range(1, e + 1):
        u[i] = g.latch()
        names[u[i]] = f"era_ge{i}"

    # ちょうど1つの sel が立っている
    prefix = FALSE
    amo_terms = []
    for lit in sel:
        amo_terms.append(g.neg(g.and_(lit, prefix)))
        prefix = g.or_(prefix, lit)
    exactly1 = g.and_(g.and_all(amo_terms), prefix)

    room = g.neg(v[p]) if p >= 1 else FALSE  # ペブル数 < p
    budget = g.neg(u[e]) if e >= 1 else FALSE  # 消去予算が残っている

    do_put, do_take, do_era = [], [], []
    for i in range(1, n + 1):
        avail = TRUE if i == 1 else x[i - 1]
        can_put = g.and_all([g.neg(x[i]), avail, room])
        irr = g.and_(x[i], g.neg(avail))
        can_take = g.and_(x[i], g.or_(avail, budget))
        chosen = g.and_(exactly1, sel[i - 1])
        dp = g.and_(g.and_(chosen, act), can_put)
        dt = g.and_(g.and_(chosen, g.neg(act)), can_take)
        do_put.append(dp)
        do_take.append(dt)
        do_era.append(g.and_(dt, irr))
        # next(x_i) = (x_i ∨ put) ∧ ¬take
        g.set_next(x[i], g.and_(g.or_(x[i], dp), g.neg(dt)))

    any_put = g.or_all(do_put)
    any_take = g.or_all(do_take)
    any_era = g.or_all(do_era)

    # ペブル数のユニタリシフトレジスタ
    for i in range(1, p + 1):
        shift_in = TRUE if i == 1 else v[i - 1]
        shift_out = v[i + 1] if i + 1 <= p else FALSE
        keep = g.and_(g.neg(any_put), g.neg(any_take))
        g.set_next(
            v[i],
            g.or_all(
                [
                    g.and_(any_put, shift_in),
                    g.and_(any_take, shift_out),
                    g.and_(keep, v[i]),
                ]
            ),
        )
    # 消去数のユニタリシフトレジスタ
    for i in range(1, e + 1):
        shift_in = TRUE if i == 1 else u[i - 1]
        g.set_next(u[i], g.or_(g.and_(any_era, shift_in), g.and_(g.neg(any_era), u[i])))

    # bad state: 節点 n のみがペブル済み（= clean 到達）
    bad = g.and_all([x[n]] + [g.neg(x[i]) for i in range(1, n)])
    g.output(bad)
    return g, names


def run_pdr(g: Aig, workdir: Path, tag: str, *, timeout: float = 600.0) -> dict:
    workdir.mkdir(parents=True, exist_ok=True)
    f = workdir / f"{tag}.aig"
    inv = workdir / f"{tag}.inv"
    f.write_bytes(g.binary())
    cmd = f"read_aiger {f}; print_stats; pdr -I {inv}"
    out = subprocess.run(
        [str(ABC), "-c", cmd], capture_output=True, text=True, timeout=timeout
    )
    txt = out.stdout
    verdict = "UNKNOWN"
    if "Property proved" in txt:
        verdict = "UNREACHABLE"
    elif "Output 0 of miter" in txt and "was asserted" in txt:
        verdict = "REACHABLE"
    elif "was asserted in frame" in txt:
        verdict = "REACHABLE"
    return {
        "verdict": verdict,
        "invariant": inv.read_text() if inv.exists() else None,
        "stdout": txt,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--e", type=int, default=0)
    ap.add_argument("--n", type=int, default=None)
    ap.add_argument("--invariant", action="store_true", help="不変量を表示")
    ap.add_argument("--timeout", type=float, default=600.0)
    ap.add_argument(
        "--workdir", type=Path, default=Path("/tmp/claude-1000/-work-a-dev/aiger")
    )
    args = ap.parse_args()

    claim = (args.e + 2) * 2 ** (args.p - 2)
    ns = [args.n] if args.n else [claim, claim + 1]
    print(f"予想 B2: reach(p={args.p}, e={args.e}) = {claim}")
    for n in ns:
        g, _ = build(n, args.p, args.e)
        r = run_pdr(g, args.workdir, f"p{args.p}e{args.e}n{n}", timeout=args.timeout)
        expect = "REACHABLE" if n <= claim else "UNREACHABLE"
        mark = "○" if r["verdict"] == expect else ("—" if r["verdict"] == "UNKNOWN" else "**×**")
        print(f"  n={n:>4}: {r['verdict']:<12} 期待 {expect:<12} {mark}")
        if args.invariant and r["invariant"]:
            lines = r["invariant"].splitlines()
            print(f"    不変量: {len(lines)} 行")
            for line in lines[:15]:
                print(f"      {line}")


if __name__ == "__main__":
    main()


def decode_invariant(text: str, n: int, p: int, e: int) -> dict:
    """PDR が出した PLA 形式の不変量を人間可読な含意に直す。

    各行は「この立方体は到達しない」＝節。ラッチの順序は
    `x_1..x_n, cnt_ge1..cnt_ge p, era_ge1..era_ge e`（`build` の割り当て順）。

    返り値の `forbidden` が**本質**（到達しないペブル集合）。
    `counter_bookkeeping` は符号化に由来する簿記（ペブル数とユニタリ計数器の整合）で、
    数学的な内容を持たない。
    """
    names = (
        [f"x{i}" for i in range(1, n + 1)]
        + [f"c>={i}" for i in range(1, p + 1)]
        + [f"u>={i}" for i in range(1, e + 1)]
    )
    rows = [
        ln.split()[0]
        for ln in text.splitlines()
        if ln and ln[0] in "01-" and len(ln.split()) >= 2
    ]
    forbidden: list[frozenset[int]] = []
    support: list[tuple[frozenset[int], list[int]]] = []
    bookkeeping = 0
    for r in rows:
        pos = [i for i, ch in enumerate(r) if ch == "1"]
        neg = [i for i, ch in enumerate(r) if ch == "0"]
        pos_x = [i + 1 for i in pos if i < n]
        neg_x = [i + 1 for i in neg if i < n]
        pos_c = [i for i in pos if i >= n]
        neg_c = [i for i in neg if i >= n]
        if not neg:  # 無条件に禁止された配置
            forbidden.append(frozenset(pos_x))
        elif neg_x and not neg_c and not pos_c:
            # 「pos_x が載っているなら neg_x のどれかも載っている」＝支持の要求
            support.append((frozenset(pos_x), neg_x))
        else:
            bookkeeping += 1
    return {
        "names": names,
        "clauses": len(rows),
        "forbidden": forbidden,
        "support": support,
        "counter_bookkeeping": bookkeeping,
    }
