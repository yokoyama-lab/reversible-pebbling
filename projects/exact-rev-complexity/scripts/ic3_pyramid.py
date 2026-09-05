#!/usr/bin/env python3
"""ピラミッド $P_h$ の時間最適並列可逆ペブリングを **遷移系** にして
IC3/PDR（ABC の `pdr` / nuXmv の `check_invar_ic3`）に到達不可能性の
帰納的不変量を自動構成させる（notes/ic3/REQUEST.md）。

**既存の `scripts/q2_cnf.py` は読むだけ**（`pyramid` / `depths` を import する）。
窓・強制・規則・基数制約は `q2_cnf.build(..., window=True)` と**同じもの**を
遷移系に移したものである（`--selftest` でそれを機械的に照合する）。

## 遷移系

状態: `x_v`（$v \\in V$、時刻 $t$ にペブルがあるか）・`t`（2 進カウンタ、$0..T$、
$T = 2h-1$）・`dead`（1 度でも規則を破ったら立つ吸収フラグ）。
入力: `y_v`（次の配置の候補。非決定）。

    legal(x,y)  := ∧_v [ (x_v ⊕ y_v) → ∧_{q∈par(v)} (x_q ∧ y_q) ]
    card(y)     := |y| ≤ p
    win(y,t+1)  := ∧_v [ y_v → lo_v ≤ t+1 ≤ hi_v ] ∧ ∧_{v forced at t+1} y_v
    viol        := ¬legal ∨ ¬card ∨ ¬win
    dead'       := dead ∨ viol
    x'_v        := y_v ∧ ¬dead'        （死んだら全 0 の吸収状態へ落とす）
    t'          := t = T ? T : t+1
    init        := x = 0, t = 0, dead = 0
    bad         := (t = T) ∧ ¬dead

`bad` が到達不能 ⟺ ピーク $\\le p$ の時間最適ペブリングが存在しない ⟺ $p_{\\min} > p$。

⚠ **IC3 が「不変量を見つけられなかった」には 2 種類しかない**:
有限状態系では性質が真なら帰納的不変量は必ず存在する（到達集合そのもの）ので、
(a)「存在しない」＝性質が偽＝反例が出る、(b)「資源内で見つからなかった」＝**打ち切り**。
打ち切りは下界の根拠にならない。

使い方:
  ic3_pyramid.py --selftest              # 符号化の校正（BFS と AIG シミュレータで照合）
  ic3_pyramid.py --h 8 --p 19 --aig out.aig
  ic3_pyramid.py --h 8 --p 19 --smv out.smv
"""
from __future__ import annotations

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from q2_cnf import pyramid, depths  # noqa: E402  （読むだけ・書き換えない）

# 実測の p_min（台帳 Q11、h=2..18）。scripts/q2_descent_cnf.py:PMIN と同じ表。
# ⚠ 検算条項によりこの表も鵜呑みにしない。--selftest が h<=6 を BFS で独立に出し直す。
PMIN = {2: 3, 3: 6, 4: 8, 5: 10, 6: 13, 7: 16, 8: 20, 9: 23, 10: 26, 11: 29,
        12: 32, 13: 37, 14: 41, 15: 45, 16: 49, 17: 54, 18: 58}


# ---------------------------------------------------------------- モデル定義
class Model:
    """窓・強制・規則。q2_cnf.build(window=True) と同じものを遷移系向けに持つ。"""

    def __init__(self, h: int, p: int, descent: bool = False):
        self.h, self.p, self.descent = h, p, descent
        self.par, self.sink = pyramid(h)
        self.n = len(self.par)
        self.dep = depths(self.par)
        D = self.dep[self.sink]
        assert D == h - 1
        if descent:
            # 降下（docs/42 §2・scripts/q2_descent_cnf.py と同じ条件）。
            # ⚠ この符号化の UNSAT は Lean の `pmin_iff_descent` と生成器の正しさに乗る。
            self.T = h - 1
            T = self.T
            self.lo = [self.dep[v] + 1 for v in range(self.n)]
            self.hi = [T] * self.n
            self.forced = [set() for _ in range(T + 1)]
            for v in range(self.n):
                if v == self.sink:
                    continue
                for t in (self.dep[v] + 1, self.dep[v] + 2):
                    if t <= T:
                        self.forced[t].add(v)
            return
        self.T = 2 * D + 1
        T = self.T
        self.lo = [min(self.dep[v] + 1, T) for v in range(self.n)]
        self.hi = [T if v == self.sink else max(T - self.dep[v] - 1, 0)
                   for v in range(self.n)]
        # 両端強制（q2_cnf の hup かつ T = 2D+1 の分岐と同一。ピラミッドは満たす）
        has_child = [False] * self.n
        for v in range(self.n):
            for u in self.par[v]:
                if self.dep[u] + 1 == self.dep[v]:
                    has_child[u] = True
        assert all(has_child[v] for v in range(self.n) if v != self.sink)
        self.forced: list[set[int]] = [set() for _ in range(T + 1)]
        for v in range(self.n):
            if v == self.sink:
                for t in range(self.lo[v], T + 1):
                    self.forced[t].add(v)
            else:
                for t in (self.lo[v], self.lo[v] + 1, self.hi[v] - 1, self.hi[v]):
                    if self.lo[v] <= t <= self.hi[v]:
                        self.forced[t].add(v)

    def live(self, v: int, t: int) -> bool:
        return self.lo[v] <= t <= self.hi[v]

    def state_ok(self, cfg: frozenset[int], t: int) -> bool:
        """時刻 t の配置として窓・強制・基数を満たすか。"""
        if len(cfg) > self.p:
            return False
        for v in cfg:
            if not self.live(v, t):
                return False
        return self.forced[t] <= cfg

    def legal(self, a: frozenset[int], b: frozenset[int]) -> bool:
        for v in a ^ b:
            for q in self.par[v]:
                if q not in a or q not in b:
                    return False
        return True


def bfs_reachable(m: Model) -> bool:
    """遷移系を素の Python で全探索し、bad（t=T に生きて到達）が可能かを返す。
    **AIG/SMV と独立の参照実装**（--selftest でのみ使う。小さい h 専用）。"""
    if not m.state_ok(frozenset(), 0):
        return False
    cur = {frozenset()}
    for t in range(m.T):
        nxt = set()
        cand = [v for v in range(m.n) if m.live(v, t + 1)]
        free = [v for v in cand if v not in m.forced[t + 1]]
        base = frozenset(m.forced[t + 1])
        room = m.p - len(base)
        if room < 0:
            return False
        for a in cur:
            for mask in range(1 << len(free)):
                if bin(mask).count("1") > room:
                    continue
                b = base | {free[i] for i in range(len(free)) if mask >> i & 1}
                b = frozenset(b)
                if m.legal(a, b):
                    nxt.add(b)
        cur = nxt
        if not cur:
            return False
    return True


# ---------------------------------------------------------------- AIG ビルダ
class Aig:
    """AND-Inverter Graph。リテラル 0=FALSE, 1=TRUE, 変数 i のリテラルは 2i。"""

    def __init__(self):
        self.ni = 0
        self.nl = 0
        self.ands: list[tuple[int, int, int]] = []
        self.inputs: list[int] = []
        self.latches: list[list[int]] = []   # [cur_lit, next_lit]
        self.outputs: list[int] = []
        self._hash: dict[tuple[int, int], int] = {}
        self._frozen_io = False

    # 変数割り当て: 入力 → ラッチ → AND の順（AIGER のバイナリ形式の要求）
    def inp(self) -> int:
        assert not self._frozen_io and not self.nl
        self.ni += 1
        lit = 2 * self.ni
        self.inputs.append(lit)
        return lit

    def latch(self) -> int:
        assert not self._frozen_io
        self.nl += 1
        lit = 2 * (self.ni + self.nl)
        self.latches.append([lit, 0])
        return lit

    def set_next(self, cur_lit: int, nxt_lit: int):
        self.latches[cur_lit // 2 - self.ni - 1][1] = nxt_lit

    def and_(self, a: int, b: int) -> int:
        self._frozen_io = True
        if a == 0 or b == 0:
            return 0
        if a == 1:
            return b
        if b == 1:
            return a
        if a == b:
            return a
        if a == (b ^ 1):
            return 0
        if a < b:
            a, b = b, a
        key = (a, b)
        if key in self._hash:
            return self._hash[key]
        lit = 2 * (self.ni + self.nl + len(self.ands) + 1)
        self.ands.append((lit, a, b))
        self._hash[key] = lit
        return lit

    def not_(self, a: int) -> int:
        return a ^ 1

    def or_(self, a: int, b: int) -> int:
        return self.and_(a ^ 1, b ^ 1) ^ 1

    def xor_(self, a: int, b: int) -> int:
        return self.or_(self.and_(a, b ^ 1), self.and_(a ^ 1, b))

    def big_and(self, xs) -> int:
        xs = list(xs)
        if not xs:
            return 1
        while len(xs) > 1:
            xs = [self.and_(xs[i], xs[i + 1]) if i + 1 < len(xs) else xs[i]
                  for i in range(0, len(xs), 2)]
        return xs[0]

    def big_or(self, xs) -> int:
        xs = list(xs)
        if not xs:
            return 0
        return self.big_and([x ^ 1 for x in xs]) ^ 1

    # --- 算術（LSB 先頭のビット列） ---
    def add(self, a: list[int], b: list[int]) -> list[int]:
        w = max(len(a), len(b))
        a = a + [0] * (w - len(a))
        b = b + [0] * (w - len(b))
        out, c = [], 0
        for i in range(w):
            s = self.xor_(self.xor_(a[i], b[i]), c)
            c = self.big_or([self.and_(a[i], b[i]), self.and_(a[i], c),
                             self.and_(b[i], c)])
            out.append(s)
        out.append(c)
        return out

    def popcount(self, bits: list[int]) -> list[int]:
        nums = [[b] for b in bits]
        if not nums:
            return [0]
        while len(nums) > 1:
            nxt = []
            for i in range(0, len(nums), 2):
                nxt.append(self.add(nums[i], nums[i + 1]) if i + 1 < len(nums)
                           else nums[i])
            nums = nxt
        return nums[0]

    def le_const(self, bits: list[int], k: int) -> int:
        """bits（LSB 先頭の非負整数）<= k。"""
        if k < 0:
            return 0
        w = len(bits)
        if w == 0:
            return 1
        if k >= (1 << w) - 1:
            return 1
        msb = bits[w - 1]
        rest = bits[:w - 1]
        half = 1 << (w - 1)
        if k >= half:
            return self.or_(msb ^ 1, self.le_const(rest, k - half))
        return self.and_(msb ^ 1, self.le_const(rest, k))

    def eq_const(self, bits: list[int], k: int) -> int:
        return self.big_and([b if (k >> i) & 1 else b ^ 1
                             for i, b in enumerate(bits)])

    # --- 出力 ---
    def write_aag(self) -> str:
        M = self.ni + self.nl + len(self.ands)
        out = [f"aag {M} {self.ni} {self.nl} {len(self.outputs)} {len(self.ands)}"]
        out += [str(x) for x in self.inputs]
        out += [f"{c} {n}" for c, n in self.latches]
        out += [str(x) for x in self.outputs]
        out += [f"{l} {a} {b}" for l, a, b in self.ands]
        return "\n".join(out) + "\n"

    def write_aig(self, path: str):
        """AIGER バイナリ（ABC の read_aiger 用）。"""
        M = self.ni + self.nl + len(self.ands)
        buf = bytearray()
        buf += f"aig {M} {self.ni} {self.nl} {len(self.outputs)} {len(self.ands)}\n".encode()
        for _, n in self.latches:
            buf += f"{n}\n".encode()
        for o in self.outputs:
            buf += f"{o}\n".encode()

        def enc(x: int):
            while x & ~0x7f:
                buf.append((x & 0x7f) | 0x80)
                x >>= 7
            buf.append(x)

        for lit, a, b in self.ands:
            hi, lo = (a, b) if a >= b else (b, a)
            assert lit > hi >= lo, (lit, hi, lo)
            enc(lit - hi)
            enc(hi - lo)
        with open(path, "wb") as f:
            f.write(bytes(buf))

    # --- シミュレータ（AIG が意図どおりかを --selftest で確かめる） ---
    def simulate(self, inp_vals: list[int], latch_vals: list[int]) -> list[int]:
        val = {0: 0, 1: 1}
        for lit, v in zip(self.inputs, inp_vals):
            val[lit] = v
            val[lit ^ 1] = 1 - v
        for (cur, _), v in zip(self.latches, latch_vals):
            val[cur] = v
            val[cur ^ 1] = 1 - v
        for lit, a, b in self.ands:
            v = val[a] & val[b]
            val[lit] = v
            val[lit ^ 1] = 1 - v
        return val


# ------------------------------------------------------------- AIG の組み立て
def build_aig(m: Model, mutate: str = "") -> tuple[Aig, dict]:
    """mutate: 変異注入用。"nolegal"/"nowin"/"nocard" は制約を落とし（弱める）、
    "tight" は基数を p-1 に締める（強める）。**検査の検出力を測るためだけに使う。**"""
    a = Aig()
    y = [a.inp() for _ in range(m.n)]                    # 次配置の候補（非決定）
    x = [a.latch() for _ in range(m.n)]                  # 現配置
    tw = max(1, (m.T).bit_length())                      # 時刻カウンタの幅
    tb = [a.latch() for _ in range(tw)]
    dead = a.latch()

    # legal(x, y)
    legal_terms = []
    for v in range(m.n):
        ch = a.xor_(x[v], y[v])
        for q in m.par[v]:
            legal_terms.append(a.or_(ch ^ 1, a.and_(x[q], y[q])))
    legal = a.big_and(legal_terms)

    # card(y): |y| <= p
    card = a.le_const(a.popcount(y), m.p)

    # win(y, t+1)
    eq = [a.eq_const(tb, j) for j in range(m.T + 1)]
    win_terms = []
    for v in range(m.n):
        allow = a.big_or([eq[j] for j in range(m.T)
                          if m.live(v, j + 1)])
        force = a.big_or([eq[j] for j in range(m.T)
                          if v in m.forced[j + 1]])
        win_terms.append(a.or_(y[v] ^ 1, allow))          # y_v -> 窓の中
        win_terms.append(a.or_(y[v], force ^ 1))          # 強制 -> y_v
    win = a.big_and(win_terms)

    if mutate == "nolegal":
        legal = 1
    elif mutate == "nowin":
        win = 1
    elif mutate == "nocard":
        card = 1
    elif mutate == "tight":
        card = a.le_const(a.popcount(y), m.p - 1)
    elif mutate:
        raise SystemExit(f"未知の変異: {mutate}")
    viol = a.big_and([legal, card, win]) ^ 1
    dead_n = a.or_(dead, viol)
    a.set_next(dead, dead_n)
    for v in range(m.n):
        a.set_next(x[v], a.and_(y[v], dead_n ^ 1))

    # t' = (t = T) ? T : t + 1
    at_T = eq[m.T]
    carry = at_T ^ 1
    for i in range(tw):
        s = a.xor_(tb[i], carry)
        carry = a.and_(tb[i], carry)
        a.set_next(tb[i], s)

    a.outputs.append(a.and_(at_T, dead ^ 1))              # bad
    return a, {"y": y, "x": x, "tb": tb, "dead": dead, "tw": tw}


# ------------------------------------------------------------------- SMV 出力
def build_smv(m: Model) -> str:
    L = [f"-- pyramid h={m.h}, p={m.p}, T={m.T}  (generated by scripts/ic3_pyramid.py)",
         "MODULE main", "VAR"]
    for v in range(m.n):
        L.append(f"  x{v} : boolean;")
    L.append(f"  t : 0..{m.T};")
    L.append("  dead : boolean;")
    L.append("IVAR")
    for v in range(m.n):
        L.append(f"  y{v} : boolean;")
    L.append("DEFINE")
    lt = []
    for v in range(m.n):
        for q in m.par[v]:
            lt.append(f"((x{v} xor y{v}) -> (x{q} & y{q}))")
    L.append("  legal := " + (" & ".join(lt) if lt else "TRUE") + ";")
    L.append(f"  card := count({', '.join('y%d' % v for v in range(m.n))}) <= {m.p};")
    wt = []
    for v in range(m.n):
        allow = [str(j) for j in range(m.T) if m.live(v, j + 1)]
        force = [str(j) for j in range(m.T) if v in m.forced[j + 1]]
        wt.append(f"(y{v} -> t in {{{', '.join(allow)}}})" if allow else f"(!y{v})")
        if force:
            wt.append(f"((t in {{{', '.join(force)}}}) -> y{v})")
    L.append("  win := " + (" & ".join(wt) if wt else "TRUE") + ";")
    L.append("  viol := !(legal & card & win);")
    L.append("INIT")
    L.append("  " + " & ".join([f"!x{v}" for v in range(m.n)])
             + " & t = 0 & !dead;")
    L.append("TRANS")
    tr = [f"(next(t) = case t = {m.T} : {m.T}; TRUE : t + 1; esac)",
          "(next(dead) <-> (dead | viol))"]
    for v in range(m.n):
        tr.append(f"(next(x{v}) <-> (y{v} & !(dead | viol)))")
    L.append("  " + " &\n  ".join(tr) + ";")
    L.append(f"INVARSPEC !(t = {m.T} & !dead);")
    return "\n".join(L) + "\n"


# ------------------------------------------------------------------ 校正試験
def aig_bfs_reachable(m: Model) -> bool:
    """**AIG そのもの**をシミュレートして bad の到達可能性を全探索する。
    build_aig が意図した遷移系になっているかの検査（小さい h 専用）。"""
    a, h = build_aig(m)
    n, tw = m.n, h["tw"]
    init = tuple([0] * n + [0] * tw + [0])
    seen = {init}
    frontier = [init]
    while frontier:
        nxt = []
        for st in frontier:
            for mask in range(1 << n):
                iv = [(mask >> i) & 1 for i in range(n)]
                val = a.simulate(iv, list(st))
                if val[a.outputs[0]]:
                    return True
                ns = tuple([val[nl] for _, nl in a.latches])
                if ns not in seen:
                    seen.add(ns)
                    nxt.append(ns)
        frontier = nxt
    return False


def selftest() -> int:
    bad = 0
    print("## 1. 遷移系の BFS（参照実装）が既知の p_min を再現するか")
    for h in (2, 3, 4, 5, 6):
        got = None
        for p in range(1, PMIN[h] + 2):
            if bfs_reachable(Model(h, p)):
                got = p
                break
        ok = got == PMIN[h]
        print(f"  h={h}: BFS の最小 p = {got}（表 {PMIN[h]}） {'○' if ok else '**✗**'}")
        bad += 0 if ok else 1
    print("## 2. AIG のシミュレーションが BFS と一致するか（AIG 出力の検査）")
    for h in (2, 3, 4):
        for p in range(1, PMIN[h] + 2):
            m = Model(h, p)
            r1, r2 = bfs_reachable(m), aig_bfs_reachable(m)
            if r1 != r2:
                print(f"  **✗ h={h} p={p}: BFS={r1} AIG={r2}**")
                bad += 1
        print(f"  h={h}: p=1..{PMIN[h]+1} で AIG と BFS が一致 ○")
    print("## 3. 降下への帰着（--descent）が 1 + d(h) = p_min を再現するか")
    for h in (2, 3, 4, 5, 6):
        got = None
        for d in range(0, PMIN[h] + 1):
            if bfs_reachable(Model(h, d, descent=True)):
                got = d
                break
        ok = got is not None and got + 1 == PMIN[h]
        print(f"  h={h}: 最小 d = {got}、1+d = {None if got is None else got+1}"
              f"（表 {PMIN[h]}） {'○' if ok else '**✗**'}")
        bad += 0 if ok else 1
    print("校正 OK" if bad == 0 else f"**校正 NG: {bad} 件**")
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--h", type=int)
    ap.add_argument("--p", type=int)
    ap.add_argument("--aig")
    ap.add_argument("--aag")
    ap.add_argument("--smv")
    ap.add_argument("--mutate", default="",
                    choices=["", "nolegal", "nowin", "nocard", "tight"],
                    help="変異注入（検査の検出力を測る）")
    ap.add_argument("--descent", action="store_true",
                    help="降下への帰着で符号化する（地平線 2h-1 → h-1。p_min = 1 + d）")
    a = ap.parse_args()
    if a.selftest:
        sys.exit(1 if selftest() else 0)
    if not (a.h and a.p):
        ap.print_help()
        sys.exit(2)
    m = Model(a.h, a.p, descent=a.descent)
    if a.aig or a.aag:
        g, _ = build_aig(m, mutate=a.mutate)
        if a.aig:
            g.write_aig(a.aig)
        if a.aag:
            open(a.aag, "w").write(g.write_aag())
        print(f"AIG: {g.ni} 入力 / {g.nl} ラッチ / {len(g.ands)} AND "
              f"（h={m.h} p={m.p} T={m.T} |V|={m.n}）")
    if a.smv:
        open(a.smv, "w").write(build_smv(m))
        print(f"SMV: {a.smv} （h={m.h} p={m.p} T={m.T} |V|={m.n}）")


if __name__ == "__main__":
    main()
