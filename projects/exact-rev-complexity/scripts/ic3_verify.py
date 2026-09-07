#!/usr/bin/env python3
"""ABC の `pdr` が吐いた帰納的不変量を **ABC の外で** 検査する（2026-09-06）。

## なぜ要るか

`Verification of invariant ... was successful` は **ABC 自身**の検査である。
「IC3 が人の設計なしに正しい不変量を構成した」を主張するなら、その主張の荷重は
不変量そのものが負うので、**独立の検査器**（cadical + drat-trim）に通す必要がある。
⚠ 下界の数値 $p_{\\min}(P_{13}) \\ge 37$ のためには不要
（`data/q2_pyr_cert_log.csv` の素の CNF の DRAT が既に支えている）。

## 検査する 3 本

不変量 $I = \\lnot\\bigvee_C C$（`pdr -d -I` の PLA。各行が塞いだ cube）。
遷移系は `ic3_pyramid.build_aig` が作る AIG そのもの（Tseitin で CNF にする）。

| # | 主張 | UNSAT にする CNF |
|---|---|---|
| 1 | $\\mathrm{Init} \\to I$ | 全ラッチ 0 ∧ $\\lnot I$ |
| 2 | $I \\wedge T \\to I'$ | $I(x)$ ∧ 遷移関係 ∧ $\\lnot I(x')$ |
| 3 | $I \\to \\lnot\\mathrm{bad}$ | $I(x)$ ∧ 遷移関係 ∧ bad 出力 = 1 |

3 本とも `s UNSATISFIABLE` かつ drat-trim が `s VERIFIED` なら、
**$I$ は帰納的不変量であり bad は到達不能**が外部検証された。

## 陰性対照（変異注入。⚠ エラーが出ないことは道具が働いた証拠にならない）

| 変異 | 何をするか | 落ちるべき検査 |
|---|---|---|
| `initblock` | 初期状態（全 0）を覆う cube を足す | **1** |
| `dropall` | cube を全部消す（$I = \\top$） | **3** |
| `dropbad` | bad を覆う cube だけ消す | **3** |
| `blockreach` | 時刻 1 の**到達可能な**状態（層 0 が全部・他は不在）を覆う cube を足す | **2** |

使い方:
  ic3_verify.py --h 13 --p 36 --inv notes/ic3/invariants/pyr_h13_p36.inv.gz
  ic3_verify.py --h 8 --p 19 --inv <...> --mutate blockreach
"""
from __future__ import annotations

import argparse
import gzip
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ic3_pyramid import Model, build_aig  # noqa: E402

SCRATCH = os.environ.get(
    "IC3_SCRATCH",
    "/work/tmp/claude-1000/-work-a-dev-github-com-tetsuo-jp-exact-rev-complexity-"
    "notes-ic3/475e0dbf-41a6-49b8-baeb-071ae7ceb4c1/scratchpad/ic3v")


def read_pla(path: str):
    op = gzip.open if path.endswith(".gz") else open
    names, cubes = [], []
    with op(path, "rt") as f:
        for ln in f:
            ln = ln.strip()
            if ln.startswith(".ilb"):
                names = ln.split()[1:]
            elif ln.startswith(".") or ln.startswith("#") or not ln:
                continue
            else:
                cubes.append(ln.split()[0])
    return names, cubes


class Cnf:
    def __init__(self, nvar: int):
        self.n = nvar
        self.cls: list[list[int]] = []

    def new(self) -> int:
        self.n += 1
        return self.n

    def add(self, c):
        self.cls.append(list(c))

    def dump(self, path: str):
        with open(path, "w") as f:
            f.write(f"p cnf {self.n} {len(self.cls)}\n")
            f.write("".join(" ".join(map(str, c)) + " 0\n" for c in self.cls))


def build_checks(m: Model, names, cubes, split: int = 1):
    """3 本の CNF を作る。戻り値は {名前: Cnf}。

    `split > 1` のとき検査 2 を分割する: ¬I(x') は「どれかの cube に入る」なので、
    cube を split 個の束に分け、束ごとに「その束のどれかに入る」を問う。
    **全部の束が UNSAT ⟺ 帰納的**（分割は健全）。単一クエリだと DRAT が 9 分で 7GB に
    膨らんで検証不能だったので分ける。"""
    a, _ = build_aig(m)
    nv = a.ni + a.nl + len(a.ands)
    latch_cur = [a.ni + j + 1 for j in range(a.nl)]        # ラッチ j の現在値の変数
    latch_nxt = [a.latches[j][1] for j in range(a.nl)]     # 次状態の AIG リテラル
    sup = [int(nm[2:]) for nm in names]                    # support のラッチ番号

    def tseitin(c: Cnf):
        """AIG の AND ゲートを CNF にし、定数用の変数を返す。"""
        false_var = c.new()
        c.add([-false_var])
        def lit(L: int) -> int:
            if L == 0:
                return false_var
            if L == 1:
                return -false_var
            v, s = L // 2, L & 1
            return -v if s else v
        for g, x, y in a.ands:
            gg, xx, yy = lit(g), lit(x), lit(y)
            c.add([-gg, xx]); c.add([-gg, yy]); c.add([gg, -xx, -yy])
        return lit

    def inv_clauses(c: Cnf, litof):
        """I(x) を節として積む（cube の否定）。"""
        for pat in cubes:
            c.add([(-litof(j) if ch == "1" else litof(j))
                   for j, ch in zip(sup, pat) if ch != "-"])

    def not_inv(c: Cnf, litof, subset=None):
        """¬I(x) をセレクタで積む（subset のどれかの cube に入る）。"""
        sel = []
        for pat in (cubes if subset is None else subset):
            s = c.new()
            sel.append(s)
            for j, ch in zip(sup, pat):
                if ch == "-":
                    continue
                c.add([-s, litof(j) if ch == "1" else -litof(j)])
        c.add(sel)

    out = {}

    # --- 1. Init -> I  （全ラッチ 0 ∧ ¬I が UNSAT） ---
    c1 = Cnf(a.ni + a.nl)
    for v in latch_cur:
        c1.add([-v])
    not_inv(c1, lambda j: latch_cur[j])
    out["1_init"] = c1

    # --- 2. I ∧ T -> I'  （I(x) ∧ 遷移 ∧ ¬I(x') が UNSAT） ---
    for b in range(split):
        sub = cubes[b::split] if split > 1 else None
        if sub is not None and not sub:
            continue
        c2 = Cnf(nv)
        lit2 = tseitin(c2)
        inv_clauses(c2, lambda j: latch_cur[j])
        not_inv(c2, lambda j: lit2(latch_nxt[j]), sub)
        out["2_induct" if split == 1 else f"2_induct_{b:03d}"] = c2

    # --- 3. I -> ¬bad  （I(x) ∧ bad(x)=1 が UNSAT） ---
    c3 = Cnf(nv)
    lit3 = tseitin(c3)
    inv_clauses(c3, lambda j: latch_cur[j])
    c3.add([lit3(a.outputs[0])])
    out["3_safe"] = c3
    return out


def mutate(m: Model, names, cubes, kind: str):
    """陰性対照。cube 集合を壊す。"""
    sup = [int(nm[2:]) for nm in names]
    tw = max(1, (m.T).bit_length())

    def cube_of(state: dict[int, int]) -> str:
        return "".join(str(state[j]) for j in sup)

    if kind == "dropall":
        return []
    if kind == "initblock":
        return cubes + [cube_of({j: 0 for j in sup})]
    if kind == "dropbad":
        bad = {j: 0 for j in sup}
        for i in range(tw):
            if m.n + i in bad:
                bad[m.n + i] = (m.T >> i) & 1
        keep = [p for p in cubes
                if not all(ch == "-" or bad[j] == int(ch) for j, ch in zip(sup, p))]
        assert len(keep) < len(cubes), "bad を覆う cube が無い（不変量が壊れている）"
        return keep
    if kind == "blockreach":
        # 時刻 1 の到達可能な状態: 層 0（深さ 0）の頂点だけが在る・dead=0
        st = {}
        for j in sup:
            if j < m.n:
                st[j] = 1 if m.dep[j] == 0 else 0
            elif j < m.n + tw:
                st[j] = (1 >> (j - m.n)) & 1
            else:
                st[j] = 0
        return cubes + [cube_of(st)]
    raise SystemExit(f"未知の変異: {kind}")


def run_one(name: str, c: Cnf, tag: str, timeout: int, mem: int, drat: bool):
    os.makedirs(SCRATCH, exist_ok=True)
    cnf = f"{SCRATCH}/{tag}_{name}.cnf"
    dr = f"{SCRATCH}/{tag}_{name}.drat"
    for f in (cnf, dr):
        if os.path.exists(f):
            os.remove(f)          # ⚠ 追記されると前回の s 行が残る
    c.dump(cnf)
    t0 = time.time()
    cmd = ["runcap", "-m", str(mem), "-t", str(timeout), "-n", f"v-{tag}-{name}", "--",
           "cadical", cnf] + ([dr, "--binary=false"] if drat else ["-q"])
    r = subprocess.run(cmd, capture_output=True, text=True)
    sat = "s UNSATISFIABLE" if "s UNSATISFIABLE" in r.stdout else (
          "s SATISFIABLE" if "s SATISFIABLE" in r.stdout else "打ち切り/エラー")
    el = time.time() - t0
    ver, drsz = "—", "—"
    if drat and sat == "s UNSATISFIABLE" and os.path.exists(dr):
        drsz = f"{os.path.getsize(dr)/1e6:.1f}MB"
        v = subprocess.run(["runcap", "-m", str(mem), "-t", str(timeout), "-n",
                            f"t-{tag}-{name}", "--", "drat-trim", cnf, dr],
                           capture_output=True, text=True)
        ver = ("s VERIFIED" if "s VERIFIED" in v.stdout else
               "s NOT VERIFIED" if "NOT VERIFIED" in v.stdout else "打ち切り/エラー")
        os.remove(dr)
    print(f"  {name:10s} 変数 {c.n:>8} / 節 {len(c.cls):>9} : {sat:16s} "
          f"{el:7.1f}s  DRAT {drsz:>8}  {ver}", flush=True)
    os.remove(cnf)
    return sat, ver


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--inv", required=True)
    ap.add_argument("--mutate", default="",
                    choices=["", "initblock", "dropall", "dropbad", "blockreach"])
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--mem", type=int, default=12)
    ap.add_argument("--no-drat", action="store_true")
    ap.add_argument("--only", default="", help="1_init / 2_induct / 3_safe（前方一致）")
    ap.add_argument("--split", type=int, default=1,
                    help="検査 2 を N 個の束に分ける（DRAT を小さく保つため）")
    a = ap.parse_args()
    m = Model(a.h, a.p)
    names, cubes = read_pla(a.inv)
    tag = f"h{a.h}p{a.p}" + (f"_{a.mutate}" if a.mutate else "")
    if a.mutate:
        cubes = mutate(m, names, cubes, a.mutate)
    print(f"h={a.h} p={a.p} cube {len(cubes)} 本 / support {len(names)} latch"
          + (f"  【変異: {a.mutate}】" if a.mutate else ""))
    checks = build_checks(m, names, cubes, split=a.split)
    res = {}
    for k, c in checks.items():
        if a.only and not k.startswith(a.only):
            continue
        res[k] = run_one(k, c, tag, a.timeout, a.mem, not a.no_drat)
    # ⚠ 2026-09-06 修正: 以前はここで「**3 本とも UNSAT**」と固定文言を出していた。
    # --only で 1 本しか走らせなくても同じ行が出るので、**総括行が合否の証拠にならなかった**。
    # 実際に ren-fe が h=15 p=42 の検査でこれを根拠に「全部通った」と書きかけている。
    # 走った本数と全体の本数を必ず併記し、一部しか走っていないなら明示する。
    total = len(checks)
    ran = len(res)
    ok = bool(res) and all(v[0] == "s UNSATISFIABLE" for v in res.values())
    if not res:
        print("**検査が 1 本も走っていない**（--only が何にも一致していない可能性）")
        return 1
    head = f"**{ran}/{total} 本が UNSAT**" if ok else f"**UNSAT でない検査がある（走 {ran}/{total} 本）**"
    if ran < total:
        head += f" ⚠ --only で絞ったため {total - ran} 本は走っていない。合否は個別行で読むこと"
    print(head + ("（変異注入なので落ちるのが正しい）" if a.mutate else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
