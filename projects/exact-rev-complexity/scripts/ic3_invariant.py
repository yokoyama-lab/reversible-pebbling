#!/usr/bin/env python3
"""ABC の `pdr -d -I <file>` が吐いた帰納的不変量（PLA 形式）を読み、
**それが個数抽象では表現できない**ことを SAT で決定的に示す。

## なぜこれを見るか

docs/35 の負の結果は「各層の**個数**だけを状態に持つ抽象では下界が上がらない」であり、
Lean の `runs_not_determined_by_card` が「個数から run 数は復元できない」を機械証明している。
IC3 が自動構成した不変量が個数の関数でないなら、**機械は人が使わなかった位置情報を
使っている**ことになる。

## 判定（決定的・乱数なし）

ABC の PLA は塞いだ cube の並びで、不変量は $I = \\lnot(\\bigvee \\mathrm{cube})$
（初期状態が cube に覆われず、bad が覆われることを検査して確認する）。

個数抽象が表せる述語は「各層の在個数・時刻・dead」の関数なので、**層内の置換で不変**である。
そこで層 $l$ 内の互換 $\\sigma$ について

$$\\exists s.\\ \\lnot I(s) \\land I(\\sigma s) \\land \\mathrm{plausible}(s)$$

を cadical に問う。ここで plausible は `dead = 0`・$t \\le T$・時間窓・両端強制・
基数 $|s| \\le p$（`q2_cnf.build(window=True)` と同じもの）。
**窓・強制・生存は層だけで決まるので $\\sigma s$ も自動的に plausible** になる。
つまり $s$ と $\\sigma s$ は個数抽象からは**区別できない**のに $I$ は区別する。
SAT ⇒ **$I$ は個数抽象では表現できない**。UNSAT ⇒ その $\\sigma$ については対称。

使い方:
  ic3_invariant.py --inv <file.inv> --h 8 --p 19
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from ic3_pyramid import Model  # noqa: E402


def parse_pla(path: str):
    names, cubes = [], []
    for ln in open(path):
        ln = ln.strip()
        if ln.startswith(".ilb"):
            names = ln.split()[1:]
        elif ln.startswith(".") or ln.startswith("#") or not ln:
            continue
        else:
            cubes.append(ln.split()[0])
    return names, cubes


def covered(names, cubes, asg: dict[str, int]) -> int:
    return sum(1 for pat in cubes
               if all(ch == "-" or asg[nm] == int(ch)
                      for nm, ch in zip(names, pat)))


def sinz_atmost(lits: list[int], k: int, nxt: int):
    """Sinz (2005) 逐次カウンタ。(clauses, 次の未使用変数番号) を返す。"""
    n = len(lits)
    cls = []
    if k >= n:
        return cls, nxt
    if k == 0:
        return [[-x] for x in lits], nxt
    s = []
    for _ in range(n):
        row = []
        for _ in range(k):
            nxt += 1
            row.append(nxt)
        s.append(row)
    cls.append([-lits[0], s[0][0]])
    for j in range(1, k):
        cls.append([-s[0][j]])
    for i in range(1, n):
        cls.append([-lits[i], s[i][0]])
        cls.append([-s[i - 1][0], s[i][0]])
        for j in range(1, k):
            cls.append([-lits[i], -s[i - 1][j - 1], s[i][j]])
            cls.append([-s[i - 1][j], s[i][j]])
        cls.append([-lits[i], -s[i - 1][k - 1]])
    return cls, nxt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inv", required=True)
    ap.add_argument("--h", type=int, required=True)
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--max-swaps", type=int, default=0,
                    help="調べる互換の本数の上限（0 = 全部）")
    a = ap.parse_args()
    m = Model(a.h, a.p)
    names, cubes = parse_pla(a.inv)
    tw = max(1, (m.T).bit_length())
    nvar0 = m.n + tw + 1                     # x_v, 時刻ビット, dead（latch 番号 +1）

    def lat(nm: str) -> int:
        return int(nm[2:])

    def kind(i: int):
        if i < m.n:
            return ("x", i)
        if i < m.n + tw:
            return ("t", i - m.n)
        return ("dead", 0)

    base, vid = {}, 0
    layer = {}
    for lvl in range(m.h):
        base[lvl] = vid
        for k in range(m.h - lvl):
            layer[vid] = lvl
            vid += 1

    sup = [lat(nm) for nm in names]
    peb = [i for i in sup if i < m.n]
    print(f"h={a.h} p={a.p}: cube {len(cubes)} 本 / support {len(names)} latch "
          f"（ペブル {len(peb)}・時刻 {sum(1 for i in sup if m.n <= i < m.n+tw)}"
          f"・dead {sum(1 for i in sup if i >= m.n+tw)}）")
    print(f"  support のペブル頂点が属する層: {sorted({layer[i] for i in peb})}")

    # PLA の極性の検査（不変量 = ¬⋁cube であること）
    z = {nm: 0 for nm in names}
    b = dict(z)
    for nm in names:
        k, i = kind(lat(nm))
        if k == "t":
            b[nm] = (m.T >> i) & 1
    print(f"  極性検査: 初期状態(全0) を覆う cube = {covered(names, cubes, z)} 本（0 が正）"
          f"／bad(t=T,dead=0) を覆う cube = {covered(names, cubes, b)} 本（1 以上が正）")

    # --- plausible(s) の節（全頂点にわたる。support 外の頂点も変数を持つ） ---
    cls: list[list[int]] = []
    V = lambda i: i + 1                                    # noqa: E731
    tb = [V(m.n + i) for i in range(tw)]
    dv = V(m.n + tw)
    cls.append([-dv])                                      # dead = 0
    for j in range(m.T + 1, 1 << tw):                      # t <= T
        cls.append([-tb[i] if (j >> i) & 1 else tb[i] for i in range(tw)])

    def t_ne(j):                                           # 「t != j」の節リテラル
        return [-tb[i] if (j >> i) & 1 else tb[i] for i in range(tw)]

    for v in range(m.n):
        for j in range(m.T + 1):
            if not m.live(v, j):
                cls.append(t_ne(j) + [-V(v)])              # 窓の外なら不在
            elif v in m.forced[j]:
                cls.append(t_ne(j) + [V(v)])               # 強制なら在
    nxt = nvar0
    ccls, nxt = sinz_atmost([V(v) for v in range(m.n)], a.p, nxt)
    cls += ccls
    base_cls = cls
    base_nxt = nxt

    lits = [[(V(lat(nm))) if ch == "1" else -(V(lat(nm)))
             for nm, ch in zip(names, pat) if ch != "-"] for pat in cubes]

    def ask(bx: int, by: int):
        """層内の互換 (bx,by) で ¬I(s) ∧ I(σs) ∧ plausible(s) を解く。"""
        cl = [c[:] for c in base_cls]
        nx = base_nxt
        sel = []
        for lt in lits:                       # ¬I(s): どれかの cube に入る
            nx += 1
            sel.append(nx)
            for x in lt:
                cl.append([-nx, x])
        cl.append(sel[:])
        sw = {bx: by, by: bx}
        for pat in cubes:                     # I(σs): どの cube にも入らない
            c2 = []
            for nm, ch in zip(names, pat):
                if ch == "-":
                    continue
                i = lat(nm)
                src = sw.get(i, i)
                c2.append(-(V(src)) if ch == "1" else V(src))
            if not c2:
                return None
            cl.append(c2)
        fd, path = tempfile.mkstemp(suffix=".cnf")
        with os.fdopen(fd, "w") as f:
            f.write(f"p cnf {nx} {len(cl)}\n")
            for c in cl:
                f.write(" ".join(map(str, c)) + " 0\n")
        r = subprocess.run(["cadical", "-q", path], capture_output=True, text=True)
        os.unlink(path)
        if "s SATISFIABLE" not in r.stdout:
            return None
        val = [0] * (m.n + tw + 1)
        for tok in r.stdout.split():
            try:
                x = int(tok)
            except ValueError:
                continue
            if 0 < abs(x) <= m.n + tw + 1:
                val[abs(x) - 1] = 1 if x > 0 else 0
        return val

    swaps = []
    for lvl in range(m.h):
        vs = [v for v in range(m.n) if layer[v] == lvl and v in peb]
        for i in range(len(vs)):
            for j in range(i + 1, len(vs)):
                swaps.append((lvl, vs[i], vs[j]))
    if a.max_swaps:
        swaps = swaps[:a.max_swaps]
    nsat = 0
    found = None
    for lvl, bx, by in swaps:
        w = ask(bx, by)
        if w is not None:
            nsat += 1
            if found is None:
                found = (lvl, bx, by, w)
    print(f"  層内の互換 {len(swaps)} 本のうち、不変量が非対称なもの: {nsat} 本"
          f"（SAT = 個数抽象では表現できない）")
    if not found:
        print("  → 検査した互換すべてで対称。個数抽象と矛盾しない不変量である。")
        return 1

    lvl, bx, by, w = found

    def dec(S):
        tv = sum(S[m.n + i] << i for i in range(tw))
        per: dict[int, list[int]] = {}
        for v in range(m.n):
            if S[v]:
                per.setdefault(layer[v], []).append(v - base[layer[v]])
        return (f"t={tv} dead={S[m.n+tw]} |s|={sum(S[:m.n])} "
                f"在頂点(層:添字)={dict(sorted(per.items()))}")
    w2 = list(w)
    w2[bx], w2[by] = w2[by], w2[bx]
    print("  **この不変量は個数抽象では表現できない**"
          "（層内で 2 頂点を入れ替えると値が変わる）:")
    print(f"    入れ替え: 層 {lvl} の添字 {bx - base[lvl]} と {by - base[lvl]}")
    print(f"    s （不変量が排除）: {dec(w)}")
    print(f"    σs（不変量が許す）: {dec(w2)}")
    print("    ※ 窓・両端強制・基数はすべて層だけで決まるので σs も同じく plausible。"
          "各層の在個数も同一。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
