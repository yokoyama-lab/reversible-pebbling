#!/usr/bin/env python3
"""要石 δ=-1（s>=3, n>=θ(s)）の証明戦略を、Lean に入る前に数値で検定する。

    python3 check_keystone.py            # 既定 s<=14, n<=1000
    python3 check_keystone.py 8 120      # s<=8, n<=120（依頼文の 422 点の範囲）

## 終わったら何が言えるか（測る前に書いた 1 行）

範囲 s<=S・n<=N で、証明が使う補助不等式 3 本（L1: U の増分>=2、L2: n>=s で U の増分>=4、
L3: G(q+1,s)<=U(q,s)+5 (q<θ(s))）と、U の分解の「任意の」最適 k から δ=-1 を導く
場合分け（P）が、漸化式の値の上で 1 点も破れない——すなわち Lean 化に進む価値がある。
1 点でも破れたら、その補題を使う方針は捨てる。**これは証明ではない**（層: 計算による確認）。

## 値の出どころ

U=T_UP, G=T_UG。Lean で両方向が証明済みの 2 本の漸化式（Upper.lean `decomp_exact`、
Unghost.lean `decomp_ug_exact`、ともに s>=3, n>=2）と、s=2 の閉形式（Cap2 / Cap2Exact）、
n=1 の値（U=1, G=2）だけから反復 DP で計算する。closed2.py とは別実装で、小範囲で照合する。

## 検査（すべて「破れの件数」を数える）

T0  依頼文の数: 3<=s<=8, B4(s)<=n<=120 の点数が 422 で、全点 δ=-1 か
T1  3<=s<=S, θ(s)<=n<=N で G=U-1。1<=n<θ(s) で G=U+1（符号反転がちょうど θ）
L1  s>=2, m>=1 で U(m+1,s) >= U(m,s)+2
L2  s>=2, m>=s で U(m+1,s) >= U(m,s)+4
L3  s>=2, 1<=q<=θ(s)-1 で G(q+1,s) <= U(q,s)+5
P   s+1>=3, n>=θ(s+1)、U(n,s+1) の分解の最適 k を**すべて**列挙し、各 k で
      A: q=n-k>=θ(s) なら G(q,s)<=U(q,s)
      B: q<θ(s) なら k-1>=s+1 かつ 2(k-1)-1+U(k-1,s+1)+G(q+1,s) <= U(n,s+1)-1
    が成り立つか（Lean の証明は存在量化された k を 1 つ受け取るので、全最適 k で要る）

## 変異（検査に検出力があること。各変異は「破れが 1 件以上出る」ことを期待する）

M1  L2 の範囲を m>=s-1 に広げる
M2  T1 の範囲を n>=θ(s)-1 に広げる
M3  L3 の定数を 4 にする
M4  L1 の定数を 3 にする
M5  P の B でずらさない（k'=k, q'=q のまま G(q,s)<=U(q,s) を要求する）
M6  P の B の結論を U-2 に強める
"""
from __future__ import annotations

import sys


def theta(s: int) -> int:
    return s * (s + 1) // 2


def B4(s: int) -> int:
    b = 4
    for t in range(3, s + 1):
        b = b + theta(t) - 1
    return b


def tables(S: int, N: int):
    """U[s][n], G[s][n]（2<=s<=S, 1<=n<=N）と、U の分解の最適 k の全列挙 K[s][n]。"""
    U = {2: [None] * (N + 2)}
    G = {2: [None] * (N + 2)}
    K: dict[int, list] = {}
    for n in range(1, N + 2):
        U[2][n] = 1 if n == 1 else n * n + n - 3
        G[2][n] = 2 * n if n <= 2 else n * n + n - 4
    for s in range(3, S + 1):
        u = [None] * (N + 2)
        g = [None] * (N + 2)
        ks = [None] * (N + 2)
        u[1], g[1] = 1, 2
        up, gp = U[s - 1], G[s - 1]
        for n in range(2, N + 2):
            best, arg = None, []
            bestg = None
            for k in range(1, n):
                head = 2 * k - 1 + u[k]
                v = head + up[n - k]
                if best is None or v < best:
                    best, arg = v, [k]
                elif v == best:
                    arg.append(k)
                w = head + gp[n - k]
                if bestg is None or w < bestg:
                    bestg = w
            u[n], g[n], ks[n] = best, bestg, arg
        U[s], G[s], K[s] = u, g, ks
    return U, G, K


def run(S: int, N: int) -> int:
    U, G, K = tables(S, N)
    rc = 0

    def report(name, checked, bad, expect_bad=False):
        nonlocal rc
        ok = (len(bad) > 0) if expect_bad else (len(bad) == 0)
        tag = "OK " if ok else "NG "
        kind = "変異（破れを期待）" if expect_bad else "検査"
        print(f"{tag}{name:<4} {kind}: {checked} 点, 破れ {len(bad)}"
              + (f"  例 {bad[:3]}" if bad else ""))
        if not ok:
            rc = 1

    # --- T0: 依頼文の 422 点
    if S >= 8 and N >= 120:
        pts = [(s, n) for s in range(3, 9) for n in range(B4(s), 121)]
        bad = [(s, n) for s, n in pts if G[s][n] != U[s][n] - 1]
        print(f"    T0   依頼文の範囲 3<=s<=8, B4(s)<=n<=120 の点数 = {len(pts)}（依頼文は 422）")
        if len(pts) != 422:
            print("NG  T0   点数が依頼文と食い違う")
            rc = 1
        report("T0", len(pts), bad)

    # --- T1
    c, bad = 0, []
    for s in range(3, S + 1):
        for n in range(1, N + 1):
            c += 1
            want = -1 if n >= theta(s) else +1
            if G[s][n] - U[s][n] != want:
                bad.append((s, n, G[s][n] - U[s][n]))
    report("T1", c, bad)
    cneg = sum(1 for s in range(3, S + 1) for n in range(theta(s), N + 1))
    cB4 = sum(1 for s in range(3, S + 1) for n in range(B4(s), N + 1))
    print(f"         うち n>=θ(s): {cneg} 点、n>=B4(s): {cB4} 点")

    # --- L1, L2, L3
    def L1(const=2):
        c, bad = 0, []
        for s in range(2, S + 1):
            for m in range(1, N + 1):
                c += 1
                if U[s][m + 1] < U[s][m] + const:
                    bad.append((s, m))
        return c, bad

    def L2(lo=0):
        c, bad = 0, []
        for s in range(2, S + 1):
            for m in range(max(1, s + lo), N + 1):
                c += 1
                if U[s][m + 1] < U[s][m] + 4:
                    bad.append((s, m))
        return c, bad

    def L3(const=5):
        c, bad = 0, []
        for s in range(2, S + 1):
            for q in range(1, min(theta(s) - 1, N) + 1):
                c += 1
                if G[s][q + 1] > U[s][q] + const:
                    bad.append((s, q))
        return c, bad

    report("L1", *L1())
    report("L2", *L2())
    report("L3", *L3())

    # --- P
    def P(shift=True, gain=1):
        c, bad, nA, nB = 0, [], 0, 0
        for s1 in range(3, S + 1):
            s = s1 - 1
            for n in range(theta(s1), N + 1):
                for k in K[s1][n]:
                    c += 1
                    q = n - k
                    if q >= theta(s):
                        nA += 1
                        if not G[s][q] <= U[s][q]:
                            bad.append((s1, n, k, "A"))
                    else:
                        nB += 1
                        if shift:
                            good = (k - 1 >= s + 1 and
                                    2 * (k - 1) - 1 + U[s1][k - 1] + G[s][q + 1]
                                    <= U[s1][n] - gain)
                        else:
                            good = G[s][q] <= U[s][q]
                        if not good:
                            bad.append((s1, n, k, "B"))
        return c, bad, nA, nB

    c, bad, nA, nB = P()
    report("P", c, bad)
    print(f"         最適 k の内訳: 場合A {nA}、場合B {nB}（B が 0 なら場合分けは空虚）")

    # --- 変異
    report("M1", *L2(lo=-1), expect_bad=True)
    c, bad = 0, []
    for s in range(3, S + 1):
        for n in range(theta(s) - 1, N + 1):
            c += 1
            if G[s][n] != U[s][n] - 1:
                bad.append((s, n))
    report("M2", c, bad, expect_bad=True)
    report("M3", *L3(const=4), expect_bad=True)
    report("M4", *L1(const=3), expect_bad=True)
    c, bad, _, _ = P(shift=False)
    report("M5", c, bad, expect_bad=True)
    c, bad, _, _ = P(gain=2)
    report("M6", c, bad, expect_bad=True)

    # --- 別実装 closed2.py との照合（小範囲）
    try:
        sys.path.insert(0, "..")
        sys.setrecursionlimit(100000)
        import closed2
        c, bad = 0, []
        for s in range(2, min(S, 8) + 1):
            for n in range(1, min(N, 60) + 1):
                c += 2
                if closed2.T_UP(n, s) != U[s][n]:
                    bad.append(("UP", n, s))
                if closed2.T_UG(n, s) != G[s][n]:
                    bad.append(("UG", n, s))
        report("X", c, bad)
    except Exception as e:  # 照合できなかったことを合格にしない
        print(f"NG  X    closed2.py との照合が走らなかった: {e!r}")
        rc = 1

    print(f"\n範囲: 2<=s<={S}, 1<=n<={N}。" + ("全検査が期待どおり" if rc == 0 else "⚠ 期待と違う検査がある"))
    return rc


if __name__ == "__main__":
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    raise SystemExit(run(S, N))
