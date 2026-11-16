#!/usr/bin/env python3
"""上包絡 T_UP(n,s) = max_m (2mn - β_m(s)) の「区間ごとの構成」を、Lean に入る前に数値で検定する。

    python3 check_envelope.py            # 既定 s<=14, n<=1000
    python3 check_envelope.py 6 120

## 終わったら何が言えるか（測る前に書いた 1 行）

折れ目 E(m,s) を E(1,s)=s、E(m,2)=m (m>=2)、E(m,s)=E(m-1,s)+E(m,s-1) と置いたとき、
傾き 2m の区間 [L(m,s), E(m,s)]（L(1,s)=1、L(m,s)=E(m-1,s)）が「頭の区間＋尻尾の区間」に
ちょうど一致し、区間上で U(n,s)=2mn-β_m(s) が漸化式の値で 1 点も破れない——すなわち
`decomp_le` と既存の下界（定理E'）だけで上包絡を Lean 化できる見込みが立つ。
1 点でも破れたら区間の取り方が違う。**これは証明ではない**（層: 計算による確認）。

## 検査（破れの件数を数える）

E0  E(2,s)=θ(s)-1、E(3,s)=B4(s)-1（既知の折れ目と一致）
E1  2·E(m,s) = β_{m+1}(s) - β_m(s)
E2  各 (n,s) で n<=E(m,s) となる最小の m を取ると L(m,s)<=n かつ U(n,s)=2mn-β_m(s)
E3  すべての m で 2mn-β_m(s) <= U(n,s)（下界。上と合わせて U は上包絡）
E4  証明の段: m>=2, s>=3, n∈[L(m,s),E(m,s)] で k=max(L(m-1,s), n-E(m,s-1)) と置くと
    k∈[L(m-1,s),E(m-1,s)]、q=n-k∈[L(m,s-1),E(m,s-1)]、1<=k<n、かつ
    2k-1 + (2(m-1)k-β_{m-1}(s)) + (2mq-β_m(s-1)) = 2mn-β_m(s)

## 変異（破れが 1 件以上出ることを期待する）

N1  区間の右端を E(m,s)+1 に広げる
N2  区間の左端を L(m,s)-1 に広げる
N3  折れ目の底を E(m,2)=m+1 にする
N4  E4 の k を 1 つずらす（k+1）
"""
from __future__ import annotations

import sys

from check_keystone import B4, tables, theta


def beta_table(M: int, S: int):
    b = {(1, s): 1 for s in range(2, S + 1)}
    for m in range(2, M + 1):
        b[(m, 2)] = m * m - m + 3
    for m in range(2, M + 1):
        for s in range(3, S + 1):
            b[(m, s)] = b[(m - 1, s)] + b[(m, s - 1)] + 1
    return b


def E_table(M: int, S: int, base_shift: int = 0):
    e = {(1, s): s for s in range(2, S + 1)}
    for m in range(2, M + 1):
        e[(m, 2)] = m + base_shift
    for m in range(2, M + 1):
        for s in range(3, S + 1):
            e[(m, s)] = e[(m - 1, s)] + e[(m, s - 1)]
    return e


def run(S: int, N: int) -> int:
    U, _, _ = tables(S, N)
    M = N + 2  # s=2 では E(m,2)=m なので m は n まで要る
    beta = beta_table(M + 8, S)  # E3 が m0+5 まで見るので余裕を持たせる
    E = E_table(M, S)
    rc = 0

    def L(m, s, e=E):
        return 1 if m == 1 else e[(m - 1, s)]

    def report(name, checked, bad, expect_bad=False):
        nonlocal rc
        ok = (len(bad) > 0) if expect_bad else (len(bad) == 0)
        kind = "変異（破れを期待）" if expect_bad else "検査"
        print(f"{'OK ' if ok else 'NG '}{name:<4} {kind}: {checked} 点, 破れ {len(bad)}"
              + (f"  例 {bad[:3]}" if bad else ""))
        if not ok:
            rc = 1

    # E0
    bad = [s for s in range(2, S + 1)
           if E[(2, s)] != theta(s) - 1 or E[(3, s)] != B4(s) - 1]
    report("E0", S - 1, bad)

    # E1
    c, bad = 0, []
    for s in range(2, S + 1):
        for m in range(1, M):
            c += 1
            if 2 * E[(m, s)] != beta[(m + 1, s)] - beta[(m, s)]:
                bad.append((m, s))
    report("E1", c, bad)

    def slope_of(n, s, e=E):
        m = 1
        while e[(m, s)] < n:
            m += 1
        return m

    # E2（と変異 N1, N2, N3）
    def E2(dl=0, dr=0, e=E):
        c, bad, mmax = 0, [], 0
        for s in range(2, S + 1):
            for m in range(1, M):
                lo, hi = L(m, s, e) - dl, e[(m, s)] + dr
                if lo > N:
                    break
                for n in range(max(1, lo), min(hi, N) + 1):
                    c += 1
                    mmax = max(mmax, m)
                    if U[s][n] != 2 * m * n - beta[(m, s)]:
                        bad.append((m, s, n))
        return c, bad, mmax

    c, bad, mmax = E2()
    report("E2", c, bad)
    # 被覆: どの (n,s) も最小の m の区間に入るか
    cov_bad = [(s, n) for s in range(2, S + 1) for n in range(1, N + 1)
               if not L(slope_of(n, s), s) <= n]
    report("E2c", (S - 1) * N, cov_bad)
    print(f"         現れた傾きの最大 2m = {2 * mmax}")

    # E3
    c, bad = 0, []
    for s in range(2, S + 1):
        for n in range(1, N + 1):
            m0 = slope_of(n, s)
            for m in range(1, m0 + 6):
                c += 1
                if 2 * m * n - beta[(m, s)] > U[s][n]:
                    bad.append((m, s, n))
    report("E3", c, bad)

    # E4（と変異 N4）
    def E4(shift=0):
        c, bad = 0, []
        for s in range(3, S + 1):
            for m in range(2, M):
                if L(m, s) > N:
                    break
                for n in range(L(m, s), min(E[(m, s)], N) + 1):
                    c += 1
                    k = max(L(m - 1, s), n - E[(m, s - 1)]) + shift
                    q = n - k
                    good = (L(m - 1, s) <= k <= E[(m - 1, s)]
                            and L(m, s - 1) <= q <= E[(m, s - 1)]
                            and 1 <= k < n
                            and 2 * k - 1 + (2 * (m - 1) * k - beta[(m - 1, s)])
                            + (2 * m * q - beta[(m, s - 1)]) == 2 * m * n - beta[(m, s)]
                            and U[s][k] == 2 * (m - 1) * k - beta[(m - 1, s)]
                            and U[s - 1][q] == 2 * m * q - beta[(m, s - 1)])
                    if not good:
                        bad.append((m, s, n, k))
        return c, bad

    report("E4", *E4())

    c, bad, _ = E2(dr=1)
    report("N1", c, bad, expect_bad=True)
    c, bad, _ = E2(dl=1)
    report("N2", c, bad, expect_bad=True)
    c, bad, _ = E2(e=E_table(M, S, base_shift=1))
    report("N3", c, bad, expect_bad=True)
    report("N4", *E4(shift=1), expect_bad=True)

    print(f"\n範囲: 2<=s<={S}, 1<=n<={N}。" + ("全検査が期待どおり" if rc == 0 else "⚠ 期待と違う検査がある"))
    return rc


if __name__ == "__main__":
    S = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    raise SystemExit(run(S, N))
