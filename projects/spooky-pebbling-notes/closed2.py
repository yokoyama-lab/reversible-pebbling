#!/usr/bin/env python3
"""**予想を使わない**閉じた系 — KSS に欠けていた $T_{UP}$ の漸化式を補って閉じる。

    python3 closed2.py --verify 12 5    # 全数探索と突き合わせ
    python3 closed2.py --theta 12       # theta(s) を系から算出（予想なし）

`closed.py` は $\\theta(s)=s(s+1)/2$ という**予想**で系を閉じていた。こちらは
次の漸化式（`lemmas.py` の候補C。全数探索で等号を確認）で閉じるので**予想を含まない**。

$$T_{UP}(n,s) = \\min_{k\\in[1,n)}\\ \\bigl[\\,2k-1 + T_{UP}(n-k,\\,s-1) + T_{UP}(k,\\,s)\\,\\bigr]$$

**意味**（KSS Lemma 4.1 の unpebbling 版）: 先頭から $v_k$ まで掃いて $v_k$ に
ペブル 1 個だけ残し（$2k-1$ 手）、その状態で尻尾 $v_{k+1}..v_n$ を片付け
（$v_k$ が枠を 1 つ占めるので上限 $s-1$）、最後に頭 $v_1..v_k$ を片付ける（上限 $s$）。

3 本の漸化式（これと KSS Cor 4.7・Cor 4.12）は $(s,n)$ の辞書式順序で整礎なので、
**厳密値がそのまま計算できる**。$\\theta$ は結果として出てくる。
"""
from __future__ import annotations

import argparse
from functools import lru_cache

INF = float("inf")


@lru_cache(maxsize=None)
def T_UP(n: int, s: int) -> float:
    """こちらの漸化式（KSS には無い）。

    **$s=2$ は底として別扱い**（$T_{UP}(n,2)=n^2+n-3$、$n\\ge2$）。分解に使う掃きは
    途中で 2 個のペブルを同時に持つので、$v_n$ の 1 個と合わせて $s\\ge3$ が要る。
    $s=2$ で分解を使うと**到達不能な手順を数えてしまい値が小さく出る**
    （実測 $T_{UP}(3,2)=9$ に対し分解は 7 を返す）。
    """
    if n == 0:
        return 0
    if n == 1:
        return 1 if s >= 1 else INF
    if s < 2:
        return INF
    if s == 2:
        return n * n + n - 3
    return min((2 * k - 1 + T_UP(n - k, s - 1) + T_UP(k, s)
                for k in range(1, n)), default=INF)


@lru_cache(maxsize=None)
def T_UG(n: int, s: int) -> float:
    """KSS Cor 4.12（k=n の項は最小にならないので除く。`closed.py` と同じ理由）。"""
    if n == 0:
        return 0
    if n == 1:
        return 2 if s >= 1 else INF
    if s < 2 and s < n:
        return INF
    return min((2 * k - 1 + T_UP(k, s) + T_UG(n - k, s - 1)
                for k in range(1, n)), default=INF)


@lru_cache(maxsize=None)
def T_P(n: int, s: int) -> float:
    """KSS Cor 4.7。"""
    if n == 1:
        return 1 if s >= 1 else INF
    if s < 3 and s < n:
        return INF
    return min((2 * k - 1 + T_UP(k, s - 1) + T_P(n - k, s - 1)
                for k in range(1, n)), default=INF)


def verify(nmax: int, smax: int) -> int:
    import kss as bfs

    bad, checked = [], 0
    for s in range(1, smax + 1):
        for n in range(1, nmax + 1):
            for name, mine, theirs in (("T_P", T_P(n, s), bfs.T_P(n, s)),
                                       ("T_UP", T_UP(n, s), bfs.T_UP(n, s)),
                                       ("T_UG", T_UG(n, s), bfs.T_UG(n, s))):
                t = INF if theirs is None else theirs
                checked += 1
                if mine != t:
                    bad.append(f"{name}({n},{s}): 漸化式={mine} 全数探索={t}")
    print(f"全数探索との突き合わせ: {checked} 点")
    if bad:
        print(f"NG {len(bad)} 件:")
        for b in bad[:20]:
            print("  -", b)
        return 1
    print(f"すべて一致（n<={nmax}, s<={smax}）")

    # SAT で確定させた値（n=20,21 / s=6）とも突き合わせる
    sat = {(20, 6, "UP"): 67, (20, 6, "UG"): 68, (21, 6, "UP"): 73, (21, 6, "UG"): 72}
    bad2 = []
    for (n, s, kind), want in sat.items():
        got = (T_UP if kind == "UP" else T_UG)(n, s)
        if got != want:
            bad2.append(f"{kind}({n},{s}): 漸化式={got} SAT={want}")
    print("SAT（DRAT 検証済み）との突き合わせ: 4 点 … "
          + ("一致" if not bad2 else f"NG {bad2}"))
    return 1 if bad2 else 0


def theta_from_system(smax: int) -> int:
    """予想を使わずに theta（T_UG-T_UP の符号が反転する n）を系から出す。"""
    print(f"{'s':>3} {'系から出た theta':>16} {'s(s+1)/2':>10} {'一致':>6}")
    bad = 0
    for s in range(2, smax + 1):
        th = None
        for n in range(1, 6 * s * s):
            up, ug = T_UP(n, s), T_UG(n, s)
            if up == INF or ug == INF:
                continue
            if ug - up == -1:
                th = n
                break
        want = s * (s + 1) // 2
        ok = th == want
        bad |= 0 if ok else 1
        print(f"{s:>3} {str(th):>16} {want:>10} {'はい' if ok else 'いいえ':>6}")
    print("\n" + ("theta(s)=s(s+1)/2 は予想ではなく、漸化式の帰結として出た"
                  if not bad else "⚠ 系から出た theta が s(s+1)/2 と違う"))
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--verify", nargs=2, type=int, metavar=("NMAX", "SMAX"))
    ap.add_argument("--theta", type=int, metavar="SMAX")
    a = ap.parse_args()
    if a.verify:
        return verify(*a.verify)
    if a.theta:
        return theta_from_system(a.theta)
    ap.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
