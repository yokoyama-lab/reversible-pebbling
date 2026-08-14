"""定理 U から予想 G（フロンティア支持則）を導く射影の検査。

`data/conj_g_proof_attempt.md` §8 の導出を機械で確かめる。

  G-1  max{ max S : W_p(S) <= u } = tau_u = (u+4)2^{p-2} - 1
  G-2  {f} in R_u  <=>  f <= c_u = (u+2)2^{p-2}
  G-3  c_u < f <= tau_u のとき
         max{ f - s : W_p(S) <= u, max S = f, s = 第2最大 }
       = Gmax(u,f) = max( 3*2^{p-3}[u>=1 かつ f-c_u <= 2^{p-3}],  2^{floor(log2 d)} )
       ただし d = c_u + 2^{p-1} - f

3 通りを突き合わせる:
  (a) 総当たり（W_p の定義から直接）
  (b) 原文 `ic3_b2_tight_support.md` §2 の閉形式
  (c) 本稿 §8.3 の還元（鎖 + f の pred = s）による 2 パラメタ最適化

    python3 scripts/conj_g_projection.py
"""

from __future__ import annotations

import sys
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from dismantle_dp import W_commit  # noqa: E402

INF = float("inf")


def c_of(p: int, u: int) -> int:
    return (u + 2) * (1 << (p - 2))


def tau_of(p: int, u: int) -> int:
    return c_of(p, u) + (1 << (p - 1)) - 1


# --- (a) 総当たり ---------------------------------------------------------


def gmax_brute(p: int, u: int, f: int):
    best = None
    for k in range(1, p + 1):
        for rest in combinations(range(1, f), k - 1):
            S = tuple(sorted(rest + (f,)))
            if W_commit(S, p) > u:
                continue
            s = S[-2] if len(S) >= 2 else 0
            if best is None or f - s > best:
                best = f - s
    return best


def frontier_max_brute(p: int, u: int, limit: int):
    best = 0
    for k in range(1, p + 1):
        for S in combinations(range(1, limit + 1), k):
            if W_commit(S, p) <= u:
                best = max(best, S[-1])
    return best


# --- (b) 原文の閉形式 -----------------------------------------------------


def g_closed(p: int, u: int, f: int):
    cu = c_of(p, u)
    d = cu + (1 << (p - 1)) - f
    if d < 1:
        return None
    band = 3 * (1 << (p - 3)) if (u >= 1 and p >= 3 and f - cu <= (1 << (p - 3))) else 0
    return max(band, 1 << (d.bit_length() - 1))


# --- (c) 還元した最適化 ---------------------------------------------------


def g_reduced(p: int, u: int, f: int):
    """max over r in [2,p], A in [0,u] of V = (A+2)2^{p-r-1}
       s.t. 1 <= f - V <= (u-A)2^{p-2} + 2^p - 2^{p-r+1}。
       r=p（自由ペブル1本）では gap は 1 のみ（A=0, V=1）。"""
    best = None
    for r in range(2, p + 1):
        j = p - r - 1
        for A in range(0, u + 1):
            if j >= 0:
                V = (A + 2) << j
            else:
                if A != 0:
                    continue
                V = 1
            maxchain = (u - A) * (1 << (p - 2)) + (1 << p) - (1 << (p - r + 1))
            if not (1 <= f - V <= maxchain):
                continue
            if best is None or V > best:
                best = V
    return best


# --------------------------------------------------------------------------


def main() -> int:
    rc = 0
    for p in (3, 4, 5):
        for u in range(3):
            cu, tau = c_of(p, u), tau_of(p, u)
            # G-1（総当たりが現実的な範囲のみ）
            if tau <= 20:
                fm = frontier_max_brute(p, u, tau + 2)
                ok1 = "ok" if fm == tau else f"✗ 実測 {fm}"
                print(f"p={p} u={u}: G-1 tau_u={tau} … {ok1}")
                if fm != tau:
                    rc = 1
            # G-2
            bad2 = 0
            for f in range(1, min(tau, 24) + 1):
                single = W_commit((f,), p) <= u
                if single != (f <= cu):
                    bad2 += 1
            print(f"p={p} u={u}: G-2 c_u={cu} 単独到達の判定 不一致 {bad2}")
            rc |= 1 if bad2 else 0
            # G-3
            bad_b = bad_r = n = 0
            for f in range(cu + 1, min(tau, 26) + 1):
                gb, gc, gr = gmax_brute(p, u, f), g_closed(p, u, f), g_reduced(p, u, f)
                n += 1
                if gb != gc:
                    bad_b += 1
                    print(f"   ✗ 閉形式 p={p} u={u} f={f}: 総当たり={gb} 閉形式={gc}")
                if gb != gr:
                    bad_r += 1
                    print(f"   ✗ 還元式 p={p} u={u} f={f}: 総当たり={gb} 還元={gr}")
            print(f"p={p} u={u}: G-3 {n} 点  閉形式と {bad_b} 件不一致 / "
                  f"還元式と {bad_r} 件不一致")
            rc |= 1 if (bad_b or bad_r) else 0
    print("すべて一致" if rc == 0 else "⚠ 不一致あり")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
