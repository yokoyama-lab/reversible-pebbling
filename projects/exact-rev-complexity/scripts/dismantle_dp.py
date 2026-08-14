"""u_min の DP を「解体（dismantling）順序」の形で独立に実装し、突き合わせる。

背景: `data/conj_g_proof_attempt.md` §2.3。予想 U の DP（`scripts/umin_dp.py` の
コミット順序 DP）は、順序を逆から読むと「1 個ずつ取り除いて空にする」形になる:

    T（|T|=k<=p）の解体順序 D=(y_k,...,y_1)。y_j は残りが j 個のときに取り除く。
    cost(D) = Σ_j psi(y_j - pred_{T_j}(y_j), m_j),  m_j = 2^{p-j-1}
    psi(g,m) = max(0, ceil(g/m) - 2)   （m=1/2 は自由ペブル1本: g=1 なら 0、他は ∞）
    W_p(T) = min_D cost(D)

この形式は補題 A・B の証明で使う正本の形。ここでは

  1. 解体形式の最小 == コミット順序 DP == `scripts/umin_dp.py` の umin_dp
  2. 独立実装の BFS（`scripts/support_truth.py` を使わない）で得た u_min と W の一致

を検査する。2 は予想 U の端点（B2 の到達限界）まで含む全 mask 照合。

    python3 scripts/dismantle_dp.py            # 1 と 2
    python3 scripts/dismantle_dp.py --quick    # 1 のみ
"""

from __future__ import annotations

import argparse
import sys
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

INF = float("inf")


# --------------------------------------------------------------------------
# 費用関数


def C(g: int, q: int) -> float:
    """足場からギャップ g を自由ペブル q 本で単独クリーン到達する最小消去数。"""
    if q <= 0:
        return INF
    if q == 1:
        return 0 if g == 1 else INF
    return max(0, -(-g // (1 << (q - 2))) - 2)


def dismantle_cost(order: tuple[int, ...], p: int) -> float:
    """解体順序（先頭が最初に取り除かれる）の費用。"""
    cur = set(order)
    tot = 0.0
    for y in order:
        j = len(cur)
        pred = max([0] + [w for w in cur if w < y])
        c = C(y - pred, p - j + 1)
        if c == INF:
            return INF
        tot += c
        cur.discard(y)
    return tot


def W_commit(positions: tuple[int, ...], p: int) -> float:
    """コミット順序 DP（umin_dp と同じ式を独立に書いたもの）。"""
    k = len(positions)
    if k == 0:
        return 0

    @lru_cache(maxsize=None)
    def best(done: int) -> float:
        if done == (1 << k) - 1:
            return 0
        free = p - bin(done).count("1")
        out = INF
        for j in range(k):
            if done & (1 << j):
                continue
            x = positions[j]
            pred = max([0] + [positions[i] for i in range(k)
                              if (done >> i) & 1 and positions[i] < x])
            c = C(x - pred, free)
            if c < INF:
                out = min(out, c + best(done | (1 << j)))
        return out

    v = best(0)
    best.cache_clear()
    return v


def W_dismantle(positions: tuple[int, ...], p: int) -> float:
    return min((dismantle_cost(o, p) for o in permutations(positions)), default=0)


# --------------------------------------------------------------------------
# 独立実装の BFS（support_truth.py は参照しない）


def umin_bfs(n: int, p: int, emax: int) -> dict[int, int]:
    """mask -> 最小消去数（<= emax のもののみ）。層別 BFS。"""
    out: dict[int, int] = {}
    frontier = {0}
    for u in range(emax + 1):
        seen = set(frontier)
        stack = list(frontier)
        nxt: set[int] = set()
        while stack:
            m = stack.pop()
            if m not in out:
                out[m] = u
            k = bin(m).count("1")
            for v in range(1, n + 1):
                b = 1 << v
                sup = (v == 1) or bool(m & (b >> 1))
                if m & b:
                    if sup:
                        nm = m ^ b
                        if nm not in seen:
                            seen.add(nm)
                            stack.append(nm)
                    else:
                        nxt.add(m ^ b)
                elif sup and k < p:
                    nm = m | b
                    if nm not in seen:
                        seen.add(nm)
                        stack.append(nm)
        frontier = nxt
        if not frontier:
            break
    return out


# --------------------------------------------------------------------------


def check_equivalence(pmax: int = 5, nmax: int = 12) -> int:
    from umin_dp import umin_dp  # noqa: PLC0415

    bad = 0
    n = 0
    for p in range(2, pmax + 1):
        for k in range(1, p + 1):
            for T in combinations(range(1, nmax + 1), k):
                a, b, c = W_dismantle(T, p), W_commit(T, p), umin_dp(T, p)
                n += 1
                if not (a == b == c):
                    bad += 1
                    if bad <= 5:
                        print(f"  ✗ p={p} T={T}: 解体={a} コミット={b} umin_dp={c}")
    print(f"1) 解体形式 == コミット DP == umin_dp: {n} 集合、不一致 {bad}")
    return bad


def check_bfs(pmax: int = 5, emax: int = 3, nlimit: int = 18) -> int:
    bad_total = 0
    for p in range(2, pmax + 1):
        for e in range(emax + 1):
            n = (e + 2) * (1 << (p - 2)) + 1
            if n > nlimit:
                continue
            tbl = umin_bfs(n, p, e)
            bad = 0
            pts = 0
            for k in range(p + 1):
                for S in combinations(range(1, n + 1), k):
                    m = 0
                    for v in S:
                        m |= 1 << v
                    obs = tbl.get(m)
                    w = W_commit(S, p)
                    pred = int(w) if w <= e else None
                    pts += 1
                    if pred != obs:
                        bad += 1
                        if bad <= 3:
                            print(f"  ✗ p={p} e={e} S={S}: W={pred} BFS={obs}")
            tip = tbl.get(1 << n)
            claim = (e + 2) * (1 << (p - 2))
            ok = "ok" if tip is None else f"✗ 到達 {tip}"
            print(f"   p={p} e={e} n={n}: 全 mask {pts} 点 不一致 {bad}"
                  f" / 単独 {{{n}}} は claim {claim} 超なので到達不能のはず … {ok}")
            bad_total += bad + (0 if tip is None else 1)
    print(f"2) 独立 BFS と W の全 mask 照合: 不一致 {bad_total}")
    return bad_total


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="等価性の検査のみ")
    args = ap.parse_args()
    rc = check_equivalence()
    if not args.quick:
        rc += check_bfs()
    return 1 if rc else 0


if __name__ == "__main__":
    raise SystemExit(main())
