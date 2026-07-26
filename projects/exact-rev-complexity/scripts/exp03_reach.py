"""候補3 の到達則 $\\mathrm{reach}(p,e)$: 構成の機械検証と、$p=6,7$ への厳密探索。

    python3 scripts/exp03_reach.py --verify-construction        # 定理 B1（下界）の検証
    python3 scripts/exp03_reach.py --exact 6 1                  # p=6, e=1 を厳密に判定

## 定理 B1（証明済み・本スクリプトで機械検証）

$$\\mathrm{reach}(p,e) \\;\\ge\\; (e+2)\\,2^{p-2} \\qquad (p\\ge2)$$

構成: (i) 常時可用な源 0 から Bennett の再帰スケジュールで $2^{p-1}$ に clean 到達する。
(ii) 単一ペブル状態 $\\{x\\}$ から、$x$ を足場に残りの $p-1$ 本で $x+2^{p-2}$ へ clean 到達し
（`bennett(x, p-1)`）、そのあと $x$ を不可逆消去する。これを $e$ 回繰り返す。
合計 $2^{p-1} + e\\,2^{p-2} = (e+2)2^{p-2}$。

**これは LTV Lemma 1（`arXiv:quant-ph/9703009` / Physica D 120:168–176, 1998）の厳密な改良**である。
LTV は「$n+2$ ペブルと $m-1$ 回の消去で長さ $m2^n$」= 本記法で $(e+1)2^{p-2}$ しか保証しない
（2 本の足場を交互に置くため、最終区間で不要な前方足場 1 ブロック分 $2^{p-2}$ を損している）。

## 予想 B2（未証明）

上式は等号で成立する。$p\\le5$（$e\\le4$）で全数確認済み。$p\\ge6$ は状態数の壁（下記）。

## 厳密探索の方法

素朴 BFS は $\\binom{n}{\\le p}\\times(e+1)$ 状態で、$p=6,e=1$（$n=48$）でも 2800 万状態になる。
そこで (a) **手数ではなく到達可能性だけ**を見る、(b) 状態を組合せ数体系で整数に**ランク付け**して
`bytearray` に持つ（1 状態 1 バイト）、(c) 鎖では動かせる頂点がペブル近傍だけなので
**候補手を $O(k)$ に絞る**、の3点で詰める。
"""

from __future__ import annotations

import argparse
import sys
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import landauer as ld  # noqa: E402
import revpebble as rp  # noqa: E402

DATA = ROOT / "data"


# ---------------------------------------------------------------------------
# 定理 B1 の構成
# ---------------------------------------------------------------------------


def bennett(anchor: int, q: int) -> list[tuple[str, int]]:
    """足場 `anchor` がペブル済み（または常時可用な 0）で自由ペブルが `q` 本あるとき、
    `anchor + 2**(q-1)` に 1 個だけ足すスケジュール（間は全て clean に戻す）。ピークは `q`。

    $q=1$: `anchor+1` を置くだけ。
    $q\\ge2$: 中点 $m=anchor+2^{q-2}$ に `bennett(anchor,q-1)` で到達 →
    $m$ を足場に `bennett(m,q-1)` で $anchor+2^{q-1}$ へ → 最初の半分を逆再生して $m$ を消す。
    """
    if q <= 0:
        raise ValueError("q >= 1")
    if q == 1:
        return [("put", anchor + 1)]
    mid = anchor + 2 ** (q - 2)
    first = bennett(anchor, q - 1)
    second = bennett(mid, q - 1)
    undo = [("take" if a == "put" else "put", v) for a, v in reversed(first)]
    return first + second + undo


def construction(p: int, e: int) -> list[tuple[str, int]]:
    """定理 B1 の構成。長さ $(e+2)2^{p-2}$ の鎖を、ピーク $p$・消去 $e$ 回で clean に勝つ。"""
    if p < 2:
        raise ValueError("p >= 2")
    seq = bennett(0, p)  # ∅ -> {2^{p-1}}
    x = 2 ** (p - 1)
    for _ in range(e):
        seq += bennett(x, p - 1)  # {x} -> {x, x+2^{p-2}}
        seq.append(("erase", x))  # x を不可逆消去
        x += 2 ** (p - 2)
    return seq


def simulate(n: int, p: int, seq: list[tuple[str, int]]) -> tuple[bool, str]:
    """スケジュールが規則（先行点条件・ピーク・clean 終端 $\\{n\\}$）を満たすか検証する。"""
    state: set[int] = set()
    peak = 0
    erasures = 0
    for i, (act, v) in enumerate(seq):
        if v < 1 or v > n:
            return False, f"手 {i}: 頂点 {v} が範囲外（n={n}）"
        ready = (v - 1) == 0 or (v - 1) in state
        if act == "put":
            if v in state:
                return False, f"手 {i}: put({v}) は既にペブル済み"
            if not ready:
                return False, f"手 {i}: put({v}) の先行点が未ペブル"
            state.add(v)
            if len(state) > p:
                return False, f"手 {i}: ピーク超過 {len(state)} > {p}"
            peak = max(peak, len(state))
        elif act == "take":
            if v not in state:
                return False, f"手 {i}: take({v}) は未ペブル"
            if not ready:
                return False, f"手 {i}: take({v}) が可逆でない"
            state.discard(v)
        else:
            if v not in state:
                return False, f"手 {i}: erase({v}) は未ペブル"
            if ready:
                return False, f"手 {i}: erase({v}) は実は可逆"
            state.discard(v)
            erasures += 1
    if state != {n}:
        return False, f"終端が clean でない: {sorted(state)}"
    return True, f"peak={peak}, 消去={erasures}, 手数={len(seq)}"


# ---------------------------------------------------------------------------
# 厳密な到達可能性判定（メモリ節約版）
# ---------------------------------------------------------------------------


def _ranker(n: int, p: int):
    """位置 $1..n$ から $\\le p$ 個選ぶ集合を colex 順で整数に写す。"""
    tbl = [[comb(i, j) if j <= i else 0 for j in range(p + 2)] for i in range(n + 2)]
    # サイズ k の集合の開始オフセット
    off = [0] * (p + 2)
    for k in range(1, p + 2):
        off[k] = off[k - 1] + (tbl[n][k - 1] if k - 1 <= p else 0)
    total = off[p + 1]

    def rank(mask: int) -> int:
        r = 0
        k = 0
        m = mask >> 1  # 位置 1 が bit0
        idx = 0
        while m:
            if m & 1:
                k += 1
                r += tbl[idx][k]
            m >>= 1
            idx += 1
        return off[k] + r

    return rank, total


def reachable(n: int, p: int, e: int, *, verbose: bool = False) -> bool:
    """chain(n) の clean 状態 $\\{n\\}$ がピーク $p$・消去予算 $e$ で到達可能か。

    手数は求めない（到達可能性のみ）。層 $u=0..e$ ごとに `bytearray` の訪問表を持つ。
    """
    if p < 1:
        return False
    rank, total = _ranker(n, p)
    seen = [bytearray(total) for _ in range(e + 1)]
    goal = 1 << n
    frontier: list[tuple[int, int]] = [(0, 0)]
    seen[0][rank(0)] = 1
    visited = 1
    while frontier:
        nxt: list[tuple[int, int]] = []
        for mask, u in frontier:
            if mask == goal:
                return True
            k = mask.bit_count()
            # 候補手は「ペブルの近傍」だけ: 位置 1 の toggle, 各ペブル x の toggle-off と x+1 の put
            cands: list[int] = [1]
            m = mask >> 1
            idx = 0
            while m:
                if m & 1:
                    cands.append(idx + 1)
                    cands.append(idx + 2)
                m >>= 1
                idx += 1
            for v in cands:
                if v < 1 or v > n:
                    continue
                bit = 1 << v
                ready = (v == 1) or bool(mask & (1 << (v - 1)))
                if mask & bit:
                    if ready:
                        nm, nu = mask ^ bit, u
                    elif u < e:
                        nm, nu = mask ^ bit, u + 1
                    else:
                        continue
                elif ready and k < p:
                    nm, nu = mask | bit, u
                else:
                    continue
                r = rank(nm)
                if not seen[nu][r]:
                    seen[nu][r] = 1
                    visited += 1
                    nxt.append((nm, nu))
        frontier = nxt
        if verbose:
            print(f"    フロンティア {len(frontier):>9d}  訪問累計 {visited:>10d}", flush=True)
    return False


def exact_reach(p: int, e: int, *, verbose: bool = False) -> int | None:
    """予想 B2 の値 $(e+2)2^{p-2}$ が到達可能で、$+1$ が到達不能かを確認する。

    返り値: 確認できたら厳密な reach、$+1$ が到達可能だった（= 予想が偽）なら None。
    """
    pred = (e + 2) * 2 ** (p - 2)
    print(f"  p={p} e={e}: 予想値 {pred} を検査")
    ok_lo = reachable(pred, p, e, verbose=verbose)
    print(f"    n={pred}   到達可能? {ok_lo}")
    if not ok_lo:
        print("    → 下界が崩れた（構成の検証と矛盾するので実装バグを疑うこと）")
        return None
    ok_hi = reachable(pred + 1, p, e, verbose=verbose)
    print(f"    n={pred+1} 到達可能? {ok_hi}")
    if ok_hi:
        print("    → 予想 B2 は偽（reach が予想値より大きい）")
        return None
    print(f"    → reach({p},{e}) = {pred} を確認")
    return pred


# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--verify-construction", action="store_true")
    ap.add_argument("--pmax", type=int, default=8)
    ap.add_argument("--emax", type=int, default=6)
    ap.add_argument("--exact", type=int, nargs=2, metavar=("P", "E"))
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    if args.exact:
        p, e = args.exact
        exact_reach(p, e, verbose=args.verbose)
        return 0

    if args.verify_construction:
        print("== 定理 B1 の構成の機械検証（規則・ピーク・消去回数・clean 終端）==")
        bad = 0
        for p in range(2, args.pmax + 1):
            for e in range(0, args.emax + 1):
                n = (e + 2) * 2 ** (p - 2)
                seq = construction(p, e)
                ok, why = simulate(n, p, seq)
                ecount = sum(1 for a, _v in seq if a == "erase")
                good = ok and ecount == e
                bad += 0 if good else 1
                flag = "ok  " if good else "FAIL"
                print(f"  {flag} p={p} e={e} n=(e+2)2^(p-2)={n:4d}  {why}")
        print(f"  不合格: {bad} 件")
        # 小さい (p,e) では素朴エンジンと突き合わせる（二重照合）
        print("\n== 素朴エンジン（landauer.reach_e）との照合（p<=5）==")
        for p in range(2, 6):
            for e in range(0, 4):
                pred = (e + 2) * 2 ** (p - 2)
                got = ld.reach_e(p, e, nmax=pred + 3)
                print(f"  p={p} e={e}: reach_e={got} 予想={pred} {'ok' if got == pred else 'MISMATCH'}")
        return 0

    print("--verify-construction か --exact P E を指定してください")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
