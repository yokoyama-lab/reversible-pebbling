"""e-消去ペブリングの**全到達集合**から「タイトな支持区間」の真値を得る。

背景（`data/ic3_b2_findings.md` §5.2, §5.4 項目2）:
  ABC の PDR が返す帰納的不変量は「十分」であって最タイトとは限らない。
  一方、**到達集合 R そのものが最タイトな帰納的不変量**である。
  そこで R を厳密に計算し、

  - 先端の支持要求区間の真値（「x_n が載るなら [a, n-1] に支持が要る」の最大の a）
  - 消去回数 u ごとの同区間（帰納的不変量の条件付き形）
  - u_min(mask)（その配置に到達する最小消去数。単独・対・三体は常に全表）

  を出す。PDR の区間が「PDR の緩み」か「真の広がり」かはこれで判定できる。

設計:
  - 状態 = (mask, u)。mask は位置 1..n のペブル集合（bit v = 位置 v、bit 0 は不使用）、
    u は消去済み回数。節点 0 は常時可用な源（位置 1 の put/take は常に支持あり）。
  - 遷移（`scripts/aiger_pebble.py` の build と同じ規則）:
      put v : v が空、支持あり（v=1 または v-1 にペブル）、|mask| < p
      take v: v にペブル。支持ありなら可逆（同じ u）、支持なしなら消去（u+1、u<e のとき）
  - **u は増えるだけ**なので、u の層ごとに可逆手だけで BFS 閉包し、
    消去手で次層の種を集める。閉包が済んだ層の訪問集合は捨てる（メモリは最大層ぶん）。
  - 集計はストリーミング（訪問時に更新）。乱数不使用・決定的。

検証（--selftest）:
  既知値のみを assert する: B2 検証済み（p≤5, e≤4）の到達の階段
  u_min({m}) = max(0, ceil((m-2^{p-1})/2^{p-2}))、§5.2 の e=0 タイト区間
  （(3,0,5)→3, (4,0,9)→5）、PDR が到達不能を証明した個別状態、
  独立実装 `exp03_reach.reachable` との判定一致。

使い方:
    python3 scripts/support_truth.py --selftest
    python3 scripts/support_truth.py --run 3 1            # p=3, e=1, n=claim+1
    python3 scripts/support_truth.py --run 4 1 --n 13 --save
    python3 scripts/support_truth.py --sweep              # p≤5 × e≤4 + (6,0)
    python3 scripts/support_truth.py --certify 3 1 --mask 4,7   # 到達手順の証明書
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections import deque
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

OUT = ROOT / "data" / "tight_support"


def claim_value(p: int, e: int) -> int:
    """予想 B2 の値 (e+2)·2^{p-2}（p≥2）。"""
    if p < 2:
        raise ValueError("p >= 2")
    return (e + 2) * (1 << (p - 2))


def mask_of(positions: list[int] | tuple[int, ...]) -> int:
    m = 0
    for v in positions:
        m |= 1 << v
    return m


def positions_of(mask: int) -> list[int]:
    out = []
    m = mask
    while m:
        low = m & -m
        out.append(low.bit_length() - 1)
        m ^= low
    return out


def bfs(
    n: int,
    p: int,
    e: int,
    *,
    keep_states: bool = False,
    kmax: int = 3,
    verbose: bool = False,
) -> dict:
    """(mask, u) の全到達集合を層ごとに閉包し、要約を返す。

    返り値:
      layer_sizes[u]   : 層 u の状態数
      umin_small[mask] : |mask| ≤ kmax の到達 mask → 最小 u（全表。既定 kmax=3）
      minsupp[u][f]    : 層 u でフロンティア f を持つ状態の最小の第2最大位置と witness
                         （0 = 支持なし＝単独ペブル）
      maxgap[u][i]     : 層 u で左から i 番目のギャップ（s_i - s_{i-1}, s_0=0）の最大値
      states[u]        : keep_states=True のとき層 u の全 mask（ソート済み）
    """
    goal_bit = 1 << n
    umin_small: dict[int, int] = {}
    minsupp: list[dict[int, tuple[int, int]]] = [dict() for _ in range(e + 1)]
    maxgap: list[dict[int, int]] = [dict() for _ in range(e + 1)]
    layer_sizes = [0] * (e + 1)
    states: list[list[int]] = []
    seeds: set[int] = {0}
    t0 = time.time()
    for u in range(e + 1):
        visited = set(seeds)
        stack = list(visited)
        nxt: set[int] = set()
        can_erase = u < e
        ms_u = minsupp[u]
        mg_u = maxgap[u]
        while stack:
            mask = stack.pop()
            k = mask.bit_count()
            # --- 集計（各 (mask,u) につき 1 回）---
            if k <= kmax and mask not in umin_small:
                umin_small[mask] = u
            if mask:
                f = mask.bit_length() - 1
                rest = mask ^ (1 << f)
                s = rest.bit_length() - 1 if rest else 0
                cur = ms_u.get(f)
                if cur is None or s < cur[0] or (s == cur[0] and mask < cur[1]):
                    ms_u[f] = (s, mask)
                m2, prev, i = mask, 0, 0
                while m2:
                    low = m2 & -m2
                    v = low.bit_length() - 1
                    i += 1
                    g = v - prev
                    if g > mg_u.get(i, 0):
                        mg_u[i] = g
                    prev = v
                    m2 ^= low
            # --- 遷移 ---
            room = k < p
            if room and not (mask & 2):  # put 1（源 0 は常時可用）
                nm = mask | 2
                if nm not in visited:
                    visited.add(nm)
                    stack.append(nm)
            m2 = mask
            while m2:
                low = m2 & -m2
                m2 ^= low
                if room:  # put v+1（支持 = v にペブル）
                    b2 = low << 1
                    if b2 <= goal_bit and not (mask & b2):
                        nm = mask | b2
                        if nm not in visited:
                            visited.add(nm)
                            stack.append(nm)
                nm = mask ^ low  # take v
                if low == 2 or (mask & (low >> 1)):  # 支持あり: 可逆
                    if nm not in visited:
                        visited.add(nm)
                        stack.append(nm)
                elif can_erase:  # 支持なし: 消去（次層へ）
                    nxt.add(nm)
        layer_sizes[u] = len(visited)
        if keep_states:
            states.append(sorted(visited))
        if verbose:
            print(
                f"    層 u={u}: {len(visited):>10,d} 状態  "
                f"（累計 {time.time()-t0:6.1f}s、次層の種 {len(nxt):,d}）",
                flush=True,
            )
        del visited
        seeds = nxt
        if not seeds:
            break
    return {
        "n": n,
        "p": p,
        "e": e,
        "layer_sizes": layer_sizes,
        "umin_small": umin_small,
        "minsupp": minsupp,
        "maxgap": maxgap,
        "states": states if keep_states else None,
        "seconds": round(time.time() - t0, 2),
    }


def staircase(res: dict) -> dict[int, int | None]:
    """単独ペブル {m} の u_min（clean 到達の階段）。None = 到達不能。"""
    return {
        m: res["umin_small"].get(1 << m)
        for m in range(1, res["n"] + 1)
    }


def expected_umin_single(m: int, p: int) -> int:
    """B1+B2 から従う u_min({m}) = max(0, ceil((m - 2^{p-1}) / 2^{p-2}))。"""
    num = m - (1 << (p - 1))
    den = 1 << (p - 2)
    return max(0, -(-num // den))


# ---------------------------------------------------------------------------
# 到達手順の証明書（witness の独立検証）
# ---------------------------------------------------------------------------


def find_schedule(n: int, p: int, e: int, target: int) -> list[tuple[str, int]] | None:
    """(target, 任意の u≤e) への最短手順を親付き BFS で探す。見つからなければ None。"""
    start = (0, 0)
    parent: dict[tuple[int, int], tuple[tuple[int, int], tuple[str, int]]] = {}
    seen = {start}
    q = deque([start])
    goal_bit = 1 << n
    hit: tuple[int, int] | None = None
    while q:
        st = q.popleft()
        mask, u = st
        if mask == target:
            hit = st
            break
        k = mask.bit_count()
        room = k < p
        cands: list[tuple[str, int, int, int]] = []  # (act, v, nmask, nu)
        if room and not (mask & 2):
            cands.append(("put", 1, mask | 2, u))
        m2 = mask
        while m2:
            low = m2 & -m2
            m2 ^= low
            v = low.bit_length() - 1
            if room:
                b2 = low << 1
                if b2 <= goal_bit and not (mask & b2):
                    cands.append(("put", v + 1, mask | b2, u))
            nm = mask ^ low
            if low == 2 or (mask & (low >> 1)):
                cands.append(("take", v, nm, u))
            elif u < e:
                cands.append(("erase", v, nm, u + 1))
        for act, v, nm, nu in cands:
            ns = (nm, nu)
            if ns not in seen:
                seen.add(ns)
                parent[ns] = (st, (act, v))
                q.append(ns)
    if hit is None:
        return None
    seq: list[tuple[str, int]] = []
    st = hit
    while st != start:
        st, mv = parent[st]
        seq.append(mv)
    seq.reverse()
    return seq


def validate_schedule(
    n: int, p: int, e: int, seq: list[tuple[str, int]], target: int
) -> tuple[bool, str]:
    """手順を規則どおり再生して検証する（探索とは独立の検査器）。"""
    st: set[int] = set()
    used = 0
    peak = 0
    for i, (act, v) in enumerate(seq):
        if not (1 <= v <= n):
            return False, f"手 {i}: 位置 {v} が範囲外"
        ready = v == 1 or (v - 1) in st
        if act == "put":
            if v in st or not ready or len(st) >= p:
                return False, f"手 {i}: put({v}) が規則違反"
            st.add(v)
            peak = max(peak, len(st))
        elif act == "take":
            if v not in st or not ready:
                return False, f"手 {i}: take({v}) が規則違反"
            st.remove(v)
        elif act == "erase":
            if v not in st or ready:
                return False, f"手 {i}: erase({v}) が規則違反（可逆なら take）"
            st.remove(v)
            used += 1
            if used > e:
                return False, f"手 {i}: 消去予算超過 {used} > {e}"
        else:
            return False, f"手 {i}: 不明な操作 {act}"
    if mask_of(sorted(st)) != target:
        return False, f"終端 {sorted(st)} が目標 {positions_of(target)} と不一致"
    return True, f"peak={peak}, 消去={used}, 手数={len(seq)}"


# ---------------------------------------------------------------------------
# 保存・表示
# ---------------------------------------------------------------------------


def summarize(res: dict) -> dict:
    n, p, e = res["n"], res["p"], res["e"]
    stair = staircase(res)
    pairs = sorted(
        [*positions_of(m), u]
        for m, u in res["umin_small"].items()
        if m.bit_count() == 2
    )
    triples = sorted(
        [*positions_of(m), u]
        for m, u in res["umin_small"].items()
        if m.bit_count() == 3
    )
    return {
        "n": n,
        "p": p,
        "e": e,
        "claim": claim_value(p, e),
        "layer_sizes": res["layer_sizes"],
        "seconds": res["seconds"],
        "staircase": {str(m): u for m, u in stair.items()},
        "tip_minsupp_by_u": {
            str(u): {
                "s": res["minsupp"][u][n][0],
                "witness": positions_of(res["minsupp"][u][n][1]),
            }
            for u in range(e + 1)
            if n in res["minsupp"][u]
        },
        "minsupp_by_u": {
            str(u): {
                str(f): {"s": sv[0], "witness": positions_of(sv[1])}
                for f, sv in sorted(res["minsupp"][u].items())
            }
            for u in range(e + 1)
        },
        "maxgap_by_u": {
            str(u): {str(i): g for i, g in sorted(res["maxgap"][u].items())}
            for u in range(e + 1)
        },
        "pairs_umin": pairs,
        "triples_umin": triples,
    }


def run_one(p: int, e: int, n: int | None, *, save: bool, verbose: bool) -> dict:
    n = n if n is not None else claim_value(p, e) + 1
    est = sum(comb(n, k) for k in range(0, p + 1)) * (e + 1)
    print(f"== p={p} e={e} n={n}（状態数の上限 {est:,d}）==", flush=True)
    res = bfs(n, p, e, verbose=verbose)
    summ = summarize(res)
    stair = staircase(res)
    reach_seen = max((m for m, u in stair.items() if u is not None), default=0)
    print(f"  clean 到達の最大 = {reach_seen}（予想 claim = {summ['claim']}）")
    for u in range(e + 1):
        tip = summ["tip_minsupp_by_u"].get(str(u))
        if tip:
            print(
                f"  u={u}: 先端 f={n} の最小支持 = {tip['s']}"
                f"（真の区間 [{tip['s']},{n-1}]、witness {tip['witness']}）"
            )
        else:
            print(f"  u={u}: 先端 f={n} に到達する状態なし")
    if save:
        OUT.mkdir(parents=True, exist_ok=True)
        path = OUT / f"p{p}e{e}n{n}.json"
        path.write_text(json.dumps(summ, ensure_ascii=False, indent=1))
        print(f"  保存: {path.relative_to(ROOT)}")
    return summ


# ---------------------------------------------------------------------------
# selftest — 既知値のみを assert（テストファースト）
# ---------------------------------------------------------------------------


def selftest() -> int:
    import exp03_reach  # 独立実装（目標到達のみの BFS）  # noqa: E402

    failures: list[str] = []

    def check(cond: bool, msg: str) -> None:
        mark = "ok  " if cond else "FAIL"
        print(f"  {mark} {msg}")
        if not cond:
            failures.append(msg)

    print("== selftest 1: 到達の階段（B2 検証済み p≤5, e≤4 の帰結）==")
    for p, e in [(2, 2), (3, 0), (3, 2), (4, 1), (5, 1)]:
        n = claim_value(p, e) + 1
        res = bfs(n, p, e)
        stair = staircase(res)
        ok = all(
            stair.get(m) == (x if (x := expected_umin_single(m, p)) <= e else None)
            for m in range(1, n + 1)
        )
        check(ok, f"(p={p},e={e},n={n}) u_min({{m}}) = max(0,⌈(m-2^{p-1})/2^{p-2}⌉)")

    print("== selftest 2: e=0 のタイト区間（§5.2 で PDR と一致確認済み）==")
    res = bfs(5, 3, 0)
    check(res["minsupp"][0][5][0] == 3, "(3,0,5) 先端の最小支持 = 3（区間 [3,4]）")
    check(mask_of([3, 5]) in res["umin_small"], "(3,0,5) {3,5} は到達可能")
    check(mask_of([2, 5]) not in res["umin_small"], "(3,0,5) {2,5} は到達不能（PDR の節）")
    res = bfs(9, 4, 0)
    check(res["minsupp"][0][9][0] == 5, "(4,0,9) 先端の最小支持 = 5（区間 [5,8]）")
    check(mask_of([5, 9]) in res["umin_small"], "(4,0,9) {5,9} は到達可能")

    print("== selftest 3: 独立実装 exp03_reach.reachable と判定一致 ==")
    for p, e in [(2, 2), (3, 0), (3, 1), (3, 2), (4, 0), (4, 1)]:
        c = claim_value(p, e)
        res = bfs(c + 1, p, e)
        stair = staircase(res)
        mine_lo = stair.get(c) is not None
        mine_hi = stair.get(c + 1) is not None
        ref_lo = exp03_reach.reachable(c, p, e)
        ref_hi = exp03_reach.reachable(c + 1, p, e)
        check(
            (mine_lo, mine_hi) == (ref_lo, ref_hi) == (True, False),
            f"(p={p},e={e}) clean 到達判定が exp03_reach と一致（{c}: 可, {c+1}: 不可）",
        )

    print("== selftest 4: 証明書（witness の独立検証）==")
    for n, p, e, tgt in [(5, 3, 0, [3, 5]), (9, 4, 0, [5, 9]), (7, 3, 1, [4, 7])]:
        seq = find_schedule(n, p, e, mask_of(tgt))
        if seq is None:
            check(False, f"(p={p},e={e},n={n}) {tgt} への手順が見つからない")
            continue
        ok, why = validate_schedule(n, p, e, seq, mask_of(tgt))
        check(ok, f"(p={p},e={e},n={n}) {tgt} への手順を再生検証（{why}）")

    print()
    if failures:
        print(f"selftest: {len(failures)} 件失敗")
        return 1
    print("selftest: 全件成功")
    return 0


# ---------------------------------------------------------------------------


SWEEP = [(p, e) for p in (2, 3, 4, 5) for e in (0, 1, 2, 3, 4)] + [(6, 0)]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--run", type=int, nargs=2, metavar=("P", "E"))
    ap.add_argument("--n", type=int, default=None, help="鎖長（既定 claim+1）")
    ap.add_argument("--save", action="store_true", help="data/tight_support/ に JSON 保存")
    ap.add_argument("--sweep", action="store_true", help="標準グリッドを実行して保存")
    ap.add_argument("--force", action="store_true", help="既存 JSON も再計算")
    ap.add_argument("--certify", type=int, nargs=2, metavar=("P", "E"))
    ap.add_argument("--mask", type=str, default=None, help="--certify の目標（例: 4,7）")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    if args.selftest:
        return selftest()
    if args.run:
        run_one(args.run[0], args.run[1], args.n, save=args.save, verbose=args.verbose)
        return 0
    if args.certify:
        p, e = args.certify
        if not args.mask:
            print("--mask a,b,c を指定してください")
            return 1
        tgt = [int(x) for x in args.mask.split(",")]
        n = args.n if args.n is not None else claim_value(p, e) + 1
        seq = find_schedule(n, p, e, mask_of(tgt))
        if seq is None:
            print(f"(p={p},e={e},n={n}) {tgt} へは到達不能（u≤{e}）")
            return 0
        ok, why = validate_schedule(n, p, e, seq, mask_of(tgt))
        print(f"(p={p},e={e},n={n}) {tgt} への手順（{why}、検証 {'OK' if ok else 'NG'}）:")
        print("  " + " ".join(f"{a}({v})" for a, v in seq))
        return 0 if ok else 1
    if args.sweep:
        for p, e in SWEEP:
            n = claim_value(p, e) + 1
            path = OUT / f"p{p}e{e}n{n}.json"
            if path.exists() and not args.force:
                print(f"== p={p} e={e} n={n}（既存、スキップ）==")
                continue
            run_one(p, e, None, save=True, verbose=args.verbose)
        return 0
    print("--selftest / --run P E / --sweep / --certify P E --mask a,b のどれかを指定")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
