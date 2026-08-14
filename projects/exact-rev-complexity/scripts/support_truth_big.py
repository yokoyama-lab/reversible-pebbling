"""大インスタンス用の rank 圧縮・層別 BFS ＋ 予想 U（コミット順序 DP）の全数照合。

`scripts/support_truth.py` の set ベース BFS はメモリが張るので、状態を
サイズ優先 colex で整数 rank に写し bytearray で持つ（1 状態 1 バイト×2 本:
訪問と u_min）。**このファイルは標準ライブラリのみ・単体で動く**（<host> / s3 へ
scp して回すため。DP も内蔵）。

照合の設計（反例ハント）:
  - 到達側（u_min ≤ e の全 mask）: DP と全数照合。
    破れの本命は「BFS < DP」（事前足場の相互作用を DP が見えない）方向。
  - 非到達側: k ≤ kchk（既定 4）の全 mask で DP > e を確認。
  - 反例が出たら即 stdout と JSON に記録（それが最大の成果）。

selftest はリポジトリ内でのみ動く（support_truth / umin_dp と突き合わせ）。

    python3 scripts/support_truth_big.py --selftest
    python3 scripts/support_truth_big.py --run 6 2 --n 65 --out /tmp/p6e2.json
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path

INF = float("inf")


# ---------------------------------------------------------------------------
# 予想 U の DP（umin_dp.py と同一ロジックの内蔵版。selftest で照合する）
# ---------------------------------------------------------------------------


def c_stair(g: int, q: int) -> float:
    if q <= 0:
        return INF
    if q == 1:
        return 0 if g == 1 else INF
    return max(0, -(-(g - (1 << (q - 1))) // (1 << (q - 2))))


def umin_dp(positions: tuple[int, ...], p: int) -> float:
    k = len(positions)
    if k == 0:
        return 0

    @lru_cache(maxsize=None)
    def best(done: int) -> float:
        if done == (1 << k) - 1:
            return 0
        placed = bin(done).count("1")
        free = p - placed
        out = INF
        for j in range(k):
            if done & (1 << j):
                continue
            x = positions[j]
            pred = 0
            for i in range(k):
                if done & (1 << i) and positions[i] < x:
                    pred = max(pred, positions[i])
            c = c_stair(x - pred, free)
            if c < INF:
                r = best(done | (1 << j))
                if c + r < out:
                    out = c + r
        return out

    return best(0)


# ---------------------------------------------------------------------------
# rank 圧縮 BFS
# ---------------------------------------------------------------------------


class Ranker:
    """位置 1..n の ≤p 元集合をサイズ優先 colex で 0..total-1 に写す。"""

    def __init__(self, n: int, p: int) -> None:
        self.n, self.p = n, p
        self.tbl = [[comb(i, j) for j in range(p + 1)] for i in range(n + 1)]
        self.off = [0] * (p + 2)
        for k in range(p + 1):
            self.off[k + 1] = self.off[k] + comb(n, k)
        self.total = self.off[p + 1]

    def rank(self, mask: int) -> int:
        r = 0
        j = 0
        m = mask >> 1  # bit0 = 位置1
        idx = 0
        tbl = self.tbl
        while m:
            if m & 1:
                j += 1
                r += tbl[idx][j]
            m >>= 1
            idx += 1
        return self.off[j] + r

    def rank_combo(self, combo: tuple[int, ...]) -> int:
        r = 0
        tbl = self.tbl
        for j, pos in enumerate(combo, start=1):
            r += tbl[pos - 1][j]
        return self.off[len(combo)] + r


def bfs_big(n: int, p: int, e: int, *, verbose: bool = True) -> dict:
    rk = Ranker(n, p)
    total = rk.total
    umin = bytearray(b"\xff") * total
    minsupp: list[dict[int, tuple[int, int]]] = [dict() for _ in range(e + 1)]
    layer_sizes = [0] * (e + 1)
    goal_bit = 1 << n
    t0 = time.time()

    seen = bytearray(total)  # 現在層の訪問表（層開始時は種が立っている）
    r0 = rk.rank(0)
    seen[r0] = 1
    stack = [0]
    for u in range(e + 1):
        if not stack:
            break
        umin_local = umin
        ms_u = minsupp[u]
        seen_next = bytearray(total)
        stack_next: list[int] = []
        cnt = 0
        rank = rk.rank
        while stack:
            mask = stack.pop()
            cnt += 1
            r = rank(mask)
            if umin_local[r] == 255:
                umin_local[r] = u
            if mask:
                f = mask.bit_length() - 1
                rest = mask ^ (1 << f)
                s = rest.bit_length() - 1 if rest else 0
                cur = ms_u.get(f)
                if cur is None or s < cur[0] or (s == cur[0] and mask < cur[1]):
                    ms_u[f] = (s, mask)
            k = mask.bit_count()
            room = k < p
            if room and not (mask & 2):
                nm = mask | 2
                nr = rank(nm)
                if not seen[nr]:
                    seen[nr] = 1
                    stack.append(nm)
            m2 = mask
            while m2:
                low = m2 & -m2
                m2 ^= low
                if room:
                    b2 = low << 1
                    if b2 <= goal_bit and not (mask & b2):
                        nm = mask | b2
                        nr = rank(nm)
                        if not seen[nr]:
                            seen[nr] = 1
                            stack.append(nm)
                nm = mask ^ low
                if low == 2 or (mask & (low >> 1)):
                    nr = rank(nm)
                    if not seen[nr]:
                        seen[nr] = 1
                        stack.append(nm)
                elif u < e:
                    nr = rank(nm)
                    if not seen_next[nr]:
                        seen_next[nr] = 1
                        stack_next.append(nm)
        layer_sizes[u] = cnt
        if verbose:
            print(
                f"    層 u={u}: {cnt:,d} 状態  （累計 {time.time()-t0:7.1f}s、"
                f"次層の種 {len(stack_next):,d}）",
                flush=True,
            )
        seen = seen_next
        stack = stack_next
    return {
        "n": n,
        "p": p,
        "e": e,
        "ranker": rk,
        "umin": umin,
        "minsupp": minsupp,
        "layer_sizes": layer_sizes,
        "seconds": round(time.time() - t0, 1),
    }


# ---------------------------------------------------------------------------
# 照合
# ---------------------------------------------------------------------------


def check_u(res: dict, *, kchk: int = 4, verbose: bool = True) -> dict:
    n, p, e = res["n"], res["p"], res["e"]
    rk: Ranker = res["ranker"]
    umin = res["umin"]
    t0 = time.time()
    pts_reach = pts_unreach = 0
    bad: list[dict] = []
    for k in range(1, p + 1):
        cnt_k = 0
        for combo in combinations(range(1, n + 1), k):
            r = rk.rank_combo(combo)
            obs = umin[r]
            if obs != 255:
                pts_reach += 1
                pred = umin_dp(combo, p)
                if pred != obs:
                    bad.append({"mask": list(combo), "bfs": obs, "dp": None if pred is INF else int(pred)})
                    print(f"  ★反例: {set(combo)} BFS={obs} DP={pred}", flush=True)
            elif k <= kchk:
                pts_unreach += 1
                pred = umin_dp(combo, p)
                if pred <= e:
                    bad.append({"mask": list(combo), "bfs": None, "dp": int(pred)})
                    print(f"  ★反例(非到達側): {set(combo)} BFS=不能 DP={pred}", flush=True)
            cnt_k += 1
        if verbose:
            print(
                f"    照合 k={k}: {cnt_k:,d} 組合せ済み（累計 {time.time()-t0:7.1f}s）",
                flush=True,
            )
    return {
        "pts_reach": pts_reach,
        "pts_unreach": pts_unreach,
        "kchk": kchk,
        "counterexamples": bad,
        "check_seconds": round(time.time() - t0, 1),
    }


def stair_expected(m: int, p: int) -> int:
    return max(0, -(-(m - (1 << (p - 1))) // (1 << (p - 2))))


def run_one(p: int, e: int, n: int, kchk: int, out: Path | None) -> int:
    print(f"== (p={p}, e={e}, n={n}) rank空間 {Ranker(n,p).total:,d} ==", flush=True)
    res = bfs_big(n, p, e)
    # 到達の階段の照合（対照）
    stair_bad = []
    for m in range(1, n + 1):
        r = res["ranker"].rank(1 << m)
        obs = res["umin"][r]
        exp = stair_expected(m, p)
        exp_v = exp if exp <= e else 255
        if obs != exp_v:
            stair_bad.append((m, obs, exp_v))
    print(f"  階段照合: 反例 {len(stair_bad)}", flush=True)
    chk = check_u(res, kchk=kchk)
    ok = not chk["counterexamples"] and not stair_bad
    print(
        f"  U照合: 到達側 {chk['pts_reach']:,d} 点・非到達側(k≤{kchk}) "
        f"{chk['pts_unreach']:,d} 点  反例 {len(chk['counterexamples'])}",
        flush=True,
    )
    if out:
        payload = {
            "p": p,
            "e": e,
            "n": n,
            "layer_sizes": res["layer_sizes"],
            "bfs_seconds": res["seconds"],
            "staircase_bad": stair_bad,
            "tip_minsupp_by_u": {
                str(u): {"s": res["minsupp"][u][n][0],
                          "witness": [i for i in range(1, n + 1) if res["minsupp"][u][n][1] >> i & 1]}
                for u in range(e + 1)
                if n in res["minsupp"][u]
            },
            **{k: v for k, v in chk.items()},
        }
        out.write_text(json.dumps(payload, ensure_ascii=False, indent=1))
        print(f"  保存: {out}", flush=True)
    print(f"  => {'反例なし' if ok else '★★反例あり★★'}", flush=True)
    return 0 if ok else 2


def selftest() -> int:
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import support_truth as st  # noqa: E402
    import umin_dp as ud  # noqa: E402

    fails = 0
    for n, p, e in [(17, 4, 2), (25, 5, 1)]:
        big = bfs_big(n, p, e, verbose=False)
        ref = st.bfs(n, p, e, kmax=p)
        rk: Ranker = big["ranker"]
        mism = 0
        for k in range(1, p + 1):
            for combo in combinations(range(1, n + 1), k):
                mask = 0
                for v in combo:
                    mask |= 1 << v
                a = big["umin"][rk.rank_combo(combo)]
                b = ref["umin_small"].get(mask, 255)
                b = 255 if b is None else b
                if a != b:
                    mism += 1
        ok1 = mism == 0
        ok2 = all(
            big["minsupp"][u].get(n) == ref["minsupp"][u].get(n)
            for u in range(e + 1)
        )
        samples = list(combinations(range(1, n + 1), 3))[::97]
        ok3 = all(umin_dp(c, p) == ud.umin_dp(c, p) for c in samples)
        for ok, msg in [
            (ok1, f"({p},{e},{n}) umin 全表が support_truth と一致"),
            (ok2, f"({p},{e},{n}) 先端 minsupp が一致"),
            (ok3, f"({p},{e},{n}) 内蔵 DP が umin_dp と一致（標本 {len(samples)}）"),
        ]:
            print(f"  {'ok  ' if ok else 'FAIL'} {msg}")
            fails += 0 if ok else 1
    print("selftest:", "全件成功" if fails == 0 else f"{fails} 件失敗")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--run", type=int, nargs=2, metavar=("P", "E"))
    ap.add_argument("--n", type=int)
    ap.add_argument("--kchk", type=int, default=4)
    ap.add_argument("--out", type=Path, default=None)
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    if args.run:
        p, e = args.run
        n = args.n if args.n else (e + 2) * (1 << (p - 2)) + 1
        return run_one(p, e, n, args.kchk, args.out)
    print("--selftest か --run P E [--n N] を指定")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
