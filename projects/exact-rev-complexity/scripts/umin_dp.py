"""u_min(mask) の閉形式候補「コミット順序 DP」を全到達データと照合する。

候補（予想 U）:
  配置 S = {s_1 < … < s_k}（源 s_0 = 0）へ到達する最小消去数は、
  **最終配置のペブルを 1 つずつ「確定」していく順序** π を選ぶ問題の最小値:

      U(S; p) = min_π Σ_{i=1..k} C( s_{π(i)} − pred_i ;  p − (i−1) )

  ここで pred_i = π の i 手目までに確定済みのペブル（と源 0）のうち s_{π(i)} の
  直下にあるもの、C(g; q) は「常時可用な足場から自由ペブル q 本でギャップ g 先を
  単独クリーン到達する最小消去数」= 到達の階段:

      C(g; q) = max(0, ⌈(g − 2^{q-1}) / 2^{q-2}⌉)   (q ≥ 2)
      C(1; 1) = 0,  C(g; 1) = ∞ (g ≥ 2),  C(g; q≤0) = ∞

  直観: 確定 i 手目には既確定の i−1 本が盤面を占めるので自由ペブルは p−(i−1) 本。
  確定は「直下の足場からの区間問題」に分解される（区間の作業領域は (pred, s] に
  収まり、確定済みペブルには触れない）。
  ペア則 min(C(a;p)+C(b−a;p−1), C(b;p)+C(a;p−1)) はこの特別な場合。

照合:
  1. data/tight_support/*.json の singles / pairs / triples 全表（34 ファイル）
  2. BFS を kmax=p で回し直した**全 mask** の u_min 表（p ≤ 5 の主要インスタンス）
  一点でも外れれば反例として報告する。

    python3 scripts/umin_dp.py --json          # 保存済み JSON と照合
    python3 scripts/umin_dp.py --full          # 全 mask 照合（BFS 再実行、数分）
"""

from __future__ import annotations

import argparse
import json
import sys
from functools import lru_cache
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from support_truth import bfs, claim_value  # noqa: E402

DATA = ROOT / "data" / "tight_support"

INF = float("inf")


def C(g: int, q: int) -> float:
    """常時可用な足場からギャップ g を自由ペブル q 本で単独クリーン到達する最小消去数。"""
    if g <= 0:
        raise ValueError("g >= 1")
    if q <= 0:
        return INF
    if q == 1:
        return 0 if g == 1 else INF
    return max(0, -(-(g - (1 << (q - 1))) // (1 << (q - 2))))


def umin_dp(positions: tuple[int, ...], p: int) -> float:
    """予想 U の DP。確定済み集合ごとの最小コスト（順序は部分集合 DP で吸収）。"""
    k = len(positions)
    if k == 0:
        return 0

    @lru_cache(maxsize=None)
    def best(done_bits: int) -> float:
        if done_bits == (1 << k) - 1:
            return 0
        placed = bin(done_bits).count("1")
        free = p - placed
        out = INF
        for j in range(k):
            if done_bits & (1 << j):
                continue
            x = positions[j]
            pred = 0
            for i in range(k):
                if done_bits & (1 << i) and positions[i] < x:
                    pred = max(pred, positions[i])
            c = C(x - pred, free)
            if c < INF:
                rest = best(done_bits | (1 << j))
                if c + rest < out:
                    out = c + rest
        return out

    return best(0)


# ---------------------------------------------------------------------------


def check_json() -> tuple[int, int, list[str]]:
    pts = 0
    bad: list[str] = []
    for path in sorted(DATA.glob("p*e*n*.json")):
        s = json.loads(path.read_text())
        p, e = s["p"], s["e"]
        # singles
        for m_str, u in s["staircase"].items():
            m = int(m_str)
            pred = umin_dp((m,), p)
            pred_v = int(pred) if pred <= e else None
            pts += 1
            if pred_v != u:
                bad.append(f"{path.name} 単独 {{{m}}}: DP={pred_v} 実測={u}")
        # pairs / triples: 実測に無い組は「u_min > e」の意味なので、DP > e を要求
        seen_pairs = {(a, b): u for a, b, u in s["pairs_umin"]}
        n = s["n"]
        for a, b in combinations(range(1, n + 1), 2):
            pred = umin_dp((a, b), p)
            obs = seen_pairs.get((a, b))
            pred_v = int(pred) if pred <= e else None
            pts += 1
            if pred_v != obs:
                bad.append(f"{path.name} 対 {{{a},{b}}}: DP={pred_v} 実測={obs}")
        seen_tri = {(a, b, c): u for a, b, c, u in s["triples_umin"]}
        for combo in combinations(range(1, n + 1), 3):
            pred = umin_dp(combo, p)
            obs = seen_tri.get(combo)
            pred_v = int(pred) if pred <= e else None
            pts += 1
            if pred_v != obs:
                bad.append(f"{path.name} 三体 {set(combo)}: DP={pred_v} 実測={obs}")
    return pts, len(bad), bad


FULL_INSTANCES = [
    (3, 4, None),
    (4, 2, None),
    (4, 4, None),
    (4, 4, 31),
    (5, 1, None),
    (5, 2, None),
    (5, 4, None),
]


def check_full() -> tuple[int, int, list[str]]:
    pts = 0
    bad: list[str] = []
    for p, e, n in FULL_INSTANCES:
        n = n if n is not None else claim_value(p, e) + 1
        res = bfs(n, p, e, kmax=p)
        table = res["umin_small"]
        print(f"  照合中 p={p} e={e} n={n}（到達 mask {len(table):,d} 件 + 非到達）", flush=True)
        for k in range(1, p + 1):
            for combo in combinations(range(1, n + 1), k):
                m = 0
                for v in combo:
                    m |= 1 << v
                obs = table.get(m)
                pred = umin_dp(combo, p)
                pred_v = int(pred) if pred <= e else None
                pts += 1
                if pred_v != obs:
                    bad.append(
                        f"(p={p},e={e},n={n}) {set(combo)}: DP={pred_v} 実測={obs}"
                    )
    return pts, len(bad), bad


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--mask", type=str, help="単発評価（例: --mask 8,24,26 --p 5）")
    ap.add_argument("--p", type=int, default=None)
    args = ap.parse_args()

    if args.mask:
        combo = tuple(int(x) for x in args.mask.split(","))
        print(f"U({set(combo)}; p={args.p}) = {umin_dp(combo, args.p)}")
        return 0

    rc = 0
    if args.json or not args.full:
        pts, nbad, bad = check_json()
        print(f"JSON 照合: {pts:,d} 点  反例 {nbad}")
        for msg in bad[:20]:
            print(f"  {msg}")
        rc |= 1 if nbad else 0
    if args.full:
        pts, nbad, bad = check_full()
        print(f"全 mask 照合: {pts:,d} 点  反例 {nbad}")
        for msg in bad[:20]:
            print(f"  {msg}")
        if len(bad) > 20:
            print(f"  …ほか {len(bad)-20} 件")
        rc |= 1 if nbad else 0
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
