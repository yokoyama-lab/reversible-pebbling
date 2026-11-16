"""候補3 × 候補1 の合流: 木・ピラミッドの $e$ 付き曲面 $M^*(G,p,e)$ と飽和点 $e^*$。

    python3 scripts/exp03_trees.py --emax 8

鎖では $e^*_{\\text{ops}}(n,p) = \\lceil (n-1)/(p-1)\\rceil - 1$、飽和値は $2n-1$ だった
（`data/exp03_results.md` 定理 A）。木では分岐があるので別の法則になるはず。

**木での飽和値の下界**: 非源点の個数を $N$、目標点以外は最後に載っていないので
最小手数は $\\ge N + (N-1) = 2N-1$。鎖と同じ形。ただし木では**同じ点を 2 回以上
置き直す**必要が出る可能性があり、そのとき $2N-1$ には届かない。
ここが鎖との本質的な違いになりうるので、飽和値と $2N-1$ の差を必ず出す。
"""

from __future__ import annotations

import argparse
import csv
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import landauer as ld  # noqa: E402
import revpebble as rp  # noqa: E402

DATA = ROOT / "data"


def fmt(v: int | None) -> str:
    return "-" if v is None else str(v)


def families(hmax_cbt: int, hmax_pyr: int):
    """(名前, Dag, 目標点, 非源点数 N) を列挙する。free-leaves 流儀。"""
    out = []
    for h in range(1, hmax_cbt + 1):
        g = rp.complete_binary_tree(h)
        out.append((g.name, g, g.n - 1, g.n - len(g.free)))
    for h in range(1, hmax_pyr + 1):
        g = rp.pyramid(h)
        out.append((g.name, g, g.n - 1, g.n - len(g.free)))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--emax", type=int, default=8)
    ap.add_argument("--dp", type=int, default=3)
    ap.add_argument("--cbt-hmax", type=int, default=3)
    ap.add_argument("--pyr-hmax", type=int, default=4)
    ap.add_argument("--budget", type=int, default=40, help="飽和点探索用の大きな予算")
    args = ap.parse_args()

    rows: list[dict] = []
    sat_rows: list[dict] = []
    print("== 木・ピラミッドの曲面 M*(G,p,e)（mode=ops, free-leaves 流儀）==")
    for name, g, target, N in families(args.cbt_hmax, args.pyr_hmax):
        pm = rp.pmin(g, target)
        if pm is None:
            continue
        std = ld.standard_bfs(g, target, pm)
        print(
            f"\n  {name}: 頂点 {g.n}, free {len(g.free)}, 非源点 N={N}, p_min={pm}, 2N-1={2*N-1}",
            flush=True,
        )
        for p in range(pm, pm + args.dp + 1):
            t0 = time.time()
            prof = ld.landauer_profile(g, target, p, args.emax, mode="ops")
            if not ld.is_monotone(prof):
                raise AssertionError(f"非単調（バグ）: {name} p={p} {prof}")
            dt = time.time() - t0
            print(
                f"    p={p}: M*(e=0..{args.emax}) = {[fmt(v) for v in prof]}  [{dt:.1f}s]",
                flush=True,
            )
            for e, v in enumerate(prof):
                rows.append(
                    {"family": name, "n_vertices": g.n, "N": N, "p": p, "p_min": pm,
                     "e": e, "mstar": fmt(v)}
                )
            # 飽和点は大きな予算で別に取る
            big = ld.landauer_profile(g, target, p, args.budget, mode="ops")
            if big[-1] is None or big[-1] != big[-2]:
                print(f"      (p={p}: 予算 {args.budget} でも飽和せず — 飽和点は未確定)")
                continue
            es = ld.saturation(big)
            sat = big[-1]
            std_p = ld.standard_bfs(g, target, p)
            sat_rows.append(
                {"family": name, "N": N, "p": p, "p_min": pm, "e_star": es,
                 "mstar_sat": sat, "two_N_minus_1": 2 * N - 1,
                 "gap_vs_2N_1": sat - (2 * N - 1), "standard": fmt(std_p),
                 "mstar_e0": fmt(big[0]),
                 "chain_formula": (-(-(N - 1) // (p - 1)) - 1) if p >= 2 else N - 1}
            )
            print(
                f"      e*={es}, 飽和値={sat}（標準={fmt(std_p)}, 2N-1={2*N-1}, "
                f"差={sat-(2*N-1)}, 鎖の式なら{sat_rows[-1]['chain_formula']}）",
                flush=True,
            )
        del std

    with (DATA / "exp03_trees_surface.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["family", "n_vertices", "N", "p", "p_min", "e", "mstar"])
        w.writeheader()
        w.writerows(rows)
    print(f"\n  -> data/exp03_trees_surface.csv ({len(rows)} 行)")
    with (DATA / "exp03_trees_esat.csv").open("w", newline="") as fh:
        w = csv.DictWriter(
            fh,
            fieldnames=["family", "N", "p", "p_min", "e_star", "mstar_sat", "two_N_minus_1",
                        "gap_vs_2N_1", "standard", "mstar_e0", "chain_formula"],
        )
        w.writeheader()
        w.writerows(sat_rows)
    print(f"  -> data/exp03_trees_esat.csv ({len(sat_rows)} 行)")

    print("\n== 読み取り ==")
    gaps = [r for r in sat_rows if r["gap_vs_2N_1"] != 0]
    print(f"  飽和値 != 2N-1 の事例: {len(gaps)}/{len(sat_rows)} 件")
    for r in gaps[:12]:
        print(f"    {r['family']} p={r['p']}: 飽和値 {r['mstar_sat']} vs 2N-1={r['two_N_minus_1']}")
    mism = [r for r in sat_rows if r["e_star"] != r["chain_formula"]]
    print(f"  e* が鎖の式と違う事例: {len(mism)}/{len(sat_rows)} 件")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
