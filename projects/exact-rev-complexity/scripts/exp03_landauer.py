"""候補3 の実験: 鎖の $e$-Landauer ペブリング曲面 $M^*(n,p,e)$ を厳密計算する。

    python3 scripts/exp03_landauer.py                 # 既定（ops 全域 + bits 縮小域）
    python3 scripts/exp03_landauer.py --nmax 16 --emax 4

出力（`data/` へ・決定的）:
  - `exp03_surface_ops.csv`  : mode=ops の曲面（n, p, e, mstar）
  - `exp03_surface_bits.csv` : mode=bits の曲面（縮小域）
  - `exp03_esat.csv`         : 飽和点 e*(n,p) と予想式の照合
  - `exp03_reach.csv`        : reach(p,e) = 到達可能な最大鎖長
標準出力に読みやすい表を出す。
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


def esat_formula(n: int, p: int) -> int:
    """予想: $e^*_{\\mathrm{ops}}(n,p) = \\lceil (n-1)/(p-1) \\rceil - 1$（$p\\ge2$）。

    根拠となる構成: ペブル $p$ 本を前方へ「飽和直線スイープ」して $p-1$ ずつ進み、
    区間の境界ごとに 1 回だけ不可逆消去する。区間数は $\\lceil (n-1)/(p-1)\\rceil$、
    最初の区間の後端（節点 1）は常時可用な節点 0 のおかげで可逆に外せるので
    消去は区間数 $-1$ 回で済む。
    """
    if n <= 1:
        return 0
    return -(-(n - 1) // (p - 1)) - 1


# ---------------------------------------------------------------------------


def surface(nmax: int, emax: int, mode: str, dp: int, pmin_floor: int | None = None):
    """鎖の曲面を計算して行のリストを返す。"""
    rows = []
    for n in range(1, nmax + 1):
        g = rp.chain(n)
        pm = rp.pmin(g, n)
        if pm is None:
            continue
        lo = pm if pmin_floor is None else min(pm, pmin_floor)
        for p in range(lo, pm + dp + 1):
            t0 = time.time()
            prof = ld.landauer_profile(g, n, p, emax, mode=mode)
            dt = time.time() - t0
            if not ld.is_monotone(prof):
                raise AssertionError(f"非単調（実装バグ）: n={n} p={p} mode={mode} {prof}")
            for e, val in enumerate(prof):
                rows.append(
                    {"n": n, "p": p, "p_min": pm, "e": e, "mode": mode, "mstar": fmt(val)}
                )
            print(
                f"  n={n:2d} p={p} (p_min={pm}) mode={mode} "
                f"M*(e=0..{emax}) = {[fmt(v) for v in prof]}  [{dt:.1f}s]",
                flush=True,
            )
    return rows


def write_csv(path: Path, rows: list[dict], fields: list[str]) -> None:
    with path.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)
    print(f"  -> {path.relative_to(ROOT)} ({len(rows)} 行)")


def bits_esat(args) -> int:
    """`mode="bits"`（一括消去つき・ビット予算）の飽和点 $e^*_{\\mathrm{bits}}$。

    飽和値は「一括取り除きを許した標準ペブリング」の値 $n + \\lceil (n-1)/(p-1)\\rceil$。
    ops 変種と違い、飽和には $\\Theta(n)$ ビットの消去が必要になるはず（要検証）。
    """
    nmax = args.bits_esat_nmax or 10
    print(f"== 飽和点 e*(n,p) mode=bits（n<={nmax}）==")
    rows = []
    for n in range(2, nmax + 1):
        g = rp.chain(n)
        pm = rp.pmin(g, n)
        assert pm is not None
        for p in range(2, min(pm + 3, 9) + 1):
            budget = 2 * n
            prof = ld.landauer_profile(g, n, p, budget, mode="bits")
            if prof[budget] is None or prof[-1] != prof[-2]:
                continue
            e_star = ld.saturation(prof)
            bulk_std = ld.standard_bfs(g, n, p, bulk=True)
            rows.append(
                {
                    "n": n,
                    "p": p,
                    "p_min": pm,
                    "e_star_bits": e_star,
                    "mstar_sat": prof[-1],
                    "bulk_standard": fmt(bulk_std),
                    "n_plus_ceil": n + -(-(n - 1) // (p - 1)),
                }
            )
            print(
                f"  n={n:2d} p={p}: e*_bits={e_star:2d} 飽和値={prof[-1]:3d} "
                f"(一括標準={fmt(bulk_std)}, n+ceil((n-1)/(p-1))={n + -(-(n-1)//(p-1))})"
            )
    write_csv(
        DATA / "exp03_esat_bits.csv",
        rows,
        ["n", "p", "p_min", "e_star_bits", "mstar_sat", "bulk_standard", "n_plus_ceil"],
    )
    return 0


def sub_pmin(args) -> int:
    """消去は $p_{\\min}$ 自体を下げる。$p_{\\min}(n,e)$ と $p<p_{\\min}(n,0)$ の曲面。

    $\\mathrm{reach}(p,e)=(e+2)2^{p-2}$ を逆に解くと
    $p_{\\min}(n,e) = 2 + \\lceil \\log_2 (n/(e+2)) \\rceil$（$n>e+2$）。これを実測と照合する。
    """
    import math

    print("== p_min(n,e) と p_min 未満の曲面（mode=ops）==")
    rows = []
    mism = 0
    for n in args.sub_pmin_ns:
        base = rp.pmin(rp.chain(n), n)
        line = []
        for e in range(args.emax + 1):
            pm = ld.pmin_e(rp.chain(n), n, e)
            pred = 2 + math.ceil(math.log2(n / (e + 2))) if n > e + 2 else (2 if n > 1 else 1)
            ok = pm == pred
            mism += 0 if ok else 1
            line.append(f"{pm}" if ok else f"{pm}(予想{pred})")
            rows.append(
                {"n": n, "e": e, "p_min_e": fmt(pm), "formula": pred, "match": int(ok),
                 "p_min_0": base}
            )
        print(f"  n={n:2d} (p_min(e=0)={base}): p_min(n,e) e=0..{args.emax} -> {line}")
    print(f"  予想 p_min(n,e)=2+ceil(log2(n/(e+2))) との不一致: {mism} 件")
    write_csv(DATA / "exp03_pmin_e.csv", rows, ["n", "e", "p_min_e", "formula", "match", "p_min_0"])

    rows2 = []
    for n in args.sub_pmin_ns:
        base = rp.pmin(rp.chain(n), n)
        assert base is not None
        for p in range(2, base):
            prof = ld.landauer_profile(rp.chain(n), n, p, args.emax, mode="ops")
            if all(v is None for v in prof):
                continue
            print(f"  n={n:2d} p={p} (< p_min={base}): M*(e=0..{args.emax}) = {[fmt(v) for v in prof]}")
            for e, v in enumerate(prof):
                rows2.append({"n": n, "p": p, "p_min_0": base, "e": e, "mode": "ops", "mstar": fmt(v)})
    write_csv(
        DATA / "exp03_surface_sub_pmin.csv",
        rows2,
        ["n", "p", "p_min_0", "e", "mode", "mstar"],
    )
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=20)
    ap.add_argument("--emax", type=int, default=6)
    ap.add_argument("--dp", type=int, default=3, help="p_min から何本上まで見るか")
    ap.add_argument("--bits-nmax", type=int, default=13, help="bits 変種の n 上限（重い）")
    ap.add_argument("--esat-nmax", type=int, default=14)
    ap.add_argument("--esat-pmax", type=int, default=8)
    ap.add_argument("--reach-pmax", type=int, default=5)
    ap.add_argument("--reach-emax", type=int, default=4)
    ap.add_argument(
        "--reach-nmax",
        type=int,
        default=160,
        help="reach 探索の打ち切り長。予想値 (e+2)2^{p-2} を超える余裕が必要（打ち切りの偽陽性防止）",
    )
    ap.add_argument("--bits-esat-nmax", type=int, default=0, help="0 なら bits の飽和点は計算しない")
    ap.add_argument("--only-bits-esat", action="store_true", help="bits の飽和点だけを計算する")
    ap.add_argument("--only-sub-pmin", action="store_true", help="p_min(n,e) と p<p_min の曲面だけ")
    ap.add_argument(
        "--sub-pmin-ns",
        type=int,
        nargs="+",
        default=[8, 12, 16, 20],
        help="p_min(n,e) を調べる n のリスト",
    )
    args = ap.parse_args()

    if args.only_bits_esat:
        return bits_esat(args)
    if args.only_sub_pmin:
        return sub_pmin(args)

    print(f"== 曲面 M*(n,p,e) mode=ops (n<={args.nmax}, e<={args.emax}) ==")
    rows_ops = surface(args.nmax, args.emax, "ops", args.dp)
    write_csv(DATA / "exp03_surface_ops.csv", rows_ops, ["n", "p", "p_min", "e", "mode", "mstar"])

    print(f"\n== 曲面 M*(n,p,e) mode=bits (n<={args.bits_nmax}, e<={args.emax}) ==")
    rows_bits = surface(args.bits_nmax, args.emax, "bits", args.dp)
    write_csv(DATA / "exp03_surface_bits.csv", rows_bits, ["n", "p", "p_min", "e", "mode", "mstar"])

    # ---- 飽和点 e* と予想式の照合（p を小さい側まで広げる）----
    print(f"\n== 飽和点 e*(n,p) mode=ops（p={2}..{args.esat_pmax}, n<={args.esat_nmax}）==")
    esat_rows = []
    mismatch = 0
    for n in range(2, args.esat_nmax + 1):
        g = rp.chain(n)
        pm = rp.pmin(g, n)
        assert pm is not None
        for p in range(2, args.esat_pmax + 1):
            budget = n + 1  # e* <= n-2 なので十分
            prof = ld.landauer_profile(g, n, p, budget, mode="ops")
            if prof[budget] is None:
                continue
            if prof[-1] != prof[-2]:
                raise AssertionError(f"飽和していない: n={n} p={p} {prof}")
            e_star = ld.saturation(prof)
            pred = esat_formula(n, p)
            ok = e_star == pred
            mismatch += 0 if ok else 1
            esat_rows.append(
                {
                    "n": n,
                    "p": p,
                    "p_min": pm,
                    "e_star": e_star,
                    "formula": pred,
                    "match": int(ok),
                    "mstar_sat": prof[-1],
                    "two_n_minus_1": 2 * n - 1,
                    "mstar_e0": fmt(prof[0]),
                }
            )
            if not ok:
                print(f"  MISMATCH n={n} p={p}: e*={e_star} formula={pred} prof={prof}")
    print(f"  照合: {len(esat_rows)} 点中 不一致 {mismatch} 件")
    write_csv(
        DATA / "exp03_esat.csv",
        esat_rows,
        ["n", "p", "p_min", "e_star", "formula", "match", "mstar_sat", "two_n_minus_1", "mstar_e0"],
    )

    # 飽和値が常に 2n-1 か（ops の絶対下界）
    bad = [r for r in esat_rows if r["mstar_sat"] != r["two_n_minus_1"]]
    print(f"  飽和値 == 2n-1 の例外: {len(bad)} 件" + (f" {bad[:3]}" if bad else ""))

    # ---- reach(p,e) ----
    print(f"\n== reach(p,e): ピーク p・消去予算 e で clean 到達できる最大鎖長 ==")
    reach_rows = []
    for p in range(1, args.reach_pmax + 1):
        line = []
        for e in range(args.reach_emax + 1):
            r = ld.reach_e(p, e, nmax=args.reach_nmax)
            if r == args.reach_nmax:
                raise AssertionError(
                    f"reach が打ち切り長に達した（値が信用できない）: p={p} e={e} nmax={r}"
                )
            pred = (e + 2) * 2 ** (p - 2) if p >= 2 else 1
            line.append(r if r == pred else f"{r}(予想{pred})")
            reach_rows.append(
                {
                    "p": p,
                    "e": e,
                    "reach": r,
                    "formula": pred,
                    "match": int(r == pred),
                    "ltv_lemma1_lb": (e + 1) * 2 ** max(p - 2, 0),
                }
            )
        print(f"  p={p}: e=0..{args.reach_emax} -> {line}")
    nmis = sum(1 for r in reach_rows if not r["match"])
    print(f"  予想 reach(p,e)=(e+2)2^(p-2) との不一致: {nmis} 件")
    write_csv(
        DATA / "exp03_reach.csv",
        reach_rows,
        ["p", "e", "reach", "formula", "match", "ltv_lemma1_lb"],
    )

    print("\n== e=1 の効果（mode=ops, p=p_min）==")
    for n in range(2, args.nmax + 1):
        pm = rp.pmin(rp.chain(n), n)
        assert pm is not None
        prof = ld.landauer_profile(rp.chain(n), n, pm, 2, mode="ops")
        if prof[0] is None:
            continue
        drop = prof[0] - prof[1] if prof[1] is not None else None
        print(
            f"  n={n:2d} p_min={pm}: M*(e=0)={prof[0]:3d} -> M*(e=1)={fmt(prof[1]):>3} "
            f"（減 {fmt(drop)}, 下界 2n-1={2*n-1}）"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
