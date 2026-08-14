"""ABC の PDR フラグを掃引し、不変量のタイトさを BFS 真値と突き合わせる。

`data/ic3_b2_findings.md` §5.4 項目1 の実行。$e\\ge1$ で PDR の不変量が広いのは
(a) PDR の緩み か (b) 真の広がり か。`scripts/support_truth.py` の全到達集合 R が
真値を与えるので、フラグごとの不変量を R と比較して切り分ける。

要点:
- **`pdr -d -I <file>` の `-d` が必須**（`-I` は名前の指定だけ。§5.1）。
- フラグの実際の意味（`pdr -h` 実測）は §5.4 の記載と食い違うので注意:
  `-r` = 一般化に手間をかける（強化方向）、`-n` = 「down をスキップ」のトグル
  （**既定が skip=yes なので `-n` を付けると down が有効になる**）、
  `-c` = down で CTG を扱う（Hassan–Bradley–Somenzi FMCAD'13 はこちら）、
  `-g` = 高価な一般化を**スキップ**（弱化方向の対照）、`-e` = サポート変数のみ
  （既定 yes、付けると解除）。
- タイトさの測り方: 節の字面ではなく**不変量が許す状態集合**で測る。
  一貫状態（cnt_ge*/era_ge* がユニタリ計数と整合する (mask,u)）を全数え上げし、
  どの節（禁止立方体）にもマッチしない集合 A ⊇ R について先端 f=n の最小支持
  min{secondmax(mask) : (mask,u) ∈ A, n ∈ mask, mask ≠ {n}} を u ごとに出す。
  R 側の同じ量（`support_truth`）と一致すればタイト。
- 相互検証: R の全状態がどの節にもマッチしないこと（マッチしたら AIGER 側か
  BFS 側のどちらかがバグ）。

使い方:
    python3 scripts/pdr_tighten.py --quick        # p=3 のみ（動作確認）
    python3 scripts/pdr_tighten.py                # 全インスタンス × 全フラグ
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from itertools import combinations
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from aiger_pebble import ABC, build  # noqa: E402
from support_truth import bfs, claim_value  # noqa: E402

OUTFILE = ROOT / "data" / "tight_support" / "pdr_matrix.json"

# (p, e, ABC タイムアウト秒)。n は claim+1。§5.3 で ABC が完走した範囲 + 対照。
INSTANCES = [
    (3, 0, 60),
    (4, 0, 120),
    (3, 1, 60),
    (3, 2, 60),
    (4, 1, 300),
    (4, 2, 600),
    (5, 1, 600),
]

FLAGSETS = [
    "",          # 既定
    "-r",        # 一般化に手間
    "-n",        # down 有効化（既定は skip）
    "-n -c",     # down + CTG（HBS'13）
    "-r -n -c",  # 全部強化
    "-j",        # 簡略一般化
    "-f",        # flop をコスト順に
    "-i",        # 中間フレームからの clause pushing
    "-p",        # proof obligation の再利用
    "-b",        # blocking つき clause pushing
    "-g",        # 高価な一般化をスキップ（弱化方向の対照）
    "-e",        # サポート変数限定を解除
]


# ---------------------------------------------------------------------------
# ABC 実行と PLA パース
# ---------------------------------------------------------------------------


def run_abc(aig: Path, inv: Path, flags: str, timeout: float) -> dict:
    cmd = f"read_aiger {aig}; pdr {flags} -d -I {inv}".replace("  ", " ")
    t0 = time.time()
    try:
        out = subprocess.run(
            [str(ABC), "-c", cmd], capture_output=True, text=True, timeout=timeout
        )
        txt = out.stdout
    except subprocess.TimeoutExpired:
        return {"verdict": "TIMEOUT", "seconds": round(time.time() - t0, 1)}
    verdict = "UNKNOWN"
    if "Property proved" in txt:
        verdict = "UNREACHABLE"
    elif "was asserted" in txt:
        verdict = "REACHABLE"
    return {
        "verdict": verdict,
        "seconds": round(time.time() - t0, 1),
        "tail": txt.strip().splitlines()[-3:],
    }


def parse_inv(text: str, width: int) -> list[tuple[int, int]]:
    """PLA の禁止立方体を (need1, need0) のビット対に。列 j = ラッチ j。"""
    cubes = []
    declared = None
    for ln in text.splitlines():
        if ln.startswith(".i "):
            declared = int(ln.split()[1])
        if not ln or ln[0] not in "01-":
            continue
        row = ln.split()[0]
        if len(row) != width:
            raise ValueError(f"PLA 行幅 {len(row)} ≠ ラッチ数 {width}")
        m1 = m0 = 0
        for j, ch in enumerate(row):
            if ch == "1":
                m1 |= 1 << j
            elif ch == "0":
                m0 |= 1 << j
        cubes.append((m1, m0))
    if declared is not None and declared != width:
        raise ValueError(f".i {declared} ≠ ラッチ数 {width}")
    return cubes


# ---------------------------------------------------------------------------
# 一貫状態の数え上げと意味論的タイトさ
# ---------------------------------------------------------------------------


def packed_universe(n: int, p: int, e: int):
    """全一貫状態 (mask,u) を packed ラッチベクトル（int64）へ。

    ラッチ順（build の割り当て）: x_1..x_n, cnt_ge1..cnt_gep, era_ge1..era_gee。
    packed bit j: j<n → x_{j+1} = mask の bit j+1（つまり x 部 = mask>>1）。
    """
    masks = []
    for k in range(0, p + 1):
        for combo in combinations(range(1, n + 1), k):
            m = 0
            for v in combo:
                m |= 1 << v
            masks.append(m)
    rows = []
    for m in masks:
        k = m.bit_count()
        x_part = m >> 1
        c_part = ((1 << k) - 1) << n
        for u in range(e + 1):
            e_part = ((1 << u) - 1) << (n + p)
            rows.append((m, u, x_part | c_part | e_part))
    mask_arr = np.array([r[0] for r in rows], dtype=np.int64)
    u_arr = np.array([r[1] for r in rows], dtype=np.int64)
    packed = np.array([r[2] for r in rows], dtype=np.int64)
    secondmax = np.array(
        [
            (lambda rest: rest.bit_length() - 1 if rest else 0)(
                r[0] ^ (1 << (r[0].bit_length() - 1))
            )
            if r[0]
            else -1
            for r in rows
        ],
        dtype=np.int64,
    )
    return mask_arr, u_arr, packed, secondmax


def allowed_after(cubes: list[tuple[int, int]], packed: np.ndarray) -> np.ndarray:
    ok = np.ones(len(packed), dtype=bool)
    for m1, m0 in cubes:
        hit = ((packed & m1) == m1) & ((packed & m0) == 0)
        ok &= ~hit
    return ok


def tip_by_u(
    n: int,
    e: int,
    mask_arr: np.ndarray,
    u_arr: np.ndarray,
    secondmax: np.ndarray,
    ok: np.ndarray,
) -> dict[int, int | None]:
    bad = 1 << n
    has_n = (mask_arr & bad) != 0
    not_bad = mask_arr != bad
    out: dict[int, int | None] = {}
    for u in range(e + 1):
        sel = ok & has_n & not_bad & (u_arr == u)
        out[u] = int(secondmax[sel].min()) if sel.any() else None
    return out


# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="p=3 のみ")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument(
        "--workdir", type=Path, default=Path(tempfile.gettempdir()) / "pdr_tighten"
    )
    args = ap.parse_args()
    args.workdir.mkdir(parents=True, exist_ok=True)

    instances = [t for t in INSTANCES if not args.quick or t[0] == 3]
    results = []
    for p, e, tmo in instances:
        n = claim_value(p, e) + 1
        L = n + p + e
        print(f"== p={p} e={e} n={n}（ラッチ {L}、timeout {tmo}s）==", flush=True)

        # 真値（BFS）と R の packed 表現
        truth = bfs(n, p, e, keep_states=True)
        truth_tip = {
            u: (truth["minsupp"][u][n][0] if n in truth["minsupp"][u] else None)
            for u in range(e + 1)
        }
        print(f"  真値 tip minsupp per u: {truth_tip}")
        reach_packed = []
        for u, layer in enumerate(truth["states"]):
            c_parts = np.array(
                [((1 << m.bit_count()) - 1) << n for m in layer], dtype=np.int64
            )
            x_parts = np.array([m >> 1 for m in layer], dtype=np.int64)
            e_part = ((1 << u) - 1) << (n + p)
            reach_packed.append(x_parts | c_parts | e_part)

        mask_arr, u_arr, packed, secondmax = packed_universe(n, p, e)

        g, _names = build(n, p, e)
        aig = args.workdir / f"p{p}e{e}n{n}.aig"
        aig.write_bytes(g.binary())

        def one(flags: str, p=p, e=e, n=n, L=L, tmo=tmo, aig=aig):
            tag = flags.replace(" ", "").replace("-", "_") or "default"
            inv = args.workdir / f"p{p}e{e}n{n}{tag}.inv"
            inv.unlink(missing_ok=True)
            r = run_abc(aig, inv, flags, tmo)
            r["flags"] = flags or "(default)"
            if r["verdict"] == "UNREACHABLE" and inv.exists():
                cubes = parse_inv(inv.read_text(), L)
                r["clauses"] = len(cubes)
                r["cubes"] = cubes
            return r

        with ThreadPoolExecutor(max_workers=args.workers) as ex:
            rows = list(ex.map(one, FLAGSETS))

        inst = {
            "p": p,
            "e": e,
            "n": n,
            "truth_tip_by_u": {str(u): s for u, s in truth_tip.items()},
            "rows": [],
        }
        for r in rows:
            row = {
                "flags": r["flags"],
                "verdict": r["verdict"],
                "seconds": r["seconds"],
            }
            if "cubes" in r:
                cubes = r.pop("cubes")
                ok = allowed_after(cubes, packed)
                inv_tip = tip_by_u(n, e, mask_arr, u_arr, secondmax, ok)
                # 妥当性: R の全状態がどの節にもマッチしない
                valid = all(
                    bool(allowed_after(cubes, rp).all()) for rp in reach_packed
                )
                # bad 状態を不変量そのものが排除しているか（-o 既定 yes だと
                # 性質を帰納仮説に使うので、ダンプが bad を含む可能性がある）
                bad_packed = np.array(
                    [(1 << n) >> 1 | (1 << n) | 0], dtype=np.int64
                )  # {n}: x 部 + cnt_ge1
                excl_bad = not bool(allowed_after(cubes, bad_packed)[0])
                tight = all(
                    inv_tip.get(u) == truth_tip.get(u) for u in range(e + 1)
                )
                row |= {
                    "clauses": r.get("clauses"),
                    "inv_tip_by_u": {str(u): s for u, s in inv_tip.items()},
                    "valid_on_R": valid,
                    "excludes_bad": excl_bad,
                    "tight": tight,
                }
            inst["rows"].append(row)
            tip_str = row.get("inv_tip_by_u", "-")
            print(
                f"  {row['flags']:<10} {row['verdict']:<12} "
                f"{row.get('clauses','-'):>5} 節  tip={tip_str} "
                f"{'TIGHT' if row.get('tight') else ''} "
                f"{'' if row.get('valid_on_R', True) else '★R違反★'}",
                flush=True,
            )
        results.append(inst)

    OUTFILE.parent.mkdir(parents=True, exist_ok=True)
    OUTFILE.write_text(json.dumps(results, ensure_ascii=False, indent=1))
    print(f"保存: {OUTFILE.relative_to(ROOT)}")

    print("\n== まとめ: インスタンスごとにタイトな不変量を出せたフラグ ==")
    for inst in results:
        tight_flags = [r["flags"] for r in inst["rows"] if r.get("tight")]
        print(
            f"  (p={inst['p']},e={inst['e']}) 真値 {inst['truth_tip_by_u']} → "
            f"{tight_flags if tight_flags else '（どのフラグもタイトに届かず）'}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
