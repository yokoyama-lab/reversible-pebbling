"""LTV の Procedure A を我々のモデルでそのまま実装し、規約解釈に依らず優劣を決める。

    python3 scripts/exp03_ltv.py --compare      # LTV vs 我々の構成を同じ表に並べる
    python3 scripts/exp03_ltv.py --nonclean 6   # 非 clean 版の厳密 reach（LTV Cor 2 の検算）

## 背景（なぜこれが必要か）

`data/exp03_results.md` §B.1 で「定理 B1 は LTV Lemma 1 を加法的に $2^{p-2}$ 改良する」と
書いたが、**LTV と我々では長さとペブルの数え方が違う**疑いがある:

- LTV Cor 2: 「$n$ ペブルで到達できる最大節点は $\\sum_{i<n}2^i = 2^n-1$」
- 我々: $\\mathrm{reach}(p) = 2^{p-1}$（clean 到達）

本文 §7 の `pebble(s,n)` を読むと差の正体が分かる: **LTV の終端は clean でない。**
`pebble(s,n)` は $s+2^{n-1}, s+2^{n-1}+2^{n-2}, \\dots, s+2^n-1$ の「2 進階段」に
$n$ 個のペブルを**置いたまま**終わる。だから $2^n-1$ まで届く。
我々は目標点だけが載った clean 状態を要求するので $2^{p-1}$ になる。
$(2^p-1+1)/2 = 2^{p-1}$ の「端条件ブリッジ」はこの差を表している。

→ **解釈で争わず、LTV の手順を我々の検証器に通して実測する**のが本モジュールの目的。
"""

from __future__ import annotations

import argparse
import csv
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import revpebble as rp  # noqa: E402

DATA = ROOT / "data"

Move = tuple[str, int]


# ---------------------------------------------------------------------------
# LTV 本文 §7 の相互再帰手続き（原文どおり）
# ---------------------------------------------------------------------------


def ltv_pebble(s: int, n: int) -> list[Move]:
    """LTV `pebble(s,n)`。節点 $s$ が載っている（または $s=0$ の源）前提で、
    自由ペブル $n$ 本を使って $s+1,\\dots,s+2^n-1$ の 2 進階段を**置いたまま**終わる。

    原文:
        pebble(s, n) { if (n = 0) return; t = s + 2^{n-1};
                       pebble(s, n-1); put a free pebble on node t;
                       unpebble(s, n-1); pebble(t, n-1); }
    """
    if n == 0:
        return []
    t = s + 2 ** (n - 1)
    return (
        ltv_pebble(s, n - 1)
        + [("put", t)]
        + ltv_unpebble(s, n - 1)
        + ltv_pebble(t, n - 1)
    )


def ltv_unpebble(s: int, n: int) -> list[Move]:
    """LTV `unpebble(s,n)`。`pebble(s,n)` の逆。

    原文:
        unpebble(s,n) { if (n = 0) return; t = s + 2^{n-1};
                        unpebble(t, n-1); pebble(s, n-1);
                        remove the pebble from node t; unpebble(s, n-1); }
    """
    if n == 0:
        return []
    t = s + 2 ** (n - 1)
    return (
        ltv_unpebble(t, n - 1)
        + ltv_pebble(s, n - 1)
        + [("take", t)]
        + ltv_unpebble(s, n - 1)
    )


def ltv_procedure_a(n: int, m: int, *, finish_clean: bool = True) -> list[Move]:
    """LTV Lemma 1 の Procedure A（本文どおり）。$n+2$ ペブル・$m-1$ 消去で $T_G=m2^n$ を主張。

    原文:
        Procedure A(n, m, G):
        for i := 0, 1, 2, ..., m-1:
            pebble(i2^n, n);
            put springboard on node (i+1)2^n;
            unpebble(i2^n, n);
            if i < m-1 erase springboard on node i2^n;

    実装上の 2 点（どちらも LTV に**有利**に解釈している）:
    - $i=0$ の「erase springboard on node 0」は、節点 0 が常時可用な源で
      そもそもペブルが載っていないため**省略**する（消去に数えない）。
    - 原文どおりに回すと最後に踏み台が $(m-1)2^n$ に残り **clean でない**。
      `finish_clean=True` のとき、それを消去する 1 手を足して clean 終端にする
      （我々のモデルの終端条件に合わせるための最小の補完）。
    """
    seq: list[Move] = []
    for i in range(m):
        s = i * 2**n
        seq += ltv_pebble(s, n)
        seq.append(("put", (i + 1) * 2**n))
        seq += ltv_unpebble(s, n)
        if i < m - 1 and s >= 1:
            seq.append(("erase", s))
    if finish_clean and m >= 2:
        seq.append(("erase", (m - 1) * 2**n))
    return seq


# ---------------------------------------------------------------------------
# 検証器（clean / 非 clean の両方に対応）
# ---------------------------------------------------------------------------


def verify_schedule(
    seq: list[Move],
    target: int,
    *,
    require_clean: bool = True,
) -> dict:
    """手順を我々のモデルの規則で実行し、実測値を返す。

    規則: `put v` / `take v` は先行点 $v-1$ が載っている（または $v=1$）ことを要求。
    `erase v` は先行点が載っていないときの取り除き（不可逆）。
    `require_clean=True` なら終端は $\\{target\\}$ のみ、`False` なら target が載っていれば可。

    返り値の `ok` が False のときは `why` に理由が入る。ピーク・消去回数・手数は実測。
    """
    state: set[int] = set()
    peak = 0
    erasures = 0
    for i, (act, v) in enumerate(seq):
        if v < 1:
            return {"ok": False, "why": f"手 {i}: 節点 {v} は源または範囲外"}
        ready = (v - 1) == 0 or (v - 1) in state
        if act == "put":
            if v in state:
                return {"ok": False, "why": f"手 {i}: put({v}) は既に載っている"}
            if not ready:
                return {"ok": False, "why": f"手 {i}: put({v}) の先行点 {v-1} が未ペブル"}
            state.add(v)
            peak = max(peak, len(state))
        elif act == "take":
            if v not in state:
                return {"ok": False, "why": f"手 {i}: take({v}) は未ペブル"}
            if not ready:
                return {"ok": False, "why": f"手 {i}: take({v}) が可逆でない（先行点 {v-1} が空）"}
            state.discard(v)
        elif act == "erase":
            if v not in state:
                return {"ok": False, "why": f"手 {i}: erase({v}) は未ペブル"}
            if ready:
                return {"ok": False, "why": f"手 {i}: erase({v}) は実は可逆（消去に数える必要なし）"}
            state.discard(v)
            erasures += 1
        else:
            return {"ok": False, "why": f"手 {i}: 未知の操作 {act}"}
    if require_clean:
        if state != {target}:
            return {"ok": False, "why": f"clean でない終端 {sorted(state)}（target={target}）"}
    else:
        if target not in state:
            return {"ok": False, "why": f"target {target} が載っていない（{sorted(state)}）"}
    return {
        "ok": True,
        "why": "",
        "peak": peak,
        "erasures": erasures,
        "moves": len(seq),
        "reached": target,
        "final": sorted(state),
    }


# ---------------------------------------------------------------------------
# 非 clean 版の厳密 reach（我々のモデル ≡ LTV のモデルかを検算する）
# ---------------------------------------------------------------------------


def nonclean_reach(p: int, e: int, nmax: int = 400) -> int:
    """「target が載っていればよい（他のペブルは残ってよい）」版の最大到達節点。

    $e=0$ でこれが $2^p-1$（LTV Cor 2）に一致すれば、
    **我々のモデルと LTV のモデルは終端条件だけが違う**ことの決定的な証拠になる。
    """
    # 到達可能な最大節点を直接求める: ∅ から到達可能な状態の最大要素
    best = 0
    seen = {(0, 0)}
    q: deque[tuple[int, int]] = deque([(0, 0)])
    while q:
        mask, u = q.popleft()
        if mask:
            best = max(best, mask.bit_length() - 1)
        k = mask.bit_count()
        cands = [1]
        m2 = mask >> 1
        idx = 0
        while m2:
            if m2 & 1:
                cands.append(idx + 1)
                cands.append(idx + 2)
            m2 >>= 1
            idx += 1
        for v in cands:
            if v < 1 or v > nmax:
                continue
            bit = 1 << v
            ready = (v == 1) or bool(mask & (1 << (v - 1)))
            if mask & bit:
                if ready:
                    nxt = (mask ^ bit, u)
                elif u < e:
                    nxt = (mask ^ bit, u + 1)
                else:
                    continue
            elif ready and k < p:
                nxt = (mask | bit, u)
            else:
                continue
            if nxt not in seen:
                seen.add(nxt)
                q.append(nxt)
    return best


# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--compare", action="store_true")
    ap.add_argument("--nonclean", type=int, default=0, help="非 clean reach を p<=この値で計算")
    ap.add_argument("--nonclean-emax", type=int, default=2)
    ap.add_argument("--pmax", type=int, default=8)
    ap.add_argument("--mmax", type=int, default=7)
    args = ap.parse_args()

    if args.nonclean:
        print("== 非 clean 版の厳密 reach（LTV Cor 2 の検算）==")
        print("   e=0 で 2^p-1 に一致すれば、我々のモデル ≡ LTV のモデル（終端条件のみ相違）")
        rows = []
        for p in range(1, args.nonclean + 1):
            line = []
            for e in range(args.nonclean_emax + 1):
                r = nonclean_reach(p, e, nmax=4 * 2**p + 8)
                line.append(r)
                rows.append({"p": p, "e": e, "nonclean_reach": r,
                             "ltv_cor2_2p_minus_1": 2**p - 1,
                             "our_clean_reach": (e + 2) * 2 ** (p - 2) if p >= 2 else 1})
            ok = "ok" if line[0] == 2**p - 1 else "MISMATCH"
            print(f"  p={p}: e=0..{args.nonclean_emax} -> {line}   LTV Cor2 の 2^p-1={2**p-1}  [{ok}]")
        with (DATA / "exp03_nonclean_reach.csv").open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=["p", "e", "nonclean_reach",
                                               "ltv_cor2_2p_minus_1", "our_clean_reach"])
            w.writeheader()
            w.writerows(rows)
        print(f"  -> data/exp03_nonclean_reach.csv ({len(rows)} 行)")
        return 0

    if args.compare:
        import exp03_reach as R

        print("== LTV Procedure A を我々のモデルで実測（clean 終端に補完した版）==")
        print("   n=LTV の自由ペブル数, m=区間数。主張は「n+2 ペブル・m-1 消去で T_G=m*2^n」")
        rows = []
        for n in range(0, args.pmax - 1):
            for m in range(1, args.mmax + 1):
                target = m * 2**n
                seq = ltv_procedure_a(n, m, finish_clean=True)
                res = verify_schedule(seq, target, require_clean=True)
                claim_p, claim_e = n + 2, m - 1
                if not res["ok"]:
                    print(f"  n={n} m={m}: 不成立 — {res['why']}")
                    rows.append({"src": "LTV-A", "n": n, "m": m, "ok": 0,
                                 "peak": "", "erasures": "", "reached": target,
                                 "moves": len(seq), "claim_p": claim_p, "claim_e": claim_e})
                    continue
                flag = "ok" if (res["peak"] <= claim_p and res["erasures"] <= claim_e) else "主張超過"
                print(
                    f"  n={n} m={m}: 到達 {target:4d}  実測 peak={res['peak']} 消去={res['erasures']} "
                    f"手数={res['moves']:5d}  （主張 p={claim_p} e={claim_e}）[{flag}]"
                )
                rows.append({"src": "LTV-A", "n": n, "m": m, "ok": 1,
                             "peak": res["peak"], "erasures": res["erasures"],
                             "reached": target, "moves": res["moves"],
                             "claim_p": claim_p, "claim_e": claim_e})

        print("\n== 同じ (peak, 消去) で我々の構成が到達する長さ ==")
        print(f"  {'p':>3} {'e':>3} | {'LTV-A 到達':>10} | {'我々 到達':>10} | {'比':>6} | {'差':>8}")
        cmp_rows = []
        for p in range(2, args.pmax + 1):
            for e in range(0, args.mmax):
                n, m = p - 2, e + 1
                ltv_target = m * 2**n
                ltv_seq = ltv_procedure_a(n, m, finish_clean=True)
                ltv_res = verify_schedule(ltv_seq, ltv_target, require_clean=True)
                if not ltv_res["ok"] or ltv_res["peak"] > p or ltv_res["erasures"] > e:
                    ltv_len = None
                else:
                    ltv_len = ltv_target
                ours_len = (e + 2) * 2 ** (p - 2)
                ours_seq = R.construction(p, e)
                ours_res = R.simulate(ours_len, p, ours_seq)
                assert ours_res[0], f"我々の構成が壊れている: p={p} e={e} {ours_res[1]}"
                ratio = f"{ours_len/ltv_len:.2f}x" if ltv_len else "-"
                diff = f"+{ours_len-ltv_len}" if ltv_len else "-"
                print(f"  {p:>3} {e:>3} | {str(ltv_len):>10} | {ours_len:>10} | {ratio:>6} | {diff:>8}")
                cmp_rows.append({"p": p, "e": e, "ltv_a_reach": ltv_len if ltv_len else "",
                                 "ours_reach": ours_len,
                                 "ratio": f"{ours_len/ltv_len:.4f}" if ltv_len else "",
                                 "diff": ours_len - ltv_len if ltv_len else "",
                                 "block_2_p_minus_2": 2 ** (p - 2)})
        with (DATA / "exp03_ltv_compare.csv").open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=["src", "n", "m", "ok", "peak", "erasures",
                                               "reached", "moves", "claim_p", "claim_e"])
            w.writeheader()
            w.writerows(rows)
        with (DATA / "exp03_ltv_vs_ours.csv").open("w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=["p", "e", "ltv_a_reach", "ours_reach",
                                               "ratio", "diff", "block_2_p_minus_2"])
            w.writeheader()
            w.writerows(cmp_rows)
        print("\n  -> data/exp03_ltv_compare.csv, data/exp03_ltv_vs_ours.csv")
        return 0

    print("--compare か --nonclean P を指定してください")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
