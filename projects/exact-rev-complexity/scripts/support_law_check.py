"""予想 G（フロンティア支持法則）を data/tight_support/*.json の全数で機械検査する。

予想 G（p ≥ 3。c_u = (u+2)·2^{p-2}, τ_u = c_u + 2^{p-1} - 1）:
  ちょうど u 回消去済みの到達状態（層 u）について
  (i)   フロンティア f の状態が存在する ⟺ 1 ≤ f ≤ min(τ_u, n)
  (ii)  f ≤ c_u なら最小支持 = 0（クリーン {f} が層 u に存在）
  (iii) c_u < f ≤ τ_u なら最小支持 = f - G(u,f) で
        G(u,f) = max( 3·2^{p-3}·[u≥1 かつ f-c_u ≤ 2^{p-3}],
                      2^⌊log2(c_u + 2^{p-1} - f)⌋ )
  （p=2 は縮退: 合流帯なし・倍々部のみで同式が成り立つ）

系（予想 B2）: n = c_e+1 では
  - u ≤ e-2 の層に f=n の状態は無い（n > τ_u ⟺ e-u ≥ 2）
  - u ∈ {e-1, e} では最小支持 ≥ n - 3·2^{p-3} ≥ 1 > 0
  よって「節点 n のみ」（支持 0）はどの層でも到達不能 = clean 到達不能。

このスクリプトは支持法則そのもの（機械が見つけた形の一般化）を、保存済みの
全インスタンス（掃引 n=claim+1 と、鎖長 τ_e までの拡張走行）に対して照合する。
1 点でも外れれば反例として報告する（予想は棄却・修正）。

    python3 scripts/support_law_check.py
"""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data" / "tight_support"


def g_pred(p: int, u: int, f: int) -> int | None:
    """層 u・フロンティア f の最大許容ギャップ（存在しないなら None）。"""
    c_u = (u + 2) << (p - 2)
    tau_u = c_u + (1 << (p - 1)) - 1
    if f > tau_u:
        return None
    if f <= c_u:
        return f  # 支持 0（クリーン {f}）= ギャップ f
    g = 1 << ((c_u + (1 << (p - 1)) - f).bit_length() - 1)  # 2^floor(log2)
    if p >= 3 and u >= 1 and f - c_u <= (1 << (p - 3)):
        g = max(g, 3 << (p - 3))
    return g


def expected_umin_single(m: int, p: int) -> int:
    num = m - (1 << (p - 1))
    den = 1 << (p - 2)
    return max(0, -(-num // den))


def check_file(path: Path) -> list[str]:
    s = json.loads(path.read_text())
    p, e, n = s["p"], s["e"], s["n"]
    errs: list[str] = []

    # 0) 到達の階段（u_min({m}) の公式）
    for m_str, u in s["staircase"].items():
        m = int(m_str)
        exp = expected_umin_single(m, p)
        exp_v = exp if exp <= e else None
        if u != exp_v:
            errs.append(f"階段: u_min({{{m}}}) = {u} ≠ 期待 {exp_v}")

    # 1)-(iii) フロンティア法則
    for u in range(e + 1):
        tbl = s["minsupp_by_u"].get(str(u), {})
        c_u = (u + 2) << (p - 2)
        tau_u = c_u + (1 << (p - 1)) - 1
        for f in range(1, n + 1):
            obs = tbl.get(str(f))
            pred = g_pred(p, u, f)
            if pred is None or f > n:
                if obs is not None:
                    errs.append(f"存在: u={u} f={f} は τ_u={tau_u} 超なのに状態あり")
                continue
            if obs is None:
                errs.append(f"存在: u={u} f={f} ≤ min(τ_u={tau_u},n) なのに状態なし")
                continue
            s_obs = obs["s"]
            s_pred = 0 if f <= c_u else f - pred
            if s_obs != s_pred:
                errs.append(
                    f"支持: u={u} f={f} 最小支持 {s_obs} ≠ 期待 {s_pred}"
                    f"（G_pred={pred}, witness={obs['witness']}）"
                )
    return errs


def main() -> int:
    files = sorted(DATA.glob("p*e*n*.json"))
    if not files:
        print("data/tight_support/*.json が無い（先に support_truth.py --sweep）")
        return 1
    total_err = 0
    total_pts = 0
    for path in files:
        s = json.loads(path.read_text())
        pts = sum(len(v) for v in s["minsupp_by_u"].values()) + len(s["staircase"])
        errs = check_file(path)
        total_pts += pts
        total_err += len(errs)
        mark = "ok  " if not errs else "FAIL"
        print(f"  {mark} {path.name:<16} 照合 {pts:>5} 点  反例 {len(errs)}")
        for msg in errs[:10]:
            print(f"        {msg}")
        if len(errs) > 10:
            print(f"        …ほか {len(errs)-10} 件")
    print()
    if total_err:
        print(f"予想 G: 反例 {total_err} 件 / 照合 {total_pts} 点 → 棄却・要修正")
        return 1
    print(f"予想 G: 反例 0 件（{len(files)} ファイル・照合 {total_pts} 点で全数一致）")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
