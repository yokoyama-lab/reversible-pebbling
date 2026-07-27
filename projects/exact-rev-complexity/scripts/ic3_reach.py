"""到達則の**上界**（定理 B2 の等号）を IC3/PDR で証明する。

## 何を示したいか

定理 B1（証明済み）は下界 $\\mathrm{reach}(p,e) \\ge (e+2)2^{p-2}$。
**残る予想 B2 は等号**、すなわち

$$\\text{ピーク} \\le p,\\ \\text{消去} \\le e \\ \\text{では } n = (e+2)2^{p-2}+1 \\text{ に clean 到達できない}$$

これは**不到達性**の主張であり、`docs/31_tool_import.md` §8.3・§10.4 の原則:

> 下界側（存在しないことを示す）は成熟した道具が必須。
> IC3/PDR は**到達不可能性を証明する帰納的不変量を自動構成する**。

IC3 が出す不変量は、**人間が一般 $n$ の証明に育てる素材**になる（機械が見つけ、人間が一般化する）。

## SMV への符号化

- 状態: `x1..xN`（各節点のペブル）＋ `cnt`（使用済み不可逆消去数, 0..e）
- 入力（非決定的）: `sel`（操作する節点）, `act`（put/take）
- `avail(i)` = 節点 $i-1$ がペブル済み（$i=1$ は常に可用。節点 0 は常時可用な源）
- `put` は `avail` と「ペブル数 < p」を要求。`take` は `avail` なら無償、
  さもなくば `cnt < e` を要求して `cnt` を増やす
- **INVARSPEC**: 「節点 N のみがペブル済み」という状態に**到達しない**

使い方:
    python3 scripts/ic3_reach.py --p 3 --e 0            # 既知値で符号化を検証
    python3 scripts/ic3_reach.py --p 4 --e 1 --engine abc
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path

NUXMV = Path.home() / "dev/infra/tools/nuXmv"
NUXMV_LIBS = Path.home() / "dev/infra/tools/nuxmv-libs"


def smv_model(n: int, p: int, e: int) -> str:
    """鎖 $0..n$（節点 0 は常時可用な源）の $e$-消去ペブリングを SMV で書く。"""
    xs = [f"x{i}" for i in range(1, n + 1)]
    lines = ["MODULE main", "VAR"]
    for x in xs:
        lines.append(f"  {x} : boolean;")
    if e > 0:
        lines.append(f"  cnt : 0..{e};")
    lines.append("IVAR")
    lines.append(f"  sel : 1..{n};")
    lines.append("  act : boolean;   -- TRUE = put, FALSE = take")
    lines.append("DEFINE")
    lines.append("  npeb := count(" + ", ".join(xs) + ");")
    for i in range(1, n + 1):
        av = "TRUE" if i == 1 else f"x{i - 1}"
        lines.append(f"  av{i} := {av};")
    # 実行可能性
    for i in range(1, n + 1):
        lines.append(
            f"  can_put{i} := !x{i} & av{i} & npeb < {p};"
        )
        if e > 0:
            lines.append(f"  can_take{i} := x{i} & (av{i} | cnt < {e});")
            lines.append(f"  irr{i} := x{i} & !av{i};")
        else:
            lines.append(f"  can_take{i} := x{i} & av{i};")
    lines.append("ASSIGN")
    for i in range(1, n + 1):
        lines.append(f"  init(x{i}) := FALSE;")
    if e > 0:
        lines.append("  init(cnt) := 0;")
    # 遷移
    for i in range(1, n + 1):
        lines.append(f"  next(x{i}) := case")
        lines.append(f"    sel = {i} & act & can_put{i} : TRUE;")
        lines.append(f"    sel = {i} & !act & can_take{i} : FALSE;")
        lines.append(f"    TRUE : x{i};")
        lines.append("  esac;")
    if e > 0:
        lines.append("  next(cnt) := case")
        clauses = " | ".join(
            f"(sel = {i} & !act & can_take{i} & irr{i})" for i in range(1, n + 1)
        )
        lines.append(f"    ({clauses}) & cnt < {e} : cnt + 1;")
        lines.append("    TRUE : cnt;")
        lines.append("  esac;")
    # 目標: 節点 n のみがペブル済み
    others = [f"!x{i}" for i in range(1, n)]
    goal = f"x{n}" + ("" if not others else " & " + " & ".join(others))
    lines.append(f"INVARSPEC !({goal});")
    return "\n".join(lines) + "\n"


def run_nuxmv(path: Path, *, timeout: float = 600.0) -> tuple[str, str]:
    """nuXmv の IC3（SMT ベース）で INVARSPEC を検査する。"""
    if not NUXMV.exists():
        return ("SKIP", "nuXmv が無い（docs/33_install_notes.md §1）")
    cmds = "\n".join(
        [f"read_model -i {path}", "go_msat", "check_invar_ic3", "quit", ""]
    )
    env = dict(os.environ, LD_LIBRARY_PATH=str(NUXMV_LIBS))
    out = subprocess.run(
        [str(NUXMV), "-int"],
        input=cmds,
        capture_output=True,
        text=True,
        timeout=timeout,
        env=env,
    )
    txt = out.stdout + out.stderr
    if "is false" in txt:
        return ("REACHABLE", txt)
    if "is true" in txt:
        return ("UNREACHABLE", txt)
    return ("UNKNOWN", txt[-2000:])


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--p", type=int, required=True)
    ap.add_argument("--e", type=int, default=0)
    ap.add_argument("--n", type=int, default=None, help="省略時は予想値と +1 の両方を試す")
    ap.add_argument("--timeout", type=float, default=600.0)
    ap.add_argument(
        "--workdir", type=Path, default=Path("/tmp/claude-1000/-work-a-dev/ic3")
    )
    args = ap.parse_args()

    args.workdir.mkdir(parents=True, exist_ok=True)
    claim = (args.e + 2) * 2 ** (args.p - 2)
    ns = [args.n] if args.n else [claim, claim + 1]
    print(f"予想 B2: reach(p={args.p}, e={args.e}) = (e+2)2^(p-2) = {claim}")
    for n in ns:
        f = args.workdir / f"chain_p{args.p}_e{args.e}_n{n}.smv"
        f.write_text(smv_model(n, args.p, args.e))
        verdict, _ = run_nuxmv(f, timeout=args.timeout)
        expect = "REACHABLE" if n <= claim else "UNREACHABLE"
        mark = "○" if verdict == expect else ("—" if verdict in ("UNKNOWN", "SKIP") else "**×**")
        print(f"  n={n:>4}: {verdict:<12} 期待 {expect:<12} {mark}")


if __name__ == "__main__":
    main()
