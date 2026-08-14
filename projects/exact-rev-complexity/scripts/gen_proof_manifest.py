"""永続化した SAT 証明ログのマニフェストを生成する（2026-08-10）。

## なぜマニフェストだけをリポジトリに置くか

証明ログ本体（CNF + DRAT）は 5.7MB あり、`.gitignore` の `data/families/sat_work/` が
示すとおり **SAT の作業成果物は git に入れない**のがこのリポジトリの規約。
一方で「下界を証明ログ付きで確認した」という主張は、**どのファイルがどこにあり、
検査が通ったか**を残さないと後から確かめられない。

→ **本体は /work に zstd で永続化し、マニフェスト（一覧・SHA256・検査結果・再生成手順）
だけをリポジトリに置く。**

## 使い方

    .venv/bin/python scripts/gen_proof_manifest.py > data/sat_proof_manifest.md
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

STORE = Path("<local>/proofs/exact-rev-complexity/2026-08-10-sat")


def verify(stem: str) -> tuple[str, float]:
    """zst を展開して drat-trim に掛け、判定行と秒を返す。"""
    import tempfile
    import time

    with tempfile.TemporaryDirectory() as td:
        cnf, drat = Path(td) / "a.cnf", Path(td) / "a.drat"
        for src, dst in ((f"{stem}.cnf.zst", cnf), (f"{stem}.drat.zst", drat)):
            p = STORE / src
            if not p.exists():
                return ("（ファイル欠落）", 0.0)
            dst.write_bytes(subprocess.run(
                ["zstd", "-dq", "-c", str(p)], capture_output=True, check=True).stdout)
        t0 = time.time()
        r = subprocess.run(["drat-trim", str(cnf), str(drat)],
                           capture_output=True, text=True, timeout=900)
        dt = time.time() - t0
        m = re.search(r"^s (VERIFIED|NOT VERIFIED)", r.stdout, re.M)
        return (m.group(0) if m else "（判定行なし）", dt)


def main() -> int:
    if not STORE.exists():
        print(f"永続化先が無い: {STORE}", file=sys.stderr)
        return 1

    stems = sorted({p.name.split(".")[0] for p in STORE.glob("*.cnf.zst")})
    total = sum(p.stat().st_size for p in STORE.glob("*.zst"))

    print("# SAT 証明ログのマニフェスト（2026-08-10）\n")
    print("`data/sat_findings.md` の下界の主張を裏づける証明ログの所在と検査結果。")
    print("**本体はリポジトリに入っていない**（`.gitignore` の `data/families/sat_work/` と")
    print("同じ方針。5.7MB あるため）。\n")
    print(f"- 永続化先: `{STORE}`（zstd 圧縮、計 {total/1024/1024:.1f} MB）")
    print("- チェックサム: 同ディレクトリの `SHA256SUMS`")
    print("- 検査器: `drat-trim`（`~/dev/TOOLS.md`）\n")
    print("## 検査結果\n")
    print("**`k = M*` の行が `NOT VERIFIED` になるのは正しい。**")
    print("そちらは充足可能で空節が無く、検証すべき UNSAT 証明が存在しないため。")
    print("逆にここが VERIFIED なら符号化が壊れている。\n")
    print("| インスタンス | 判定 | 検査秒 | 意味 |")
    print("|---|---|---:|---|")

    ok = ng = 0
    for stem in stems:
        res, dt = verify(stem)
        meaning = ("**下界**: この手数では不可能" if res == "s VERIFIED"
                   else "上界側（充足可能）。UNSAT 証明は無い")
        if res == "s VERIFIED":
            ok += 1
        else:
            ng += 1
        print(f"| `{stem}` | {res} | {dt:.2f} | {meaning} |")

    print(f"\n**VERIFIED {ok} 件 / NOT VERIFIED {ng} 件。**")
    print("後者はすべて `k = M*`（充足可能）であることを確認すること。\n")
    print("## 再生成\n")
    print("```sh")
    print(".venv/bin/python scripts/sat_pebble.py      # CNF と DRAT を作り直す")
    print(".venv/bin/python scripts/gen_proof_manifest.py > data/sat_proof_manifest.md")
    print("```")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
