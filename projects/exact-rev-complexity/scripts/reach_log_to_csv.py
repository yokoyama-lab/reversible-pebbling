"""`exp03_reach_dag.py` の実行ログから CSV を復元する（**救出用**）。

    python3 scripts/reach_log_to_csv.py --family pyramid --log run.log \\
            --out /abs/path/data/reach_pyramid.csv

## なぜ要るか

`exp03_reach_dag.py` は 2026-08-10 まで**結果を最後に 1 回しか書いていなかった**。
そのため時間切れ・OOM・Ctrl-C で、それまでに確定した升が丸ごと消えた
（実例: `<host>` の pyramid が約 1.5 時間走って CSV が空のまま）。
本体は追記式に直したが、**それ以前に起動して現在も走っているジョブ**は
古い挙動のままなので、標準出力のログから CSV を組み立て直せるようにしておく。

ログ側は各升を確定するたびに `flush=True` で 1 行出しているので、
**途中で殺されてもそこまでは必ず残っている**。

## 何を読むか

```
  p=7 e=3: reach=     6  [exact] 49.9s
  p=8 e=4: reach=UNKNOWN  [UNKNOWN] 12.0s  mem_cap: 訪問表 ... > 上限 ...
```

`[exact]` と `[UNKNOWN]` を区別して落とす。**`UNKNOWN` を空欄や不可解と混ぜない。**
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

ROW = re.compile(
    r"^\s*p=(?P<p>\d+)\s+e=(?P<e>\d+):\s*reach=\s*(?P<val>\S+)\s+\[(?P<status>\w+)\]"
    r"(?:\s+[\d.]+s)?(?P<reason>.*)$"
)


def parse(text: str) -> list[tuple[int, int, str, str, str]]:
    out: list[tuple[int, int, str, str, str]] = []
    for line in text.splitlines():
        m = ROW.match(line)
        if not m:
            continue
        status = m.group("status")
        val = m.group("val")
        if status == "exact":
            if not val.isdigit():
                continue
        else:
            val = ""
        reason = m.group("reason").strip()
        out.append((int(m.group("p")), int(m.group("e")), val, status, reason))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", required=True)
    ap.add_argument("--log", required=True, help="- で標準入力")
    ap.add_argument("--out", required=True, help="絶対パス推奨（相対はリポジトリルート基準）")
    args = ap.parse_args()

    text = sys.stdin.read() if args.log == "-" else Path(args.log).read_text(
        encoding="utf-8", errors="replace")
    rows = parse(text)
    if not rows:
        print("復元できる行が無い（ログの形式を確認すること）")
        return 1
    # 同じ (p,e) が複数回出たら最後を採る（再実行の上書き）
    latest: dict[tuple[int, int], tuple[int, int, str, str, str]] = {}
    for r in rows:
        latest[(r[0], r[1])] = r

    out_path = Path(args.out)
    if not out_path.is_absolute():
        out_path = ROOT / out_path
    out_path.parent.mkdir(parents=True, exist_ok=True)
    lines = ["family,p,e,reach,status,reason"]
    for (p, e) in sorted(latest):
        _p, _e, val, status, reason = latest[(p, e)]
        lines.append(f"{args.family},{p},{e},{val},{status},\"{reason}\"")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    n_exact = sum(1 for v in latest.values() if v[3] == "exact")
    print(f"-> {out_path}  {len(latest)} 升（exact {n_exact} / UNKNOWN {len(latest)-n_exact}）")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
