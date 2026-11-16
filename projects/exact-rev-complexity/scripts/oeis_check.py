"""`data/sequences_index.md` の `exact` な数列を OEIS に照合する（**読み取りのみ**）。

出力: `data/oeis_matches.md`、キャッシュ `data/oeis_cache.json`

## 健全性（これが無いと結果を信用してはいけない）

OEIS の JSON API は

- ヒットあり → JSON 配列
- ヒットなし → `null`（HTTP 200）
- 過負荷・遮断 → 非 200 か JSON でない本文

を返す。**429 や HTML を「0 件」と読むと、既知の数列を『新規』と誤判定する**
（`~/.claude` の記憶 `api-error-parsed-as-zero-hits`）。そこで:

1. **健全性チェック**: 存在確実な数列（Fibonacci）を、開始時・10 件ごと・終了時に問い合わせ、
   ヒットが返ることを確認する。返らなければ**その時点で中断**し、結果を破棄する。
2. 非 200 / JSON でない本文は `error` として記録し、**「未登録」とは書かない**。
3. 問い合わせ間隔を空ける（既定 2 秒）。OEIS への礼儀であり、遮断の予防でもある。

**書き込みは一切しない。**

    python3 scripts/oeis_check.py               # キャッシュを使い、未取得のものだけ問い合わせ
    python3 scripts/oeis_check.py --refresh     # キャッシュを無視して取り直す
    python3 scripts/oeis_check.py --dry-run     # 問い合わせずキャッシュの内容だけ表示
"""

from __future__ import annotations

import argparse
import json
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from sequences_index import exact_sequences  # noqa: E402

CACHE = ROOT / "data" / "oeis_cache.json"
OUT = ROOT / "data" / "oeis_matches.md"
API = "https://oeis.org/search"
UA = "exact-rev-complexity/1.0 (research; read-only)"

HEALTH_SEQ = [1, 1, 2, 3, 5, 8, 13, 21]
HEALTH_EXPECT = "A000045"


def query(seq: list[int], *, timeout: int = 30) -> dict:
    """OEIS へ 1 回問い合わせる。戻り値の `status` は hit / none / error。"""
    q = ",".join(str(v) for v in seq)
    url = f"{API}?{urllib.parse.urlencode({'q': q, 'fmt': 'json'})}"
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310
            code = resp.status
            body = resp.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as exc:
        return {"status": "error", "detail": f"HTTP {exc.code}"}
    except Exception as exc:  # noqa: BLE001
        return {"status": "error", "detail": f"{type(exc).__name__}: {exc}"}
    if code != 200:
        return {"status": "error", "detail": f"HTTP {code}"}
    body = body.strip()
    if body == "null" or body == "":
        return {"status": "none", "detail": ""}
    try:
        data = json.loads(body)
    except json.JSONDecodeError:
        return {"status": "error", "detail": "JSON でない本文（遮断の可能性）"}
    if data is None:
        return {"status": "none", "detail": ""}
    if not isinstance(data, list):
        return {"status": "error", "detail": f"予期しない型 {type(data).__name__}"}
    hits = []
    for item in data[:8]:
        num = item.get("number")
        raw = (item.get("data") or "")
        try:
            vals = [int(x) for x in raw.split(",") if x.strip()]
        except ValueError:
            vals = []
        hits.append({
            "id": f"A{num:06d}" if isinstance(num, int) else str(num),
            "name": (item.get("name") or "")[:200],
            "data": vals,
        })
    return {"status": "hit", "hits": hits, "n_total": len(data)}


def contains_block(hay: list[int], needle: list[int]) -> bool:
    """OEIS 側の数列 `hay` に、こちらの全項 `needle` が連続部分列として入っているか。"""
    if not needle or len(needle) > len(hay):
        return False
    for i in range(len(hay) - len(needle) + 1):
        if hay[i:i + len(needle)] == needle:
            return True
    return False


def triviality(vals: list[int]) -> str:
    """OEIS ヒットが**情報を持たない**型かどうか。

    等差・等比の数列は OEIS に必ず載っているので、「ヒットした＝既知の結果だ」の
    根拠にならない。ここで印を付けて、台帳への追記候補から外す。
    """
    if len(vals) < 3:
        return ""
    d = [b - a for a, b in zip(vals, vals[1:])]
    if len(set(d)) == 1:
        return f"等差（公差 {d[0]}）"
    if all(v != 0 for v in vals[:-1]):
        q = [b / a for a, b in zip(vals, vals[1:])]
        if len(set(q)) == 1 and float(q[0]).is_integer():
            return f"等比（公比 {int(q[0])}）"
    dd = [b - a for a, b in zip(d, d[1:])]
    if len(set(dd)) == 1:
        return f"2 階差が一定（{dd[0]}）＝ 2 次式"
    return ""


def health_check(delay: float) -> tuple[bool, str]:
    r = query(HEALTH_SEQ)
    time.sleep(delay)
    if r["status"] != "hit":
        return False, f"健全性チェックが hit を返さなかった: {r}"
    ids = [h["id"] for h in r["hits"]]
    if HEALTH_EXPECT not in ids:
        return False, f"健全性チェックの結果に {HEALTH_EXPECT} が無い: {ids}"
    return True, f"ok（{HEALTH_EXPECT} を確認）"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--refresh", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--delay", type=float, default=2.0)
    ap.add_argument("--terms", type=int, default=16, help="問い合わせに使う先頭項数")
    ap.add_argument("--min-terms", type=int, default=5)
    args = ap.parse_args()

    cache: dict = json.loads(CACHE.read_text()) if CACHE.exists() else {}
    seqs = [s for s in exact_sequences() if s.n >= args.min_terms]
    # 同じ値の並びは 1 回だけ問い合わせる
    todo: dict[str, list[int]] = {}
    for s in seqs:
        probe = s.values[:args.terms]
        todo.setdefault(",".join(map(str, probe)), probe)

    if not args.dry_run:
        ok, msg = health_check(args.delay)
        print(f"健全性チェック(開始): {msg}")
        if not ok:
            print("→ 中断する。結果は書かない。", file=sys.stderr)
            return 1
        n = 0
        def stale(entry: dict) -> bool:
            """古い形式（hits に `data` が無い）は再取得する。
            これを入れないと、全項照合が常に失敗して『別物』と誤判定する。"""
            if entry.get("status") == "error":
                return True
            if entry.get("status") == "hit":
                return any("data" not in h for h in entry.get("hits", []))
            return False

        for key, probe in todo.items():
            if key in cache and not args.refresh and not stale(cache[key]):
                continue
            r = query(probe)
            if r["status"] == "error":         # 1 度だけ再試行
                time.sleep(args.delay * 3)
                r = query(probe)
            cache[key] = r
            n += 1
            print(f"  [{n}] {key[:48]:48s} → {r['status']}")
            time.sleep(args.delay)
            if n % 10 == 0:
                ok, msg = health_check(args.delay)
                if not ok:
                    print(f"→ 途中の健全性チェックが失敗: {msg}。ここで中断する。",
                          file=sys.stderr)
                    CACHE.write_text(json.dumps(cache, ensure_ascii=False, indent=1))
                    return 1
        ok, msg = health_check(args.delay)
        print(f"健全性チェック(終了): {msg}")
        if not ok:
            print("→ 終了時のチェックが失敗。結果を疑うこと。", file=sys.stderr)
            CACHE.write_text(json.dumps(cache, ensure_ascii=False, indent=1))
            return 1
        CACHE.write_text(json.dumps(cache, ensure_ascii=False, indent=1))

    # 出力
    L = ["# OEIS 照合の結果（自動生成・手編集禁止）", "",
         "生成: `python3 scripts/oeis_check.py`（**読み取りのみ**）", "",
         "**読み方**: `error` は「未登録」ではない。問い合わせが失敗しただけなので、"
         "取り直すまで何も言えない。`none` だけが「OEIS に無い」を意味する。", ""]
    counts = {"verified": 0, "partial": 0, "none": 0, "error": 0, "未取得": 0}
    rows = []
    for s in sorted(seqs, key=lambda x: (-x.n, x.key)):
        key = ",".join(map(str, s.values[:args.terms]))
        r = cache.get(key)
        st = r["status"] if r else "未取得"
        detail = ""
        if r and st == "hit":
            verified = [h for h in r["hits"]
                        if contains_block(h.get("data", []), s.values)]
            if verified:
                st = "verified"
                detail = "; ".join(f"[{h['id']}] {h['name'][:70]}" for h in verified[:2])
            else:
                st = "partial"
                detail = ("先頭 %d 項だけ一致し、全 %d 項では一致しなかった: "
                          % (min(args.terms, s.n), s.n)) + "; ".join(
                    f"[{h['id']}]" for h in r["hits"][:3])
        elif r and st == "error":
            detail = r.get("detail", "")
        rows.append((s, st, detail))
        counts[st] = counts.get(st, 0) + 1
    L.append("**要約**: " + " / ".join(f"{k} {v}" for k, v in counts.items() if v))
    # 制御: 閉形式が確定している reach(p,0)=2^{p-1} は A000079 に全項一致するはず
    ctrl = [(s, st) for s, st, _ in rows if s.key == "reach:e0"]
    if ctrl:
        _, cst = ctrl[0]
        L += ["", f"**制御列の自己検査**: `reach:e0`（$2^{{p-1}}$、閉形式が確定済み）の判定は "
              f"**{cst}**。ここが `verified` でなければ照合系が壊れている。"]
    L += ["", "| key | 数列 | 項数 | 判定 | OEIS |", "|---|---|---:|---|---|"]
    for s, st, detail in rows:
        mark = {"verified": "**既知（全項一致）**", "partial": "先頭のみ一致→別物",
                "none": "未登録", "error": "⚠ 取得失敗", "未取得": "—"}[st]
        L.append(f"| `{s.key}` | {s.title} | {s.n} | {mark} | {detail} |")
    L += ["", "## 全項一致したもの（既知として早期棄却の材料にする）", "",
          "**信頼度の読み方**: 「全項一致」は*こちらの全項が OEIS 側の数列の連続部分に現れる*"
          "という意味であって、同じ数列だという証明ではない。項数が少ないほど偶然の一致が増える:",
          "",
          "- 10 項以上 … **強**（偶然はまず無い）",
          "- 7〜9 項 … 中（別系列の可能性が残る）",
          "- 6 項以下 … **弱**（短い並びは多くの数列に現れる。棄却の根拠にしてよいが、"
          "『同じ数列だ』と書いてはいけない）", ""]
    any_hit = False
    for s, st, detail in rows:
        if st == "verified":
            any_hit = True
            conf = "強" if s.n >= 10 else ("中" if s.n >= 7 else "**弱**")
            triv = triviality(s.values)
            tmark = (f"、**自明な型: {triv} → OEIS ヒットは既知性の根拠にならない**"
                     if triv else "")
            L.append(f"- **{s.title}**（`{s.key}`, {s.n} 項 → 信頼度 {conf}{tmark}, "
                     f"出典 `{s.source}`）")
            L.append(f"  - 先頭: `{s.values[:args.terms]}`")
            L.append(f"  - {detail}")
    if not any_hit:
        L.append("（なし）")
    L += ["", "## 先頭だけ一致したもの（**別物**。当てはめ崩壊の実例として記録）", ""]
    any_p = False
    for s, st, detail in rows:
        if st == "partial":
            any_p = True
            L.append(f"- **{s.title}**（`{s.key}`, {s.n} 項）: {detail}")
    if not any_p:
        L.append("（なし）")
    # --- docs/22_known_facts_ledger.md との突き合わせ -------------------------
    ledger = ROOT / "docs" / "22_known_facts_ledger.md"
    L += ["", "## 既知事実台帳との突き合わせ", "",
          "OEIS に載っている＝**既に知られている**なので、早期棄却の材料になる。",
          "`docs/22_known_facts_ledger.md` に該当項目があるかを機械的に照合した",
          "（A 番号の文字列一致。**台帳は書き換えていない**——追記は人間の判断）。", "",
          "⚠ **照合は A 番号の文字列一致だけ**なので、台帳が『概念として』記載していても"
          "A 番号を書いていなければ「記載なし」と出る。実例: `reach:e*` は"
          "台帳 KF-03（$\\mathrm{reach}(p)=2^{p-1}$、Královič 2001）が該当するが、"
          "A 番号が書かれていないので下では「記載なし」になっている。"
          "**この一覧を根拠に台帳へ追記してはいけない。**", ""]
    if not ledger.exists():
        L.append("（台帳が見つからない）")
    else:
        text = ledger.read_text()
        anys = False
        for s_, st, _detail in rows:
            if st != "verified":
                continue
            r = cache.get(",".join(map(str, s_.values[:args.terms])), {})
            ids = [h["id"] for h in r.get("hits", [])
                   if contains_block(h.get("data", []), s_.values)]
            if not ids:
                continue
            anys = True
            listed = [i for i in ids if i in text]
            conf = "強" if s_.n >= 10 else ("中" if s_.n >= 7 else "弱")
            triv = triviality(s_.values)
            if triv:
                L.append(f"- `{s_.key}`: **{triv}** なので OEIS に載っているのは当然。"
                         f"{ids[:2]} は**台帳に足す対象ではない**")
                continue
            if listed:
                L.append(f"- `{s_.key}`（信頼度 {conf}）: {listed} は**台帳に記載あり**")
            else:
                L.append(f"- `{s_.key}`（信頼度 {conf}）: {ids[:3]} は台帳に**記載なし**"
                         + ("。ただし項数が少なく偶然の一致でありうるので、"
                            "台帳に足す前に一次情報で確かめること" if s_.n < 7 else
                            "。台帳への追記を検討する価値がある"))
        if not anys:
            L.append("（全項一致したものが無いので照合対象なし）")
    L.append("")
    OUT.write_text("\n".join(L) + "\n")
    print("\n".join(L[:6]))
    print(f"→ {OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
