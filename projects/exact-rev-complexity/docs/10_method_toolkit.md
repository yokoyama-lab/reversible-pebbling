# 10 — 共通手順とツールキット

どの候補でも同じパイプラインを回す。**手計算・手証明に入る前に機械化を検討する**
（`~/dev/CLAUDE.md` の「証明・計算の方針」に従う）。

## パイプライン

```
(0) 文献の一次確認 → (1) 厳密全数計算 → (2) 二重実装で照合 → (3) OEIS 照合
  → (4) 閉形式/漸化式の推定 → (5) Lean 二層検証 → (6) 表の自動生成 → (7) 執筆
```

### (0) 文献の一次確認

- Semantic Scholar（キーは `~/.env` の `S2_API_KEY`。無認証は 429 で使えない）:
  ```bash
  set -a; . ~/.env; set +a
  curl -s -H "x-api-key: $S2_API_KEY" -G \
    "https://api.semanticscholar.org/graph/v1/paper/search" \
    --data-urlencode "query=<TITLE>" \
    --data-urlencode "fields=title,authors,year,venue,externalIds" --data-urlencode "limit=5"
  ```
- **前方引用も必ず辿る**（`/paper/{id}/citations`）。後発が同じ量を再発明していることがある。
- 決定的な主張は**必ず本文 PDF を読む**。アブストラクトだけで「既知」「未知」を判定しない。
- Crossref はタイトル完全一致のみ採用。arXiv は `https://export.arxiv.org/api/query?id_list=<ID>`（https 必須）。
  正式出版版があれば arXiv ではなく出版版を引く。

### (1) 厳密全数計算

- 状態空間探索は **BFS（最短手数）** が既定。状態は `frozenset` / ビットマスク。
- 探索が爆発したら順に: ①同型除去（nauty / 自作正規形） ②再帰式への置換
  ③区間代数（値ベクトルを厳密整数で持ち、漸近順序オラクルで比較） ④分枝限定。
- **計算可能域の上限まで回す**。「n≤8 で成立」は予想の根拠に弱い。先行例では
  p=10 まで回して初めて予想が偽だと分かった。

### (2) 二重実装で照合

素朴実装（正しさが自明）と高速実装（再帰式・DP）を**両方**書き、重なる範囲で一致を確認する。
一致しない範囲は公表しない。これが査読での唯一の防具。

### (3) OEIS 照合

```bash
curl -s "https://oeis.org/search?q=1,3,5,9,11,15,19,25&fmt=json" | head -c 2000
```
- API の健全性を既知列（Fibonacci 等）で先に確認する（無応答と未登録を区別するため）。
- 未登録なら**新規性の即時証拠**。登録申請も小さな成果になる。

### (4) 閉形式・漸化式の推定

- **Newton 差分**: 差分列を取って多項式次数を判定（外部 CAS 不要。整数のまま扱う）。
- 差分に周期構造があれば「$n$ の 2 進表現に依存する式」を疑う（可逆計算では頻出）。
- 比 $a_{n+1}/a_n$ が定数に近づけば指数型、$a_n/n^c$ を試して $c$ を推定。
- 推定式は**必ず計算域の外側で1点以上検証**してから採用する。

### (5) Lean 二層検証

二層を明確に分けて manifest に書く。混ぜると「何が証明されたのか」が曖昧になる。

| 層 | 内容 | 手法 |
|---|---|---|
| L1: 一般証明 | 無条件の定理（到達可能性の特徴付け、下界の不変量） | 通常の証明項 |
| L2: 有界全数検査 | 「$n \le N$ について表の値が正しい」 | `decide` / `native_decide` |

- 既存資産: `~/dev/github.com/tetsuo-jp/gen_janus/260612/formal/GenJanus/Hard18.lean`
  に `mstar_table` / `pmin_table` の L2 検証がある。**まずこれを写して形を真似る。**
- `native_decide` は信頼境界が広がる（コンパイラを信じる）ので、論文では明記する。
- ビルドは `lake build`（`~/dev/.claude/settings.json` で allowlist 済み）。
  エラー時はまず `.vo`/`.olean` の陳腐化と opam/elan スイッチを疑う。

### (6) 表の自動生成

- `data/*.csv` をスクリプトから生成し、LaTeX 表も生成物にする（**手編集禁止**とファイル冒頭に書く）。
- 先行例: `scripts/pebble_data.py → tables/mstar.tex`。

### (7) 執筆

- 論文本体は Overleaf 側（`~/dev/overleaf/2026_*`）。本リポジトリには計算とメモのみ。
- 投稿先の既定候補: **RC**（Reversible Computation, 本命）、**TCS / IPL**（理論寄り）、
  **CPP / ITP**（形式化を主張にする場合）、国内は **PPL / JSSST / IEICE**。
- 論文には必ず「何を機械が検証し、何を人間が証明したか」の manifest 節を置く。

## リポジトリ規約

- **テストファースト**: 新しい定義・関数を入れるときは先に `tests/` へ期待値を書く。
- 厳密値を `tests/` に固定したら、以後エンジン改造の回帰検出に使う。
- 重い実験は `data/` へ結果をキャッシュし、スクリプトは再実行で同じ数を出すこと（乱数を使わない）。
