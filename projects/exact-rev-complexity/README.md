# exact-rev-complexity — 可逆計算の「厳密値」探究ラボ

可逆計算まわりの量を **漸近ではなく厳密整数値で決める**ための研究候補集と、
その探究をゼロから始めるための最小実行環境。

先行例: `~/dev/overleaf/2026_exact_reversible_pebbling`
（reversible pebbling game の厳密最小手数 $M^*(n,p)$ を BFS + 区間代数 + Lean で確定し、
Pesu–Phillips 2015 の族が Knill 1995 の厳密値に劣ることを示した）。
本リポジトリは**同じ勝ちパターンを他のトピックへ移植する**ための出発点である。

## まず読む順番

1. [`docs/00_overview.md`](docs/00_overview.md) — 勝ちパターンの定義、候補10件の一覧と優先順位
2. [`docs/10_method_toolkit.md`](docs/10_method_toolkit.md) — 共通手順（全数探索 → OEIS 照合 → 閉形式推定 → Lean 二層検証 → 執筆）
3. [`docs/20_prior_art.md`](docs/20_prior_art.md) — 先行プロジェクトで確定した既知事実（ここを知らずに始めると再発明する）
4. [`docs/idea01_trees_dags.md`](docs/idea01_trees_dags.md) 以降 — 候補ごとの独立した実行計画

各アイデア md は**単独で読めば着手できる**ように書いてある（定義・既知文献・機械化設計・
初日の実験コマンド・成功判定・撤退条件・Lean 計画・投稿先）。

## いますぐ動くもの

```bash
cd ~/dev/github.com/tetsuo-jp/exact-rev-complexity
python3 tests/test_revpebble.py     # 回帰テスト（先行プロジェクトの厳密値を再現）
python3 scripts/revpebble.py        # 鎖・完全二分木の厳密値をその場で計算
python3 scripts/exp01_trees.py      # 候補1の初日実験（木族の p_min と M* 表）
```

`scripts/revpebble.py` は **DAG 一般**の可逆ペブリング BFS エンジン。
鎖（Bennett のゲーム）で先行プロジェクトの数値
（`reach(p)=2^{p-1}`、`M*(n)=1,3,5,9,11,15,19,25,25,29,33,39,45,53,61,71`）を
再現することがテストで固定されている。候補 1・2・3・4 はこのエンジンの拡張で走る。

## ディレクトリ

| パス | 中身 |
|---|---|
| `docs/` | 研究計画（本体）。`00`→`10`→`20`→`ideaNN` の順に読む |
| `scripts/` | 計算エンジンと各候補の実験スクリプト |
| `tests/` | 回帰テスト。**新しい定義を入れる前にここへテストを足す**（テストファースト） |
| `data/` | 実験で出た厳密値の表（CSV/JSON、スクリプトから自動生成・手編集禁止） |

## 方針

- 論文ドラフトは Overleaf 側（`~/dev/overleaf/2026_*`）に置き、本リポジトリには計算とメモだけを置く。
- 厳密値は必ず **2つの独立実装**（例: 素朴 BFS と再帰式）で突き合わせてから採用する。
- 表は `data/` へ自動生成し、LaTeX へは生成物として流し込む（手打ちしない）。
