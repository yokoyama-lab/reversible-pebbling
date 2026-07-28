# アトラス Phase 0（実行センサス）の結果（2026-07-28）

生成: `python3 scripts/atlas_census.py`（18 秒で完走）。生データ `data/atlas/census.csv`。

## 結果

| コーパス | 実行 OK | 母数 | 備考 |
|---|---:|---:|---|
| pyjanus | **97** | 97 | **全数成功**（タイムアウトなし） |
| jana | **7** | 7 | 全数成功。方言差は問題にならなかった |
| oracle | 0 | 8 | `.jns` 方言が jana2014 でパース不能。**計画どおり落とす**（docs/81 §5） |
| memoization | 7 | 8 | `bottomUpCutRod` のみ実行時エラー（既知。exp52 §1） |
| **計** | **111** | **120** | |

**主コーパス（pyjanus + jana）は 104/104 で全数成功。**
docs/81 §5 の撤退条件（実行成功 50 本未満でミニアトラスに縮小）は大きく上回った。
**Phase 1（全数計測）へ進む条件は満たされた。**

## 収穫した詳細

1. `bottomUpCutRod` の失敗原因が特定できた:
   `Expected value to be 11 for local variable` — **delocal 表明の失敗**。
   PyJanus の方言差かプログラム側の前提の問題（exp52 では「原因未特定」だった）。
   Phase 1 では対象外とし、census に記録を残す。
2. 実行時間は全プログラムが 120 秒以内（最長でも数秒）。
   **Phase 1 のトレーサ（1 文ごとにスナップショット）でも現実的な時間で回る見込み。**
3. テスト実行時の副産物: **PyJanus は終端の非ゼロ値を自前で警告する**
   （`Warning: non-zero values remain at end of execution`）。
   Phase 1 で `final_live_bits` と突き合わせる検証に使える（独立実装照合の材料）。

## 次（Phase 1）

- exp51/exp52 のトレーサを一般化（**全配列の自動追跡**。変数名決め打ちの罠を恒久対応）。
- 既測 5 本（fib, fac, cut rod 3 種）の数値を回帰テストに固定してから全体へ。
- `peak_live_vars` を PyJanus 純正 `profile_space` と二重照合。
