# erasure-pebbling 論文の表（生成物）

`python3 scripts/gen_tables.py --out data/tables_erasure_pebbling` の出力。手編集しない。
Overleaf の `2026_erasure_pebbling/tables/` へはこの 3 ファイルをそのまま写す（または既定の出力先で生成する）。

- `reach.tex`: 定理 B1 は p>=2、LTV Lemma 1 は p>=2・e>=1 の主張なので、範囲外は `n/a`。
  下界の列が厳密値を超えたら生成器が止まる（`tests/test_gen_tables.py`、変異注入 2 種で検出を確認）。
  LTV 列は Lemma 1 の閉形式 (e+1)2^{p-2}。Procedure A の実測値（`data/exp03_ltv_compare.csv`）ではない。
  実測は p=2 で e+2（= 定理 B1）になり、p>=3 で閉形式に一致する。
- `recheck_reach_csv.log`: `scripts/recheck_reach_csv.py` で `data/exp03_reach.csv` の厳密値 25 行を
  BFS（`landauer.reach_e`, nmax=200）で再計算した記録。有界の全数検査（p<=5, e<=4）であり一般の定理ではない。
- `SHA256SUMS`: 入力 CSV・生成器・生成物のハッシュ。
