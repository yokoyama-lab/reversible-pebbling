# アトラス Phase 2（スケーリング）の結果（2026-07-28）

生成: `python3 scripts/atlas_scale.py`（9 族 × 6 サイズ = 54 点、102 秒、失敗 0）。
生データ `data/atlas/scaling.csv`。回帰テスト 3 件 pass（全族の実行・fib_pairs の exp51 再現・
gcd 族の成長）。**当てはめはしない**（docs/81 §3 Phase 2 の規約）。以下の「観察」は
すべて**実測点上の等式・比の照合のみ**であり、層 3（機械実験）である。一般式は主張しない。

## 1. 実測列（steps）と隣接比

| family | steps（6 点） | 隣接比 | stack_peak |
|---|---|---|---|
| fib_iter | 25→125 | 1.80→1.19 | 0 |
| factorial | 31→36,859 | **4.48→4.00** | 0 |
| gcd_fib | 20→60 | 1.40→1.15 | **= k（6/6 点で一致）** |
| bubble_sort | 68→788 | 2.18→1.36 | **= n(n−1)/2（6/6 点で一致）** |
| edit_distance | 52→347 | 1.71→1.30 | 0 |
| lcs | 29→212 | 1.79→1.32 | 0 |
| knapsack | 50→306 | 1.72→1.28 | 0 |
| fib_pairs_2017 | 15→50 | **一階差分が全点 7** | 0 |
| cutrod_linear | 210→16,878 | 2.71→2.27 | **/steps = 0.105→0.111** |

## 2. 観察（層 3。すべて実測点のみの照合）

1. **成長の型が 3 群に分かれる。**
   線形群（fib_iter・gcd_fib・fib_pairs_2017: 一階差分がほぼ/完全に一定）、
   多項式群（sort・DP 系: 隣接比が 1 に向かって減少）、
   急成長群（factorial: 隣接比が 4.00 に張り付く、cutrod_linear: 2.27 に張り付く）。
   再帰の uncompute を素朴に書いた factorial が最も高くつく。
2. **スタックの正体が族ごとに厳密に読めた（測定 6 点全てで等式が成立）:**
   - gcd_fib: `stack_peak = k`（除算 1 回につき push 1 回、という構造の反映）。
   - bubble_sort: `stack_peak = n(n−1)/2`（比較 1 回につき push 1 回）。
   - cutrod_linear: `stack_peak / steps` が 0.105→0.111 でほぼ一定。
     **「メモリ使用量は実行時間に比例する」という 2021 年の著者メモ
     （`2021_rev_memoization2/programs/memo`）を、スケーリング実測として初めて裏づけた。**
   ⚠️ いずれも 6 点の照合であり一般式の証明ではない（4 回崩壊の教訓。層 2 に上げるには
   プログラム構造からの証明が要る——gcd と bubble_sort は構造的に自明に近いが、未証明は未証明）。
3. **fib_pairs_2017 の steps は完全に線形（差分 7 が全点）。**
   exp51 の「実装は put 部分だけを実行する（線形）」の、サイズを振った確認になっている。
4. **bottom-up DP（edit_distance・lcs・knapsack）はスタックを一切使わない。**
   Phase 1 の「スタック支配型 = グラフ／top-down 再帰」クラスタの裏面の確認。

## 3. 論文・短報への含意

- JSSST 短報の図の候補: 隣接比の推移（3 群が視覚的に分かれる）と、
  スタック等式 2 件（gcd・bubble_sort）。図は人間確認を経てから作成。
- 候補 3 論文には「$\Theta(n)$ 空間・熱 0 の設計点」の実在がコーパス横断で示せる。

## 4. 次

1. Phase 3: DP 系（fib_pairs・cutrod・knapsack・edit_distance・lcs）に厳密最適の基準線。
2. 注釈つき clean/dirty 判定。
3. bubble_sort・gcd のスタック等式を層 2 に上げる（構造からの紙証明。短い）。
