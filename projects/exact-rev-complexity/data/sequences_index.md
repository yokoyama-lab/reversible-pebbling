# 厳密値の数列 索引（自動生成・手編集禁止）

生成: `python3 scripts/sequences_index.py`

**種別**: `exact`=全数探索で最適性が確定 / `upper`=上界のみ / `lower`=下界のみ / `cutoff`=打ち切り / `mixed`=混在。
**`exact` だけ**を OEIS 照合（`scripts/oeis_check.py`）と holonomic guessing（`scripts/conjecture_queue.py`）に回す。

添字に飛びがある表は**最小添字からの連続部分だけ**を採った（`落` 列がその際に捨てた点数）。

**要約**: 93 本（exact 86 / lower 3 / mixed 1 / upper 3）。うち `exact` かつ 4 項以上が 75 本。

## 最適値（$M^*$・$p_{\min}$ など）

| key | 数列 | 出典 | 添字 | 項数 | 種別 | 落 | 先頭 |
|---|---|---|---|---:|---|---:|---|
| `fib:M*_p_min+0` | Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ | `data/exp04_fib.csv` | n から 1 | 43 | exact | 0 | 0, 1, 3, 5, 7, 11, 13, 17, … |
| `fib:M*_p_min+1` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ | `data/exp04_fib.csv` | n から 1 | 43 | exact | 0 | 0, 1, 3, 5, 7, 9, 11, 15, … |
| `fib:M*_p_min+2` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ | `data/exp04_fib.csv` | n から 1 | 43 | exact | 0 | 0, 1, 3, 5, 7, 9, 11, 13, … |
| `fam:cylinder:k[w=2]:off0` | cylinder (k[w=2]) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | k[w=2] から 2 | 17 | exact | 0 | 5, 9, 17, 21, 29, 37, 51, 49, … |
| `fam:cylinder:k[w=2]:off1` | cylinder (k[w=2]) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | k[w=2] から 2 | 17 | exact | 0 | 5, 9, 15, 19, 27, 35, 45, 47, … |
| `fam:cylinder:k[w=2]:off2` | cylinder (k[w=2]) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | k[w=2] から 2 | 17 | exact | 0 | 5, 9, 13, 17, 25, 33, 41, 45, … |
| `hard:0`★ | 鎖の $M^*(p_{\min})$ | `scripts/exp_guess_sequences.py` | n から 1 | 16 | exact | 0 | 1, 3, 5, 9, 11, 15, 19, 25, … |
| `hard:4`★ | spinal tree $S_k^*$ の $M^*(p_{\min})$ | `scripts/exp_guess_sequences.py` | n から 1 | 16 | exact | 0 | 5, 11, 19, 25, 35, 45, 61, 57, … |
| `hard:6`★ | spinal tree $S_k^*$ の $M^*(p_{\min}+1)$ | `scripts/exp_guess_sequences.py` | n から 1 | 16 | exact | 0 | 5, 9, 17, 23, 31, 39, 47, 53, … |
| `saturation:M*_p_min` | 飽和族の $M^*(p_{\min})$ | `data/exp01b_saturation.csv` | k から 1 | 16 | exact | 0 | 5, 11, 19, 25, 35, 45, 61, 57, … |
| `saturation:p_min` | 飽和族の $p_{\min}$ | `data/exp01b_saturation.csv` | k から 1 | 16 | exact | 0 | 3, 4, 4, 5, 5, 5, 5, 6, … |
| `chain:M*_p_min+0` | 鎖の $M^*(p_{\min})$ | `data/exp01_trees.csv` | n から 1 | 14 | exact | 0 | 1, 3, 5, 9, 11, 15, 19, 25, … |
| `chain:M*_p_min+1` | 鎖の $M^*(p_{\min}+1)$ | `data/exp01_trees.csv` | n から 1 | 14 | exact | 0 | 1, 3, 5, 7, 9, 13, 17, 21, … |
| `chain:M*_p_min+2` | 鎖の $M^*(p_{\min}+2)$ | `data/exp01_trees.csv` | n から 1 | 14 | exact | 0 | 1, 3, 5, 7, 9, 11, 15, 19, … |
| `fam:cylinder:k[w=3]:off0` | cylinder (k[w=3]) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | k[w=3] から 2 | 11 | exact | 0 | 5, 13, 23, 37, 47, 53, 75, 85, … |
| `slice:fib:M*_p_min+0:p10` | fib の M*_p_min+0 の $p_{\min}=10$ 切片 | `data/sequences_extended.csv（追加計算）` | n から 33 | 11 | exact | 0 | 125, 133, 141, 149, 157, 165, 173, 181, … |
| `slice:fib:M*_p_min+1:p10` | fib の M*_p_min+1 の $p_{\min}=10$ 切片 | `data/sequences_extended.csv（追加計算）` | n から 33 | 11 | exact | 0 | 107, 113, 119, 127, 135, 143, 151, 159, … |
| `slice:fib:M*_p_min+2:p10` | fib の M*_p_min+2 の $p_{\min}=10$ 切片 | `data/sequences_extended.csv（追加計算）` | n から 33 | 11 | exact | 0 | 103, 107, 111, 115, 119, 123, 129, 135, … |
| `fam:cylinder:k[w=3]:off1` | cylinder (k[w=3]) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | k[w=3] から 2 | 10 | exact | 0 | 5, 11, 21, 31, 41, 51, 67, 75, … |
| `fam:cylinder:k[w=3]:off2` | cylinder (k[w=3]) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | k[w=3] から 2 | 9 | exact | 0 | 5, 11, 19, 29, 39, 49, 61, 71, … |
| `fam:cylinder:k[w=4]:off0` | cylinder (k[w=4]) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | k[w=4] から 2 | 8 | exact | 0 | 5, 13, 27, 45, 93, 69, 107, 115 |
| `hard:5`★ | spinal tree $S_k^*$ の $M^*(p_{\min})$（段差の内側 $k=8..15$） | `scripts/exp_guess_sequences.py` | n から 1 | 8 | exact | 0 | 57, 71, 85, 101, 119, 137, 155, 179 |
| `slice:fam:cylinder:k[w=2]:off0:p9` | cylinder (k[w=2]) の $M^*(p_{\min}+0)$ の $p_{\min}=9$ 切片 | `data/families/atlas.csv` | k[w=2] から 9 | 8 | exact | 0 | 49, 57, 65, 79, 93, 109, 125, 147 |
| `slice:fam:cylinder:k[w=2]:off1:p9` | cylinder (k[w=2]) の $M^*(p_{\min}+1)$ の $p_{\min}=9$ 切片 | `data/families/atlas.csv` | k[w=2] から 9 | 8 | exact | 0 | 47, 55, 63, 73, 83, 99, 115, 133 |
| `slice:fam:cylinder:k[w=2]:off2:p9` | cylinder (k[w=2]) の $M^*(p_{\min}+2)$ の $p_{\min}=9$ 切片 | `data/families/atlas.csv` | k[w=2] から 9 | 8 | exact | 0 | 45, 53, 61, 69, 77, 85, 93, 101 |
| `slice:fib:M*_p_min+0:p8` | Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ の $p_{\min}=8$ 切片 | `data/exp04_fib.csv` | n から 17 | 8 | exact | 0 | 47, 51, 57, 63, 71, 79, 87, 97 |
| `slice:fib:M*_p_min+0:p9` | Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ の $p_{\min}=9$ 切片 | `data/exp04_fib.csv` | n から 25 | 8 | exact | 0 | 85, 93, 101, 109, 117, 125, 135, 145 |
| `slice:fib:M*_p_min+1:p8` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ の $p_{\min}=8$ 切片 | `data/exp04_fib.csv` | n から 17 | 8 | exact | 0 | 45, 49, 53, 57, 61, 65, 71, 77 |
| `slice:fib:M*_p_min+1:p9` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ の $p_{\min}=9$ 切片 | `data/exp04_fib.csv` | n から 25 | 8 | exact | 0 | 75, 79, 83, 89, 95, 101, 109, 117 |
| `slice:fib:M*_p_min+2:p8` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=8$ 切片 | `data/exp04_fib.csv` | n から 17 | 8 | exact | 0 | 43, 47, 51, 55, 59, 63, 67, 71 |
| `slice:fib:M*_p_min+2:p9` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=9$ 切片 | `data/exp04_fib.csv` | n から 25 | 8 | exact | 0 | 73, 77, 81, 85, 89, 93, 97, 101 |
| `fam:cylinder:k[w=4]:off1` | cylinder (k[w=4]) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | k[w=4] から 2 | 7 | exact | 0 | 5, 11, 25, 39, 57, 65, 85 |
| `fam:cylinder:k[w=4]:off2` | cylinder (k[w=4]) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | k[w=4] から 2 | 7 | exact | 0 | 5, 11, 23, 37, 51, 63, 79 |
| `fam:cylinder:k[w=5]:off0` | cylinder (k[w=5]) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | k[w=5] から 2 | 6 | exact | 0 | 5, 13, 27, 47, 103, 89 |
| `fam:cylinder:k[w=5]:off1` | cylinder (k[w=5]) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | k[w=5] から 2 | 6 | exact | 0 | 5, 11, 25, 43, 63, 79 |
| `fam:cylinder:k[w=5]:off2` | cylinder (k[w=5]) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | k[w=5] から 2 | 6 | exact | 0 | 5, 11, 23, 41, 59, 75 |
| `fam:cylinder:k[w=6]:off0` | cylinder (k[w=6]) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | k[w=6] から 2 | 6 | exact | 0 | 5, 13, 27, 47, 105, 97 |
| `fam:cylinder:k[w=6]:off1` | cylinder (k[w=6]) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | k[w=6] から 2 | 6 | exact | 0 | 5, 11, 25, 43, 67, 85 |
| `fam:cylinder:k[w=7]:off0` | cylinder (k[w=7]) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | k[w=7] から 2 | 6 | exact | 0 | 5, 13, 27, 47, 105, 99 |
| `fam:cylinder:k[w=7]:off1` | cylinder (k[w=7]) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | k[w=7] から 2 | 6 | exact | 0 | 5, 11, 25, 43, 67, 89 |
| `hard:1`★ | 完全二分木の $M^*(T_h)$ | `scripts/exp_guess_sequences.py` | n から 1 | 6 | exact | 0 | 1, 5, 17, 53, 155, 429 |
| `hard:2`★ | ピラミッドの $M^*(P_h, p_{\min})$ | `scripts/exp_guess_sequences.py` | n から 1 | 6 | exact | 0 | 5, 13, 27, 47, 105, 99 |
| `pascal:M*_p_min+0` | Pascal 型メモ化 DAGの $M^*(p_{\min})$ | `data/exp04_pascal.csv` | n から 1 | 6 | exact | 0 | 0, 1, 3, 7, 13, 23 |
| `pascal:M*_p_min+1` | Pascal 型メモ化 DAGの $M^*(p_{\min}+1)$ | `data/exp04_pascal.csv` | n から 1 | 6 | exact | 0 | 0, 1, 3, 7, 11, 21 |
| `pascal:M*_p_min+2` | Pascal 型メモ化 DAGの $M^*(p_{\min}+2)$ | `data/exp04_pascal.csv` | n から 1 | 6 | exact | 0 | 0, 1, 3, 7, 11, 19 |
| `slice:chain:M*_p_min+0:p5` | 鎖の $M^*(p_{\min})$ の $p_{\min}=5$ 切片 | `data/exp01_trees.csv` | n から 9 | 6 | exact | 0 | 25, 29, 33, 39, 45, 53 |
| `slice:chain:M*_p_min+1:p5` | 鎖の $M^*(p_{\min}+1)$ の $p_{\min}=5$ 切片 | `data/exp01_trees.csv` | n から 9 | 6 | exact | 0 | 23, 27, 31, 35, 39, 43 |
| `slice:chain:M*_p_min+2:p5` | 鎖の $M^*(p_{\min}+2)$ の $p_{\min}=5$ 切片 | `data/exp01_trees.csv` | n から 9 | 6 | exact | 0 | 21, 25, 29, 33, 37, 41 |
| `fam:cylinder:k[w=6]:off2` | cylinder (k[w=6]) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | k[w=6] から 2 | 5 | exact | 0 | 5, 11, 23, 41, 63 |
| `fam:cylinder:k[w=7]:off2` | cylinder (k[w=7]) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | k[w=7] から 2 | 5 | exact | 0 | 5, 11, 23, 41, 63 |
| `hard:3`★ | ピラミッドの $M^*(P_h, p_{\min})$（段差前のみ $h=1..5$） | `scripts/exp_guess_sequences.py` | n から 1 | 5 | exact | 0 | 5, 13, 27, 47, 105 |
| `baseline:edit_distance:floor` | edit_distance の floor | `data/atlas/baselines.csv` | n から 2 | 4 | lower | 0 | 7, 17, 31, 49 |
| `baseline:edit_distance:mstar` | edit_distance の mstar | `data/atlas/baselines.csv` | n から 2 | 4 | exact | 0 | 7, 25, 63, 117 |
| `baseline:knapsack:floor` | knapsack の floor | `data/atlas/baselines.csv` | n から 2 | 4 | lower | 0 | 5, 13, 27, 43 |
| `baseline:knapsack:mstar` | knapsack の mstar | `data/atlas/baselines.csv` | n から 2 | 4 | exact | 0 | 5, 17, 49, 103 |
| `baseline:lcs:floor` | lcs の floor | `data/atlas/baselines.csv` | n から 2 | 4 | lower | 0 | 7, 17, 31, 49 |
| `baseline:lcs:mstar` | lcs の mstar | `data/atlas/baselines.csv` | n から 2 | 4 | exact | 0 | 7, 25, 63, 117 |
| `fam:bitrev:k:off0` | bitrev (k) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | k から 1 | 4 | exact | 0 | 5, 17, 57, 209 |
| `fam:kary_tree:h[ary=2]:off0` | kary_tree (h[ary=2]) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | h[ary=2] から 1 | 4 | exact | 0 | 1, 5, 17, 53 |
| `fam:kary_tree:h[ary=2]:off1` | kary_tree (h[ary=2]) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | h[ary=2] から 1 | 4 | exact | 0 | 1, 5, 15, 45 |
| `fam:kary_tree:h[ary=2]:off2` | kary_tree (h[ary=2]) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | h[ary=2] から 1 | 4 | exact | 0 | 1, 5, 13, 43 |
| `slice:fam:cylinder:k[w=2]:off0:p7` | cylinder (k[w=2]) の $M^*(p_{\min}+0)$ の $p_{\min}=7$ 切片 | `data/families/atlas.csv` | k[w=2] から 5 | 4 | exact | 0 | 21, 29, 37, 51 |
| `slice:fam:cylinder:k[w=2]:off1:p7` | cylinder (k[w=2]) の $M^*(p_{\min}+1)$ の $p_{\min}=7$ 切片 | `data/families/atlas.csv` | k[w=2] から 5 | 4 | exact | 0 | 19, 27, 35, 45 |
| `slice:fam:cylinder:k[w=2]:off2:p7` | cylinder (k[w=2]) の $M^*(p_{\min}+2)$ の $p_{\min}=7$ 切片 | `data/families/atlas.csv` | k[w=2] から 5 | 4 | exact | 0 | 17, 25, 33, 41 |
| `fam:bitrev:k:off1` | bitrev (k) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | k から 1 | 3 | exact | 0 | 5, 15, 43 |
| `fam:bitrev:k:off2` | bitrev (k) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | k から 1 | 3 | exact | 0 | 5, 13, 41 |
| `fam:kary_tree:h[ary=3]:off0` | kary_tree (h[ary=3]) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | h[ary=3] から 1 | 3 | exact | 0 | 1, 7, 37 |
| `fam:kary_tree:h[ary=3]:off1` | kary_tree (h[ary=3]) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | h[ary=3] から 1 | 3 | exact | 0 | 1, 7, 35 |
| `fam:kary_tree:h[ary=3]:off2` | kary_tree (h[ary=3]) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | h[ary=3] から 1 | 3 | exact | 0 | 1, 7, 33 |
| `fam:kary_tree:h[ary=4]:off0` | kary_tree (h[ary=4]) の $M^*(p_{\min}+0)$ | `data/families/atlas.csv` | h[ary=4] から 1 | 3 | exact | 0 | 1, 9, 65 |
| `fam:kary_tree:h[ary=4]:off1` | kary_tree (h[ary=4]) の $M^*(p_{\min}+1)$ | `data/families/atlas.csv` | h[ary=4] から 1 | 3 | exact | 0 | 1, 9, 63 |
| `fam:kary_tree:h[ary=4]:off2` | kary_tree (h[ary=4]) の $M^*(p_{\min}+2)$ | `data/families/atlas.csv` | h[ary=4] から 1 | 3 | exact | 0 | 1, 9, 61 |
| `slice:fam:cylinder:k[w=2]:off0:p11` | fam の cylinder の $p_{\min}=11$ 切片 | `data/sequences_extended.csv（追加計算）` | n から 17 | 2 | exact | 0 | 115, 129 |
| `slice:fam:cylinder:k[w=2]:off1:p11` | fam の cylinder の $p_{\min}=11$ 切片 | `data/sequences_extended.csv（追加計算）` | n から 17 | 2 | exact | 0 | 109, 119 |
| `slice:fam:cylinder:k[w=2]:off2:p11` | fam の cylinder の $p_{\min}=11$ 切片 | `data/sequences_extended.csv（追加計算）` | n から 17 | 2 | exact | 0 | 105, 113 |
| `cpsat:summary` | （CP-SAT の M*: 数列化せず内訳のみ） | `data/families/cpsat.csv` | - から 0 | 0 | mixed | 0 |  |

## 閉形式が既知／既知値の再現（対照）

| key | 数列 | 出典 | 添字 | 項数 | 種別 | 落 | 先頭 |
|---|---|---|---|---:|---|---:|---|
| `reach:e0` | $\mathrm{reach}(p, e=0)$ | `data/exp03_reach.csv` | p から 1 | 5 | exact | 0 | 1, 2, 4, 8, 16 |
| `reach:e1` | $\mathrm{reach}(p, e=1)$ | `data/exp03_reach.csv` | p から 1 | 5 | exact | 0 | 1, 3, 6, 12, 24 |
| `reach:e2` | $\mathrm{reach}(p, e=2)$ | `data/exp03_reach.csv` | p から 1 | 5 | exact | 0 | 1, 4, 8, 16, 32 |
| `reach:e3` | $\mathrm{reach}(p, e=3)$ | `data/exp03_reach.csv` | p から 1 | 5 | exact | 0 | 1, 5, 10, 20, 40 |
| `reach:e4` | $\mathrm{reach}(p, e=4)$ | `data/exp03_reach.csv` | p から 1 | 5 | exact | 0 | 1, 6, 12, 24, 48 |
| `hard:9`★ | 五つ組 $\mathrm{BB}_{\mathrm{rev}}(k)$（既知値・対照） | `scripts/exp_guess_sequences.py` | n から 1 | 4 | exact | 0 | 6, 17, 48, 388 |

## 可逆 Busy Beaver

| key | 数列 | 出典 | 添字 | 項数 | 種別 | 落 | 先頭 |
|---|---|---|---|---:|---|---:|---|
| `hard:8`★ | 四つ組形式 $\mathrm{BB}^4_{\mathrm{rev}}(k)$ | `scripts/exp_guess_sequences.py` | n から 1 | 6 | exact | 0 | 2, 4, 6, 12, 22, 34 |
| `hard:7`★ | $\Sigma_{\mathrm{rev}}(k)$（可逆 BB の最大 1 の個数） | `scripts/exp_guess_sequences.py` | n から 1 | 5 | exact | 0 | 1, 2, 4, 8, 16 |

## 実プログラムの実測（最適値ではない）

| key | 数列 | 出典 | 添字 | 項数 | 種別 | 落 | 先頭 |
|---|---|---|---|---:|---|---:|---|
| `scaling:edit_distance:final_live_bits` | edit_distance の final_live_bits | `data/atlas/scaling.csv` | n から 2 | 6 | exact | 0 | 23, 40, 72, 108, 150, 198 |
| `scaling:edit_distance:steps` | edit_distance の steps | `data/atlas/scaling.csv` | n から 2 | 6 | exact | 0 | 52, 89, 137, 196, 266, 347 |
| `scaling:knapsack:final_live_bits` | knapsack の final_live_bits | `data/atlas/scaling.csv` | n から 2 | 6 | exact | 0 | 20, 39, 70, 109, 161, 226 |
| `scaling:knapsack:steps` | knapsack の steps | `data/atlas/scaling.csv` | n から 2 | 6 | exact | 0 | 50, 86, 129, 179, 239, 306 |
| `scaling:lcs:final_live_bits` | lcs の final_live_bits | `data/atlas/scaling.csv` | n から 2 | 6 | exact | 0 | 13, 24, 41, 63, 91, 125 |
| `scaling:lcs:steps` | lcs の steps | `data/atlas/scaling.csv` | n から 2 | 6 | exact | 0 | 29, 52, 81, 118, 161, 212 |
| `baseline:edit_distance:impl_moves` | edit_distance の impl_moves | `data/atlas/baselines.csv` | n から 2 | 4 | upper | 0 | 8, 15, 24, 35 |
| `baseline:knapsack:impl_moves` | knapsack の impl_moves | `data/atlas/baselines.csv` | n から 2 | 4 | upper | 0 | 6, 13, 22, 33 |
| `baseline:lcs:impl_moves` | lcs の impl_moves | `data/atlas/baselines.csv` | n から 2 | 4 | upper | 0 | 3, 8, 15, 24 |

★ = `data/holonomic_guess.md` で既に扱っている数列。

## 数列に使わなかったもの（注意書き）

- **（CP-SAT の M*: 数列化せず内訳のみ）**（`cpsat:summary`, mixed）: OPTIMAL かつ cap 非到達 18 行 / **cap 到達 21 行（打ち切り）** / UNKNOWN 15 行。BFS 側（families/atlas.csv）と重複するので数列には使わない

## 各数列の全項

### `baseline:edit_distance:floor` — edit_distance の floor

- 出典: `data/atlas/baselines.csv`、添字 n = 2..5、種別 **lower**
- 値: `[7, 17, 31, 49]`

### `baseline:edit_distance:impl_moves` — edit_distance の impl_moves

- 出典: `data/atlas/baselines.csv`、添字 n = 2..5、種別 **upper**
- 値: `[8, 15, 24, 35]`

### `baseline:edit_distance:mstar` — edit_distance の mstar

- 出典: `data/atlas/baselines.csv`、添字 n = 2..5、種別 **exact**
- 値: `[7, 25, 63, 117]`

### `baseline:knapsack:floor` — knapsack の floor

- 出典: `data/atlas/baselines.csv`、添字 n = 2..5、種別 **lower**
- 値: `[5, 13, 27, 43]`

### `baseline:knapsack:impl_moves` — knapsack の impl_moves

- 出典: `data/atlas/baselines.csv`、添字 n = 2..5、種別 **upper**
- 値: `[6, 13, 22, 33]`

### `baseline:knapsack:mstar` — knapsack の mstar

- 出典: `data/atlas/baselines.csv`、添字 n = 2..5、種別 **exact**
- 値: `[5, 17, 49, 103]`

### `baseline:lcs:floor` — lcs の floor

- 出典: `data/atlas/baselines.csv`、添字 n = 2..5、種別 **lower**
- 値: `[7, 17, 31, 49]`

### `baseline:lcs:impl_moves` — lcs の impl_moves

- 出典: `data/atlas/baselines.csv`、添字 n = 2..5、種別 **upper**
- 値: `[3, 8, 15, 24]`

### `baseline:lcs:mstar` — lcs の mstar

- 出典: `data/atlas/baselines.csv`、添字 n = 2..5、種別 **exact**
- 値: `[7, 25, 63, 117]`

### `chain:M*_p_min+0` — 鎖の $M^*(p_{\min})$

- 出典: `data/exp01_trees.csv`、添字 n = 1..14、種別 **exact**
- 注: $p_{\min}$ の段差で区分的になりうる（値が減る点に注意）
- 値: `[1, 3, 5, 9, 11, 15, 19, 25, 25, 29, 33, 39, 45, 53]`

### `chain:M*_p_min+1` — 鎖の $M^*(p_{\min}+1)$

- 出典: `data/exp01_trees.csv`、添字 n = 1..14、種別 **exact**
- 注: $p_{\min}$ の段差で区分的になりうる（値が減る点に注意）
- 値: `[1, 3, 5, 7, 9, 13, 17, 21, 23, 27, 31, 35, 39, 43]`

### `chain:M*_p_min+2` — 鎖の $M^*(p_{\min}+2)$

- 出典: `data/exp01_trees.csv`、添字 n = 1..14、種別 **exact**
- 注: $p_{\min}$ の段差で区分的になりうる（値が減る点に注意）
- 値: `[1, 3, 5, 7, 9, 11, 15, 19, 21, 25, 29, 33, 37, 41]`

### `fam:bitrev:k:off0` — bitrev (k) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 k = 1..4、種別 **exact**
- 値: `[5, 17, 57, 209]`

### `fam:bitrev:k:off1` — bitrev (k) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 k = 1..3、種別 **exact**
- 値: `[5, 15, 43]`

### `fam:bitrev:k:off2` — bitrev (k) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 k = 1..3、種別 **exact**
- 値: `[5, 13, 41]`

### `fam:cylinder:k[w=2]:off0` — cylinder (k[w=2]) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 k[w=2] = 2..18、種別 **exact**
- 値: `[5, 9, 17, 21, 29, 37, 51, 49, 57, 65, 79, 93, 109, 125, 147, 115, 129]`

### `fam:cylinder:k[w=2]:off1` — cylinder (k[w=2]) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 k[w=2] = 2..18、種別 **exact**
- 注:   （`scripts/extend_sequences.py` で 2 点を追加計算）
- 値: `[5, 9, 15, 19, 27, 35, 45, 47, 55, 63, 73, 83, 99, 115, 133, 109, 119]`

### `fam:cylinder:k[w=2]:off2` — cylinder (k[w=2]) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 k[w=2] = 2..18、種別 **exact**
- 注:   （`scripts/extend_sequences.py` で 2 点を追加計算）
- 値: `[5, 9, 13, 17, 25, 33, 41, 45, 53, 61, 69, 77, 85, 93, 101, 105, 113]`

### `fam:cylinder:k[w=3]:off0` — cylinder (k[w=3]) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 k[w=3] = 2..12、種別 **exact**
- 値: `[5, 13, 23, 37, 47, 53, 75, 85, 115, 115, 145]`

### `fam:cylinder:k[w=3]:off1` — cylinder (k[w=3]) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 k[w=3] = 2..11、種別 **exact**
- 値: `[5, 11, 21, 31, 41, 51, 67, 75, 91, 95]`

### `fam:cylinder:k[w=3]:off2` — cylinder (k[w=3]) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 k[w=3] = 2..10、種別 **exact**
- 値: `[5, 11, 19, 29, 39, 49, 61, 71, 83]`

### `fam:cylinder:k[w=4]:off0` — cylinder (k[w=4]) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 k[w=4] = 2..9、種別 **exact**
- 値: `[5, 13, 27, 45, 93, 69, 107, 115]`

### `fam:cylinder:k[w=4]:off1` — cylinder (k[w=4]) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 k[w=4] = 2..8、種別 **exact**
- 値: `[5, 11, 25, 39, 57, 65, 85]`

### `fam:cylinder:k[w=4]:off2` — cylinder (k[w=4]) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 k[w=4] = 2..8、種別 **exact**
- 値: `[5, 11, 23, 37, 51, 63, 79]`

### `fam:cylinder:k[w=5]:off0` — cylinder (k[w=5]) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 k[w=5] = 2..7、種別 **exact**
- 値: `[5, 13, 27, 47, 103, 89]`

### `fam:cylinder:k[w=5]:off1` — cylinder (k[w=5]) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 k[w=5] = 2..7、種別 **exact**
- 値: `[5, 11, 25, 43, 63, 79]`

### `fam:cylinder:k[w=5]:off2` — cylinder (k[w=5]) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 k[w=5] = 2..7、種別 **exact**
- 値: `[5, 11, 23, 41, 59, 75]`

### `fam:cylinder:k[w=6]:off0` — cylinder (k[w=6]) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 k[w=6] = 2..7、種別 **exact**
- 値: `[5, 13, 27, 47, 105, 97]`

### `fam:cylinder:k[w=6]:off1` — cylinder (k[w=6]) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 k[w=6] = 2..7、種別 **exact**
- 値: `[5, 11, 25, 43, 67, 85]`

### `fam:cylinder:k[w=6]:off2` — cylinder (k[w=6]) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 k[w=6] = 2..6、種別 **exact**
- 値: `[5, 11, 23, 41, 63]`

### `fam:cylinder:k[w=7]:off0` — cylinder (k[w=7]) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 k[w=7] = 2..7、種別 **exact**
- 値: `[5, 13, 27, 47, 105, 99]`

### `fam:cylinder:k[w=7]:off1` — cylinder (k[w=7]) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 k[w=7] = 2..7、種別 **exact**
- 値: `[5, 11, 25, 43, 67, 89]`

### `fam:cylinder:k[w=7]:off2` — cylinder (k[w=7]) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 k[w=7] = 2..6、種別 **exact**
- 値: `[5, 11, 23, 41, 63]`

### `fam:kary_tree:h[ary=2]:off0` — kary_tree (h[ary=2]) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 h[ary=2] = 1..4、種別 **exact**
- 値: `[1, 5, 17, 53]`

### `fam:kary_tree:h[ary=2]:off1` — kary_tree (h[ary=2]) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 h[ary=2] = 1..4、種別 **exact**
- 値: `[1, 5, 15, 45]`

### `fam:kary_tree:h[ary=2]:off2` — kary_tree (h[ary=2]) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 h[ary=2] = 1..4、種別 **exact**
- 値: `[1, 5, 13, 43]`

### `fam:kary_tree:h[ary=3]:off0` — kary_tree (h[ary=3]) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 h[ary=3] = 1..3、種別 **exact**
- 値: `[1, 7, 37]`

### `fam:kary_tree:h[ary=3]:off1` — kary_tree (h[ary=3]) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 h[ary=3] = 1..3、種別 **exact**
- 値: `[1, 7, 35]`

### `fam:kary_tree:h[ary=3]:off2` — kary_tree (h[ary=3]) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 h[ary=3] = 1..3、種別 **exact**
- 値: `[1, 7, 33]`

### `fam:kary_tree:h[ary=4]:off0` — kary_tree (h[ary=4]) の $M^*(p_{\min}+0)$

- 出典: `data/families/atlas.csv`、添字 h[ary=4] = 1..3、種別 **exact**
- 値: `[1, 9, 65]`

### `fam:kary_tree:h[ary=4]:off1` — kary_tree (h[ary=4]) の $M^*(p_{\min}+1)$

- 出典: `data/families/atlas.csv`、添字 h[ary=4] = 1..3、種別 **exact**
- 値: `[1, 9, 63]`

### `fam:kary_tree:h[ary=4]:off2` — kary_tree (h[ary=4]) の $M^*(p_{\min}+2)$

- 出典: `data/families/atlas.csv`、添字 h[ary=4] = 1..3、種別 **exact**
- 値: `[1, 9, 61]`

### `fib:M*_p_min+0` — Fibonacci 型メモ化 DAGの $M^*(p_{\min})$

- 出典: `data/exp04_fib.csv`、添字 n = 1..43、種別 **exact**
- 注: $p_{\min}$ の段差で区分的になりうる（値が減る点に注意）  （`scripts/extend_sequences.py` で 14 点を追加計算）
- 値: `[0, 1, 3, 5, 7, 11, 13, 17, 19, 23, 27, 33, 33, 37, 43, 51, 47, 51, 57, 63, 71, 79, 87, 97, 85, 93, 101, 109, 117, 125, 135, 145, 125, 133, 141, 149, 157, 165, 173, 181, 189, 199, 209]`

### `fib:M*_p_min+1` — Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$

- 出典: `data/exp04_fib.csv`、添字 n = 1..43、種別 **exact**
- 注: $p_{\min}$ の段差で区分的になりうる（値が減る点に注意）  （`scripts/extend_sequences.py` で 14 点を追加計算）
- 値: `[0, 1, 3, 5, 7, 9, 11, 15, 17, 21, 25, 29, 31, 35, 39, 43, 45, 49, 53, 57, 61, 65, 71, 77, 75, 79, 83, 89, 95, 101, 109, 117, 107, 113, 119, 127, 135, 143, 151, 159, 167, 175, 183]`

### `fib:M*_p_min+2` — Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$

- 出典: `data/exp04_fib.csv`、添字 n = 1..43、種別 **exact**
- 注: $p_{\min}$ の段差で区分的になりうる（値が減る点に注意）  （`scripts/extend_sequences.py` で 14 点を追加計算）
- 値: `[0, 1, 3, 5, 7, 9, 11, 13, 15, 19, 23, 27, 29, 33, 37, 41, 43, 47, 51, 55, 59, 63, 67, 71, 73, 77, 81, 85, 89, 93, 97, 101, 103, 107, 111, 115, 119, 123, 129, 135, 141, 147, 155]`

### `hard:0` — 鎖の $M^*(p_{\min})$

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..16、種別 **exact**
- 注: 先行プロジェクト 2026_exact_reversible_pebbling（$n=1..16$）。OEIS 未登録。$p_{\min}$ が $n=9$ で変わるため区分的。
- 値: `[1, 3, 5, 9, 11, 15, 19, 25, 25, 29, 33, 39, 45, 53, 61, 71]`

### `hard:1` — 完全二分木の $M^*(T_h)$

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..6、種別 **exact**
- 注: data/exp01_results.md §2.1（$h=1..6$、free-leaves 流儀）。OEIS 未登録。予想 $2\cdot3^h-1$ は反証済み。
- 値: `[1, 5, 17, 53, 155, 429]`

### `hard:2` — ピラミッドの $M^*(P_h, p_{\min})$

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..6、種別 **exact**
- 注: data/exp01_results.md §2.2（$h=1..6$、all-pebbled 流儀）。$h=6$ で $p_{\min}$ が 2 段上がり値が**減る**（区分的）。
- 値: `[5, 13, 27, 47, 105, 99]`

### `hard:3` — ピラミッドの $M^*(P_h, p_{\min})$（段差前のみ $h=1..5$）

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..5、種別 **exact**
- 注: 上の数列から $p_{\min}$ 段差の手前だけを取り出したもの。4点当てはめ $3h^2-h+3$ が5点目で崩壊した実例。
- 値: `[5, 13, 27, 47, 105]`

### `hard:4` — spinal tree $S_k^*$ の $M^*(p_{\min})$

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..16、種別 **exact**
- 注: data/exp01_results.md §2.3（$k=1..16$、all-pebbled 流儀）。OEIS 未登録。$k=8,16$ で $p_{\min}$ 段差＝値が減る（区分的）。
- 値: `[5, 11, 19, 25, 35, 45, 61, 57, 71, 85, 101, 119, 137, 155, 179, 153]`

### `hard:5` — spinal tree $S_k^*$ の $M^*(p_{\min})$（段差の内側 $k=8..15$）

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..8、種別 **exact**
- 注: 上の数列から $p_{\min}=6$ が続く区間だけを取り出したもの（固定 $p$ 相当）。
- 値: `[57, 71, 85, 101, 119, 137, 155, 179]`

### `hard:6` — spinal tree $S_k^*$ の $M^*(p_{\min}+1)$

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..16、種別 **exact**
- 注: data/exp01_results.md §2.3。
- 値: `[5, 9, 17, 23, 31, 39, 47, 53, 61, 71, 81, 91, 105, 121, 137, 125]`

### `hard:7` — $\Sigma_{\mathrm{rev}}(k)$（可逆 BB の最大 1 の個数）

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..5、種別 **exact**
- 注: data/exp05_results.md（$k=1..5$、五つ組形式）。bbchallenge wiki に無い量。OEIS 未登録。
- 値: `[1, 2, 4, 8, 16]`

### `hard:8` — 四つ組形式 $\mathrm{BB}^4_{\mathrm{rev}}(k)$

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..6、種別 **exact**
- 注: data/exp05_results.md（$k=1..6$、Morita 流四つ組）。wiki 未収録。
- 値: `[2, 4, 6, 12, 22, 34]`

### `hard:9` — 五つ組 $\mathrm{BB}_{\mathrm{rev}}(k)$（既知値・対照）

- 出典: `scripts/exp_guess_sequences.py`、添字 n = 1..4、種別 **exact**
- 注: bbchallenge wiki（$k=2..5$）。**我々の発見ではなく既知値の独立再現**。
- 値: `[6, 17, 48, 388]`

### `pascal:M*_p_min+0` — Pascal 型メモ化 DAGの $M^*(p_{\min})$

- 出典: `data/exp04_pascal.csv`、添字 n = 1..6、種別 **exact**
- 注: $p_{\min}$ の段差で区分的になりうる（値が減る点に注意）
- 値: `[0, 1, 3, 7, 13, 23]`

### `pascal:M*_p_min+1` — Pascal 型メモ化 DAGの $M^*(p_{\min}+1)$

- 出典: `data/exp04_pascal.csv`、添字 n = 1..6、種別 **exact**
- 注: $p_{\min}$ の段差で区分的になりうる（値が減る点に注意）
- 値: `[0, 1, 3, 7, 11, 21]`

### `pascal:M*_p_min+2` — Pascal 型メモ化 DAGの $M^*(p_{\min}+2)$

- 出典: `data/exp04_pascal.csv`、添字 n = 1..6、種別 **exact**
- 注: $p_{\min}$ の段差で区分的になりうる（値が減る点に注意）
- 値: `[0, 1, 3, 7, 11, 19]`

### `reach:e0` — $\mathrm{reach}(p, e=0)$

- 出典: `data/exp03_reach.csv`、添字 p = 1..5、種別 **exact**
- 注: **閉形式は確定済み**（定理 B2 $=(e+2)2^{p-2}$、`lean/Revgarbage/PebbleB1.lean` で機械証明）。健全性の対照に使う
- 値: `[1, 2, 4, 8, 16]`

### `reach:e1` — $\mathrm{reach}(p, e=1)$

- 出典: `data/exp03_reach.csv`、添字 p = 1..5、種別 **exact**
- 注: **閉形式は確定済み**（定理 B2 $=(e+2)2^{p-2}$、`lean/Revgarbage/PebbleB1.lean` で機械証明）。健全性の対照に使う
- 値: `[1, 3, 6, 12, 24]`

### `reach:e2` — $\mathrm{reach}(p, e=2)$

- 出典: `data/exp03_reach.csv`、添字 p = 1..5、種別 **exact**
- 注: **閉形式は確定済み**（定理 B2 $=(e+2)2^{p-2}$、`lean/Revgarbage/PebbleB1.lean` で機械証明）。健全性の対照に使う
- 値: `[1, 4, 8, 16, 32]`

### `reach:e3` — $\mathrm{reach}(p, e=3)$

- 出典: `data/exp03_reach.csv`、添字 p = 1..5、種別 **exact**
- 注: **閉形式は確定済み**（定理 B2 $=(e+2)2^{p-2}$、`lean/Revgarbage/PebbleB1.lean` で機械証明）。健全性の対照に使う
- 値: `[1, 5, 10, 20, 40]`

### `reach:e4` — $\mathrm{reach}(p, e=4)$

- 出典: `data/exp03_reach.csv`、添字 p = 1..5、種別 **exact**
- 注: **閉形式は確定済み**（定理 B2 $=(e+2)2^{p-2}$、`lean/Revgarbage/PebbleB1.lean` で機械証明）。健全性の対照に使う
- 値: `[1, 6, 12, 24, 48]`

### `saturation:M*_p_min` — 飽和族の $M^*(p_{\min})$

- 出典: `data/exp01b_saturation.csv`、添字 k = 1..16、種別 **exact**
- 値: `[5, 11, 19, 25, 35, 45, 61, 57, 71, 85, 101, 119, 137, 155, 179, 153]`

### `saturation:p_min` — 飽和族の $p_{\min}$

- 出典: `data/exp01b_saturation.csv`、添字 k = 1..16、種別 **exact**
- 値: `[3, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7]`

### `scaling:edit_distance:final_live_bits` — edit_distance の final_live_bits

- 出典: `data/atlas/scaling.csv`、添字 n = 2..7、種別 **exact**
- 注: **実プログラムの実測値であって最適値ではない**。閉形式が出ても『そのプログラムの計算量』の主張にしかならない
- 値: `[23, 40, 72, 108, 150, 198]`

### `scaling:edit_distance:steps` — edit_distance の steps

- 出典: `data/atlas/scaling.csv`、添字 n = 2..7、種別 **exact**
- 注: **実プログラムの実測値であって最適値ではない**。閉形式が出ても『そのプログラムの計算量』の主張にしかならない
- 値: `[52, 89, 137, 196, 266, 347]`

### `scaling:knapsack:final_live_bits` — knapsack の final_live_bits

- 出典: `data/atlas/scaling.csv`、添字 n = 2..7、種別 **exact**
- 注: **実プログラムの実測値であって最適値ではない**。閉形式が出ても『そのプログラムの計算量』の主張にしかならない
- 値: `[20, 39, 70, 109, 161, 226]`

### `scaling:knapsack:steps` — knapsack の steps

- 出典: `data/atlas/scaling.csv`、添字 n = 2..7、種別 **exact**
- 注: **実プログラムの実測値であって最適値ではない**。閉形式が出ても『そのプログラムの計算量』の主張にしかならない
- 値: `[50, 86, 129, 179, 239, 306]`

### `scaling:lcs:final_live_bits` — lcs の final_live_bits

- 出典: `data/atlas/scaling.csv`、添字 n = 2..7、種別 **exact**
- 注: **実プログラムの実測値であって最適値ではない**。閉形式が出ても『そのプログラムの計算量』の主張にしかならない
- 値: `[13, 24, 41, 63, 91, 125]`

### `scaling:lcs:steps` — lcs の steps

- 出典: `data/atlas/scaling.csv`、添字 n = 2..7、種別 **exact**
- 注: **実プログラムの実測値であって最適値ではない**。閉形式が出ても『そのプログラムの計算量』の主張にしかならない
- 値: `[29, 52, 81, 118, 161, 212]`

### `slice:chain:M*_p_min+0:p5` — 鎖の $M^*(p_{\min})$ の $p_{\min}=5$ 切片

- 出典: `data/exp01_trees.csv`、添字 n = 9..14、種別 **exact**
- 注: $p_{\min}=5$ が続く区間だけを取り出した（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）
- 値: `[25, 29, 33, 39, 45, 53]`

### `slice:chain:M*_p_min+1:p5` — 鎖の $M^*(p_{\min}+1)$ の $p_{\min}=5$ 切片

- 出典: `data/exp01_trees.csv`、添字 n = 9..14、種別 **exact**
- 注: $p_{\min}=5$ が続く区間だけを取り出した（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）
- 値: `[23, 27, 31, 35, 39, 43]`

### `slice:chain:M*_p_min+2:p5` — 鎖の $M^*(p_{\min}+2)$ の $p_{\min}=5$ 切片

- 出典: `data/exp01_trees.csv`、添字 n = 9..14、種別 **exact**
- 注: $p_{\min}=5$ が続く区間だけを取り出した（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）
- 値: `[21, 25, 29, 33, 37, 41]`

### `slice:fam:cylinder:k[w=2]:off0:p11` — fam の cylinder の $p_{\min}=11$ 切片

- 出典: `data/sequences_extended.csv（追加計算）`、添字 n = 17..18、種別 **exact**
- 注: **追加計算だけで得た新しい切片**（表にはまだ無い）
- 値: `[115, 129]`

### `slice:fam:cylinder:k[w=2]:off0:p7` — cylinder (k[w=2]) の $M^*(p_{\min}+0)$ の $p_{\min}=7$ 切片

- 出典: `data/families/atlas.csv`、添字 k[w=2] = 5..8、種別 **exact**
- 注: $p_{\min}=7$ の区間だけ。**閉じている**
- 値: `[21, 29, 37, 51]`

### `slice:fam:cylinder:k[w=2]:off0:p9` — cylinder (k[w=2]) の $M^*(p_{\min}+0)$ の $p_{\min}=9$ 切片

- 出典: `data/families/atlas.csv`、添字 k[w=2] = 9..16、種別 **exact**
- 注: $p_{\min}=9$ の区間だけ。**閉じている**
- 値: `[49, 57, 65, 79, 93, 109, 125, 147]`

### `slice:fam:cylinder:k[w=2]:off1:p11` — fam の cylinder の $p_{\min}=11$ 切片

- 出典: `data/sequences_extended.csv（追加計算）`、添字 n = 17..18、種別 **exact**
- 注: **追加計算だけで得た新しい切片**（表にはまだ無い）
- 値: `[109, 119]`

### `slice:fam:cylinder:k[w=2]:off1:p7` — cylinder (k[w=2]) の $M^*(p_{\min}+1)$ の $p_{\min}=7$ 切片

- 出典: `data/families/atlas.csv`、添字 k[w=2] = 5..8、種別 **exact**
- 注: $p_{\min}=7$ の区間だけ。**閉じている**
- 値: `[19, 27, 35, 45]`

### `slice:fam:cylinder:k[w=2]:off1:p9` — cylinder (k[w=2]) の $M^*(p_{\min}+1)$ の $p_{\min}=9$ 切片

- 出典: `data/families/atlas.csv`、添字 k[w=2] = 9..16、種別 **exact**
- 注: $p_{\min}=9$ の区間だけ。まだ開いている  （追加計算で $p_{\min}$ の次の段が見つかったので、**この切片は閉じている**）
- 値: `[47, 55, 63, 73, 83, 99, 115, 133]`

### `slice:fam:cylinder:k[w=2]:off2:p11` — fam の cylinder の $p_{\min}=11$ 切片

- 出典: `data/sequences_extended.csv（追加計算）`、添字 n = 17..18、種別 **exact**
- 注: **追加計算だけで得た新しい切片**（表にはまだ無い）
- 値: `[105, 113]`

### `slice:fam:cylinder:k[w=2]:off2:p7` — cylinder (k[w=2]) の $M^*(p_{\min}+2)$ の $p_{\min}=7$ 切片

- 出典: `data/families/atlas.csv`、添字 k[w=2] = 5..8、種別 **exact**
- 注: $p_{\min}=7$ の区間だけ。**閉じている**
- 値: `[17, 25, 33, 41]`

### `slice:fam:cylinder:k[w=2]:off2:p9` — cylinder (k[w=2]) の $M^*(p_{\min}+2)$ の $p_{\min}=9$ 切片

- 出典: `data/families/atlas.csv`、添字 k[w=2] = 9..16、種別 **exact**
- 注: $p_{\min}=9$ の区間だけ。まだ開いている  （追加計算で $p_{\min}$ の次の段が見つかったので、**この切片は閉じている**）
- 値: `[45, 53, 61, 69, 77, 85, 93, 101]`

### `slice:fib:M*_p_min+0:p10` — fib の M*_p_min+0 の $p_{\min}=10$ 切片

- 出典: `data/sequences_extended.csv（追加計算）`、添字 n = 33..43、種別 **exact**
- 注: **追加計算だけで得た新しい切片**（表にはまだ無い）
- 値: `[125, 133, 141, 149, 157, 165, 173, 181, 189, 199, 209]`

### `slice:fib:M*_p_min+0:p8` — Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ の $p_{\min}=8$ 切片

- 出典: `data/exp04_fib.csv`、添字 n = 17..24、種別 **exact**
- 注: $p_{\min}=8$ が続く区間だけを取り出した（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）。**この切片は閉じている**（次の添字は別の $p_{\min}$ に属する）ので、次の 1 点を計算しても検証にならない
- 値: `[47, 51, 57, 63, 71, 79, 87, 97]`

### `slice:fib:M*_p_min+0:p9` — Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ の $p_{\min}=9$ 切片

- 出典: `data/exp04_fib.csv`、添字 n = 25..32、種別 **exact**
- 注: $p_{\min}=9$ が続く区間だけを取り出した（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）  （追加計算で $p_{\min}$ の次の段が見つかったので、**この切片は閉じている**）  （`scripts/extend_sequences.py` で 3 点を追加計算）
- 値: `[85, 93, 101, 109, 117, 125, 135, 145]`

### `slice:fib:M*_p_min+1:p10` — fib の M*_p_min+1 の $p_{\min}=10$ 切片

- 出典: `data/sequences_extended.csv（追加計算）`、添字 n = 33..43、種別 **exact**
- 注: **追加計算だけで得た新しい切片**（表にはまだ無い）
- 値: `[107, 113, 119, 127, 135, 143, 151, 159, 167, 175, 183]`

### `slice:fib:M*_p_min+1:p8` — Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ の $p_{\min}=8$ 切片

- 出典: `data/exp04_fib.csv`、添字 n = 17..24、種別 **exact**
- 注: $p_{\min}=8$ が続く区間だけを取り出した（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）。**この切片は閉じている**（次の添字は別の $p_{\min}$ に属する）ので、次の 1 点を計算しても検証にならない
- 値: `[45, 49, 53, 57, 61, 65, 71, 77]`

### `slice:fib:M*_p_min+1:p9` — Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ の $p_{\min}=9$ 切片

- 出典: `data/exp04_fib.csv`、添字 n = 25..32、種別 **exact**
- 注: $p_{\min}=9$ が続く区間だけを取り出した（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）  （追加計算で $p_{\min}$ の次の段が見つかったので、**この切片は閉じている**）  （`scripts/extend_sequences.py` で 3 点を追加計算）
- 値: `[75, 79, 83, 89, 95, 101, 109, 117]`

### `slice:fib:M*_p_min+2:p10` — fib の M*_p_min+2 の $p_{\min}=10$ 切片

- 出典: `data/sequences_extended.csv（追加計算）`、添字 n = 33..43、種別 **exact**
- 注: **追加計算だけで得た新しい切片**（表にはまだ無い）
- 値: `[103, 107, 111, 115, 119, 123, 129, 135, 141, 147, 155]`

### `slice:fib:M*_p_min+2:p8` — Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=8$ 切片

- 出典: `data/exp04_fib.csv`、添字 n = 17..24、種別 **exact**
- 注: $p_{\min}=8$ が続く区間だけを取り出した（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）。**この切片は閉じている**（次の添字は別の $p_{\min}$ に属する）ので、次の 1 点を計算しても検証にならない
- 値: `[43, 47, 51, 55, 59, 63, 67, 71]`

### `slice:fib:M*_p_min+2:p9` — Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=9$ 切片

- 出典: `data/exp04_fib.csv`、添字 n = 25..32、種別 **exact**
- 注: $p_{\min}=9$ が続く区間だけを取り出した（固定 $p$ 相当。段差をまたがないので漸化式の候補になる）  （追加計算で $p_{\min}$ の次の段が見つかったので、**この切片は閉じている**）  （`scripts/extend_sequences.py` で 3 点を追加計算）
- 値: `[73, 77, 81, 85, 89, 93, 97, 101]`
