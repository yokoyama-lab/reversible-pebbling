# OEIS 照合の結果（自動生成・手編集禁止）

生成: `python3 scripts/oeis_check.py`（**読み取りのみ**）

**読み方**: `error` は「未登録」ではない。問い合わせが失敗しただけなので、取り直すまで何も言えない。`none` だけが「OEIS に無い」を意味する。

**要約**: verified 13 / none 45 / 未取得 3

**制御列の自己検査**: `reach:e0`（$2^{p-1}$、閉形式が確定済み）の判定は **verified**。ここが `verified` でなければ照合系が壊れている。

| key | 数列 | 項数 | 判定 | OEIS |
|---|---|---:|---|---|
| `fib:M*_p_min+0` | Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ | 37 | 未登録 |  |
| `fib:M*_p_min+1` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ | 37 | 未登録 |  |
| `fib:M*_p_min+2` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ | 37 | 未登録 |  |
| `fam:cylinder:k[w=2]:off0` | cylinder (k[w=2]) の $M^*(p_{\min}+0)$ | 17 | 未登録 |  |
| `hard:0` | 鎖の $M^*(p_{\min})$ | 16 | 未登録 |  |
| `hard:4` | spinal tree $S_k^*$ の $M^*(p_{\min})$ | 16 | 未登録 |  |
| `hard:6` | spinal tree $S_k^*$ の $M^*(p_{\min}+1)$ | 16 | 未登録 |  |
| `saturation:M*_p_min` | 飽和族の $M^*(p_{\min})$ | 16 | 未登録 |  |
| `saturation:p_min` | 飽和族の $p_{\min}$ | 16 | 未登録 |  |
| `fam:cylinder:k[w=2]:off1` | cylinder (k[w=2]) の $M^*(p_{\min}+1)$ | 15 | 未登録 |  |
| `fam:cylinder:k[w=2]:off2` | cylinder (k[w=2]) の $M^*(p_{\min}+2)$ | 15 | 未登録 |  |
| `chain:M*_p_min+0` | 鎖の $M^*(p_{\min})$ | 14 | 未登録 |  |
| `chain:M*_p_min+1` | 鎖の $M^*(p_{\min}+1)$ | 14 | 未登録 |  |
| `chain:M*_p_min+2` | 鎖の $M^*(p_{\min}+2)$ | 14 | 未登録 |  |
| `fam:cylinder:k[w=3]:off0` | cylinder (k[w=3]) の $M^*(p_{\min}+0)$ | 11 | 未登録 |  |
| `fam:cylinder:k[w=3]:off1` | cylinder (k[w=3]) の $M^*(p_{\min}+1)$ | 10 | 未登録 |  |
| `fam:cylinder:k[w=3]:off2` | cylinder (k[w=3]) の $M^*(p_{\min}+2)$ | 9 | 未登録 |  |
| `fam:cylinder:k[w=4]:off0` | cylinder (k[w=4]) の $M^*(p_{\min}+0)$ | 8 | 未登録 |  |
| `hard:5` | spinal tree $S_k^*$ の $M^*(p_{\min})$（段差の内側 $k=8..15$） | 8 | 未登録 |  |
| `slice:fib:M*_p_min+0:p8` | Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ の $p_{\min}=8$ 切片 | 8 | 未登録 |  |
| `slice:fib:M*_p_min+0:p9` | Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ の $p_{\min}=9$ 切片 | 8 | 未登録 |  |
| `slice:fib:M*_p_min+1:p8` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ の $p_{\min}=8$ 切片 | 8 | 未登録 |  |
| `slice:fib:M*_p_min+1:p9` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ の $p_{\min}=9$ 切片 | 8 | 未登録 |  |
| `slice:fib:M*_p_min+2:p8` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=8$ 切片 | 8 | **既知（全項一致）** | [A004767] a(n) = 4*n + 3.; [A172338] a(n) = floor(n*(sqrt(5)+sqrt(3))). |
| `slice:fib:M*_p_min+2:p9` | Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=9$ 切片 | 8 | **既知（全項一致）** | [A016813] a(n) = 4*n + 1.; [A004766] Numbers whose binary expansion ends 01. |
| `fam:cylinder:k[w=4]:off1` | cylinder (k[w=4]) の $M^*(p_{\min}+1)$ | 7 | 未登録 |  |
| `fam:cylinder:k[w=4]:off2` | cylinder (k[w=4]) の $M^*(p_{\min}+2)$ | 7 | 未登録 |  |
| `fam:cylinder:k[w=5]:off0` | cylinder (k[w=5]) の $M^*(p_{\min}+0)$ | 6 | 未登録 |  |
| `fam:cylinder:k[w=5]:off1` | cylinder (k[w=5]) の $M^*(p_{\min}+1)$ | 6 | 未登録 |  |
| `fam:cylinder:k[w=5]:off2` | cylinder (k[w=5]) の $M^*(p_{\min}+2)$ | 6 | 未登録 |  |
| `fam:cylinder:k[w=6]:off0` | cylinder (k[w=6]) の $M^*(p_{\min}+0)$ | 6 | 未登録 |  |
| `fam:cylinder:k[w=6]:off1` | cylinder (k[w=6]) の $M^*(p_{\min}+1)$ | 6 | 未登録 |  |
| `fam:cylinder:k[w=7]:off0` | cylinder (k[w=7]) の $M^*(p_{\min}+0)$ | 6 | 未登録 |  |
| `fam:cylinder:k[w=7]:off1` | cylinder (k[w=7]) の $M^*(p_{\min}+1)$ | 6 | 未登録 |  |
| `hard:1` | 完全二分木の $M^*(T_h)$ | 6 | 未登録 |  |
| `hard:2` | ピラミッドの $M^*(P_h, p_{\min})$ | 6 | 未登録 |  |
| `hard:8` | 四つ組形式 $\mathrm{BB}^4_{\mathrm{rev}}(k)$ | 6 | **既知（全項一致）** | [A102588] Absolute row sums of triangle A102587, which is equal to the matrix in |
| `pascal:M*_p_min+0` | Pascal 型メモ化 DAGの $M^*(p_{\min})$ | 6 | **既知（全項一致）** | [A306902] Sum over all partitions of n of the bitwise OR of the parts.; [A058682] a(n) = p(0) + p(1) + ... + p(n) - n - 1, where p = partition numbers,  |
| `pascal:M*_p_min+1` | Pascal 型メモ化 DAGの $M^*(p_{\min}+1)$ | 6 | 未登録 |  |
| `pascal:M*_p_min+2` | Pascal 型メモ化 DAGの $M^*(p_{\min}+2)$ | 6 | **既知（全項一致）** | [A181497] a(n) is the smallest m such that A056753(m) = 2*n + 1.; [A236632] Sum of all divisors of all positive integers <= n minus the total numb |
| `scaling:edit_distance:final_live_bits` | edit_distance の final_live_bits | 6 | 未登録 |  |
| `scaling:edit_distance:steps` | edit_distance の steps | 6 | 未登録 |  |
| `scaling:knapsack:final_live_bits` | knapsack の final_live_bits | 6 | 未登録 |  |
| `scaling:knapsack:steps` | knapsack の steps | 6 | 未登録 |  |
| `scaling:lcs:final_live_bits` | lcs の final_live_bits | 6 | 未登録 |  |
| `scaling:lcs:steps` | lcs の steps | 6 | 未登録 |  |
| `slice:chain:M*_p_min+0:p5` | 鎖の $M^*(p_{\min})$ の $p_{\min}=5$ 切片 | 6 | 未登録 |  |
| `slice:chain:M*_p_min+1:p5` | 鎖の $M^*(p_{\min}+1)$ の $p_{\min}=5$ 切片 | 6 | **既知（全項一致）** | [A004767] a(n) = 4*n + 3.; [A172338] a(n) = floor(n*(sqrt(5)+sqrt(3))). |
| `slice:chain:M*_p_min+2:p5` | 鎖の $M^*(p_{\min}+2)$ の $p_{\min}=5$ 切片 | 6 | **既知（全項一致）** | [A016813] a(n) = 4*n + 1.; [A001855] Sorting numbers: maximal number of comparisons for sorting n elements  |
| `fam:cylinder:k[w=6]:off2` | cylinder (k[w=6]) の $M^*(p_{\min}+2)$ | 5 | 未登録 |  |
| `fam:cylinder:k[w=7]:off2` | cylinder (k[w=7]) の $M^*(p_{\min}+2)$ | 5 | 未登録 |  |
| `hard:3` | ピラミッドの $M^*(P_h, p_{\min})$（段差前のみ $h=1..5$） | 5 | 未登録 |  |
| `hard:7` | $\Sigma_{\mathrm{rev}}(k)$（可逆 BB の最大 1 の個数） | 5 | **既知（全項一致）** | [A000079] Powers of 2: a(n) = 2^n.; [A011782] Coefficients of expansion of (1-x)/(1-2*x) in powers of x. |
| `reach:e0` | $\mathrm{reach}(p, e=0)$ | 5 | **既知（全項一致）** | [A000079] Powers of 2: a(n) = 2^n.; [A011782] Coefficients of expansion of (1-x)/(1-2*x) in powers of x. |
| `reach:e1` | $\mathrm{reach}(p, e=1)$ | 5 | **既知（全項一致）** | [A003945] Expansion of g.f. (1+x)/(1-2*x).; [A163876] Number of reduced words of length n in Coxeter group on 3 generators S |
| `reach:e2` | $\mathrm{reach}(p, e=2)$ | 5 | **既知（全項一致）** | [A151821] Powers of 2, omitting 2 itself.; [A005934] Highly powerful numbers: numbers with record value of the product of t |
| `reach:e3` | $\mathrm{reach}(p, e=3)$ | 5 | **既知（全項一致）** | [A146523] Binomial transform of A010685.; [A226311] a(n+5) = a(n+4)+a(n+3)+a(n+2)+a(n+1)+2*a(n) with a(0)=2, a(1)=1, a(2)= |
| `reach:e4` | $\mathrm{reach}(p, e=4)$ | 5 | **既知（全項一致）** | [A082505] a(n) = sum of (n-1)-th row terms of triangle A134059.; [A330997] Sorted list containing the least number with each possible nonzero num |
| `slice:fib:M*_p_min+0:p10` | fib の M*_p_min+0 の $p_{\min}=10$ 切片 | 5 | — |  |
| `slice:fib:M*_p_min+1:p10` | fib の M*_p_min+1 の $p_{\min}=10$ 切片 | 5 | — |  |
| `slice:fib:M*_p_min+2:p10` | fib の M*_p_min+2 の $p_{\min}=10$ 切片 | 5 | — |  |

## 全項一致したもの（既知として早期棄却の材料にする）

**信頼度の読み方**: 「全項一致」は*こちらの全項が OEIS 側の数列の連続部分に現れる*という意味であって、同じ数列だという証明ではない。項数が少ないほど偶然の一致が増える:

- 10 項以上 … **強**（偶然はまず無い）
- 7〜9 項 … 中（別系列の可能性が残る）
- 6 項以下 … **弱**（短い並びは多くの数列に現れる。棄却の根拠にしてよいが、『同じ数列だ』と書いてはいけない）

- **Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=8$ 切片**（`slice:fib:M*_p_min+2:p8`, 8 項 → 信頼度 中、**自明な型: 等差（公差 4） → OEIS ヒットは既知性の根拠にならない**, 出典 `data/exp04_fib.csv`）
  - 先頭: `[43, 47, 51, 55, 59, 63, 67, 71]`
  - [A004767] a(n) = 4*n + 3.; [A172338] a(n) = floor(n*(sqrt(5)+sqrt(3))).
- **Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=9$ 切片**（`slice:fib:M*_p_min+2:p9`, 8 項 → 信頼度 中、**自明な型: 等差（公差 4） → OEIS ヒットは既知性の根拠にならない**, 出典 `data/exp04_fib.csv`）
  - 先頭: `[73, 77, 81, 85, 89, 93, 97, 101]`
  - [A016813] a(n) = 4*n + 1.; [A004766] Numbers whose binary expansion ends 01.
- **四つ組形式 $\mathrm{BB}^4_{\mathrm{rev}}(k)$**（`hard:8`, 6 項 → 信頼度 **弱**, 出典 `scripts/exp_guess_sequences.py`）
  - 先頭: `[2, 4, 6, 12, 22, 34]`
  - [A102588] Absolute row sums of triangle A102587, which is equal to the matrix in
- **Pascal 型メモ化 DAGの $M^*(p_{\min})$**（`pascal:M*_p_min+0`, 6 項 → 信頼度 **弱**, 出典 `data/exp04_pascal.csv`）
  - 先頭: `[0, 1, 3, 7, 13, 23]`
  - [A306902] Sum over all partitions of n of the bitwise OR of the parts.; [A058682] a(n) = p(0) + p(1) + ... + p(n) - n - 1, where p = partition numbers, 
- **Pascal 型メモ化 DAGの $M^*(p_{\min}+2)$**（`pascal:M*_p_min+2`, 6 項 → 信頼度 **弱**, 出典 `data/exp04_pascal.csv`）
  - 先頭: `[0, 1, 3, 7, 11, 19]`
  - [A181497] a(n) is the smallest m such that A056753(m) = 2*n + 1.; [A236632] Sum of all divisors of all positive integers <= n minus the total numb
- **鎖の $M^*(p_{\min}+1)$ の $p_{\min}=5$ 切片**（`slice:chain:M*_p_min+1:p5`, 6 項 → 信頼度 **弱**、**自明な型: 等差（公差 4） → OEIS ヒットは既知性の根拠にならない**, 出典 `data/exp01_trees.csv`）
  - 先頭: `[23, 27, 31, 35, 39, 43]`
  - [A004767] a(n) = 4*n + 3.; [A172338] a(n) = floor(n*(sqrt(5)+sqrt(3))).
- **鎖の $M^*(p_{\min}+2)$ の $p_{\min}=5$ 切片**（`slice:chain:M*_p_min+2:p5`, 6 項 → 信頼度 **弱**、**自明な型: 等差（公差 4） → OEIS ヒットは既知性の根拠にならない**, 出典 `data/exp01_trees.csv`）
  - 先頭: `[21, 25, 29, 33, 37, 41]`
  - [A016813] a(n) = 4*n + 1.; [A001855] Sorting numbers: maximal number of comparisons for sorting n elements 
- **$\Sigma_{\mathrm{rev}}(k)$（可逆 BB の最大 1 の個数）**（`hard:7`, 5 項 → 信頼度 **弱**、**自明な型: 等比（公比 2） → OEIS ヒットは既知性の根拠にならない**, 出典 `scripts/exp_guess_sequences.py`）
  - 先頭: `[1, 2, 4, 8, 16]`
  - [A000079] Powers of 2: a(n) = 2^n.; [A011782] Coefficients of expansion of (1-x)/(1-2*x) in powers of x.
- **$\mathrm{reach}(p, e=0)$**（`reach:e0`, 5 項 → 信頼度 **弱**、**自明な型: 等比（公比 2） → OEIS ヒットは既知性の根拠にならない**, 出典 `data/exp03_reach.csv`）
  - 先頭: `[1, 2, 4, 8, 16]`
  - [A000079] Powers of 2: a(n) = 2^n.; [A011782] Coefficients of expansion of (1-x)/(1-2*x) in powers of x.
- **$\mathrm{reach}(p, e=1)$**（`reach:e1`, 5 項 → 信頼度 **弱**, 出典 `data/exp03_reach.csv`）
  - 先頭: `[1, 3, 6, 12, 24]`
  - [A003945] Expansion of g.f. (1+x)/(1-2*x).; [A163876] Number of reduced words of length n in Coxeter group on 3 generators S
- **$\mathrm{reach}(p, e=2)$**（`reach:e2`, 5 項 → 信頼度 **弱**, 出典 `data/exp03_reach.csv`）
  - 先頭: `[1, 4, 8, 16, 32]`
  - [A151821] Powers of 2, omitting 2 itself.; [A005934] Highly powerful numbers: numbers with record value of the product of t
- **$\mathrm{reach}(p, e=3)$**（`reach:e3`, 5 項 → 信頼度 **弱**, 出典 `data/exp03_reach.csv`）
  - 先頭: `[1, 5, 10, 20, 40]`
  - [A146523] Binomial transform of A010685.; [A226311] a(n+5) = a(n+4)+a(n+3)+a(n+2)+a(n+1)+2*a(n) with a(0)=2, a(1)=1, a(2)=
- **$\mathrm{reach}(p, e=4)$**（`reach:e4`, 5 項 → 信頼度 **弱**, 出典 `data/exp03_reach.csv`）
  - 先頭: `[1, 6, 12, 24, 48]`
  - [A082505] a(n) = sum of (n-1)-th row terms of triangle A134059.; [A330997] Sorted list containing the least number with each possible nonzero num

## 先頭だけ一致したもの（**別物**。当てはめ崩壊の実例として記録）

（なし）

## 既知事実台帳との突き合わせ

OEIS に載っている＝**既に知られている**なので、早期棄却の材料になる。
`docs/22_known_facts_ledger.md` に該当項目があるかを機械的に照合した
（A 番号の文字列一致。**台帳は書き換えていない**——追記は人間の判断）。

⚠ **照合は A 番号の文字列一致だけ**なので、台帳が『概念として』記載していてもA 番号を書いていなければ「記載なし」と出る。実例: `reach:e*` は台帳 KF-03（$\mathrm{reach}(p)=2^{p-1}$、Královič 2001）が該当するが、A 番号が書かれていないので下では「記載なし」になっている。**この一覧を根拠に台帳へ追記してはいけない。**

- `slice:fib:M*_p_min+2:p8`: **等差（公差 4）** なので OEIS に載っているのは当然。['A004767', 'A172338'] は**台帳に足す対象ではない**
- `slice:fib:M*_p_min+2:p9`: **等差（公差 4）** なので OEIS に載っているのは当然。['A016813', 'A004766'] は**台帳に足す対象ではない**
- `hard:8`（信頼度 弱）: ['A102588'] は台帳に**記載なし**。ただし項数が少なく偶然の一致でありうるので、台帳に足す前に一次情報で確かめること
- `pascal:M*_p_min+0`（信頼度 弱）: ['A306902', 'A058682', 'A103116'] は台帳に**記載なし**。ただし項数が少なく偶然の一致でありうるので、台帳に足す前に一次情報で確かめること
- `pascal:M*_p_min+2`（信頼度 弱）: ['A181497', 'A236632', 'A265323'] は台帳に**記載なし**。ただし項数が少なく偶然の一致でありうるので、台帳に足す前に一次情報で確かめること
- `slice:chain:M*_p_min+1:p5`: **等差（公差 4）** なので OEIS に載っているのは当然。['A004767', 'A172338'] は**台帳に足す対象ではない**
- `slice:chain:M*_p_min+2:p5`: **等差（公差 4）** なので OEIS に載っているのは当然。['A016813', 'A001855'] は**台帳に足す対象ではない**
- `hard:7`: **等比（公比 2）** なので OEIS に載っているのは当然。['A000079', 'A011782'] は**台帳に足す対象ではない**
- `reach:e0`: **等比（公比 2）** なので OEIS に載っているのは当然。['A000079', 'A011782'] は**台帳に足す対象ではない**
- `reach:e1`（信頼度 弱）: ['A003945', 'A163876', 'A367217'] は台帳に**記載なし**。ただし項数が少なく偶然の一致でありうるので、台帳に足す前に一次情報で確かめること
- `reach:e2`（信頼度 弱）: ['A151821', 'A005934', 'A085629'] は台帳に**記載なし**。ただし項数が少なく偶然の一致でありうるので、台帳に足す前に一次情報で確かめること
- `reach:e3`（信頼度 弱）: ['A146523', 'A226311', 'A049948'] は台帳に**記載なし**。ただし項数が少なく偶然の一致でありうるので、台帳に足す前に一次情報で確かめること
- `reach:e4`（信頼度 弱）: ['A082505', 'A330997', 'A049964'] は台帳に**記載なし**。ただし項数が少なく偶然の一致でありうるので、台帳に足す前に一次情報で確かめること

