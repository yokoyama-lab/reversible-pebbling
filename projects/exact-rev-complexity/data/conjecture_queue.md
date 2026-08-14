# 予想キュー（自動生成・手編集禁止）

生成: `python3 scripts/conjecture_queue.py`／推測は `scripts/holonomic.py`
（held-out 検証を通らない推測は出さない。当てはめ崩壊の再発防止）

> **ここに出るのはすべて 層3（予想）である。** held-out を通っていても証明ではない。
> **層の昇格は人間が判断する。**このスクリプトは昇格しない。

**使い方**: 表は**検証費用の安い順**。各行の「次の点」を計算して予測値と比べれば、
その予想の真偽がその場で決まる。外れたら予想を捨てる（それも成果）。

**要約**: `exact` かつ 5 項以上の 64 本のうち、**1 本で漸化式が見つかった**（＝予想 1 本）。残り 63 本は漸化式なし・判定不能。

## 予想（費用の安い順）

| # | 数列 | 項数 | 予測: 次の点 | 漸化式 | 検証に要る計算 | 費用 | 層 |
|---:|---|---:|---|---|---|---|---|
| 1 | fib の M*_p_min+1 の $p_{\min}=10$ 切片<br/>`slice:fib:M*_p_min+1:p10` | 11 | **n=44 で 191** | holonomic: (-1*n +1)*a(n) + (+2*n -2)*a(n+1) + (-1*n +1)*a(n+2) = 0 | n=44 の値を計算（出典 `data/sequences_extended.csv（追加計算）` の続き） | 387.9s | 3 |

### 各予想の詳細

#### 1. fib の M*_p_min+1 の $p_{\min}=10$ 切片（`slice:fib:M*_p_min+1:p10`） — holonomic

- 出典: `data/sequences_extended.csv（追加計算）`、添字 n = 33..43（11 項）
- 値: `[107, 113, 119, 127, 135, 143, 151, 159, 167, 175, 183]`
- **規則（予想）**: (-1*n +1)*a(n) + (+2*n -2)*a(n+1) + (-1*n +1)*a(n+2) = 0
- **予測**: n=44 のとき **191**
- 検証費用の見積: 直近 258.59s、比 1.5× から外挿

- 注: **追加計算だけで得た新しい切片**（表にはまだ無い）

## 漸化式が出なかったもの

「漸化式なし」は holonomic でない証拠ではない（探索範囲と項数の問題）。
**判定不能**は項数不足なので、数列を伸ばすのが次の手。

| 数列 | 項数 | 判定 |
|---|---:|---|
| Fibonacci 型メモ化 DAGの $M^*(p_{\min})$<br/>`fib:M*_p_min+0` | 43 | **区分的だと分かっている**（$p_{\min}$ 切片が存在する）ので、この数列からは予想を出さない。切片版を見ること |
| Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$<br/>`fib:M*_p_min+1` | 43 | **区分的だと分かっている**（$p_{\min}$ 切片が存在する）ので、この数列からは予想を出さない。切片版を見ること |
| Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$<br/>`fib:M*_p_min+2` | 43 | **区分的だと分かっている**（$p_{\min}$ 切片が存在する）ので、この数列からは予想を出さない。切片版を見ること |
| cylinder (k[w=2]) の $M^*(p_{\min}+0)$<br/>`fam:cylinder:k[w=2]:off0` | 17 | **区分的だと分かっている**（$p_{\min}$ 切片が存在する）ので、この数列からは予想を出さない。切片版を見ること |
| cylinder (k[w=2]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=2]:off1` | 17 | **区分的だと分かっている**（$p_{\min}$ 切片が存在する）ので、この数列からは予想を出さない。切片版を見ること |
| cylinder (k[w=2]) の $M^*(p_{\min}+2)$<br/>`fam:cylinder:k[w=2]:off2` | 17 | **区分的だと分かっている**（$p_{\min}$ 切片が存在する）ので、この数列からは予想を出さない。切片版を見ること |
| 鎖の $M^*(p_{\min})$<br/>`hard:0` | 16 | 漸化式なし（$order\le4$, $degree\le4$ の 11 組を確証つきで排除） |
| spinal tree $S_k^*$ の $M^*(p_{\min})$<br/>`hard:4` | 16 | 漸化式なし（$order\le4$, $degree\le4$ の 11 組を確証つきで排除） |
| spinal tree $S_k^*$ の $M^*(p_{\min}+1)$<br/>`hard:6` | 16 | 漸化式なし（$order\le4$, $degree\le4$ の 11 組を確証つきで排除） |
| 飽和族の $M^*(p_{\min})$<br/>`saturation:M*_p_min` | 16 | 漸化式なし（$order\le4$, $degree\le4$ の 11 組を確証つきで排除） |
| 飽和族の $p_{\min}$<br/>`saturation:p_min` | 16 | 漸化式なし（$order\le4$, $degree\le4$ の 11 組を確証つきで排除） |
| 鎖の $M^*(p_{\min})$<br/>`chain:M*_p_min+0` | 14 | **区分的だと分かっている**（$p_{\min}$ 切片が存在する）ので、この数列からは予想を出さない。切片版を見ること |
| 鎖の $M^*(p_{\min}+1)$<br/>`chain:M*_p_min+1` | 14 | **区分的だと分かっている**（$p_{\min}$ 切片が存在する）ので、この数列からは予想を出さない。切片版を見ること |
| 鎖の $M^*(p_{\min}+2)$<br/>`chain:M*_p_min+2` | 14 | **区分的だと分かっている**（$p_{\min}$ 切片が存在する）ので、この数列からは予想を出さない。切片版を見ること |
| cylinder (k[w=3]) の $M^*(p_{\min}+0)$<br/>`fam:cylinder:k[w=3]:off0` | 11 | 漸化式なし（$order\le3$, $degree\le2$ の 6 組を確証つきで排除） |
| fib の M*_p_min+0 の $p_{\min}=10$ 切片<br/>`slice:fib:M*_p_min+0:p10` | 11 | 漸化式なし（$order\le3$, $degree\le2$ の 6 組を確証つきで排除） |
| fib の M*_p_min+2 の $p_{\min}=10$ 切片<br/>`slice:fib:M*_p_min+2:p10` | 11 | 漸化式なし（$order\le3$, $degree\le2$ の 6 組を確証つきで排除） |
| cylinder (k[w=3]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=3]:off1` | 10 | 漸化式なし（$order\le3$, $degree\le2$ の 5 組を確証つきで排除） |
| cylinder (k[w=3]) の $M^*(p_{\min}+2)$<br/>`fam:cylinder:k[w=3]:off2` | 9 | 漸化式なし（$order\le2$, $degree\le1$ の 3 組を確証つきで排除） |
| spinal tree $S_k^*$ の $M^*(p_{\min})$（段差の内側 $k=8..15$）<br/>`hard:5` | 8 | 漸化式なし（$order\le2$, $degree\le1$ の 3 組を確証つきで排除） |
| cylinder (k[w=4]) の $M^*(p_{\min}+0)$<br/>`fam:cylinder:k[w=4]:off0` | 8 | 漸化式なし（$order\le2$, $degree\le1$ の 3 組を確証つきで排除） |
| cylinder (k[w=2]) の $M^*(p_{\min}+0)$ の $p_{\min}=9$ 切片<br/>`slice:fam:cylinder:k[w=2]:off0:p9` | 8 | 漸化式なし（$order\le2$, $degree\le1$ の 3 組を確証つきで排除） |
| cylinder (k[w=2]) の $M^*(p_{\min}+1)$ の $p_{\min}=9$ 切片<br/>`slice:fam:cylinder:k[w=2]:off1:p9` | 8 | 漸化式なし（$order\le2$, $degree\le1$ の 3 組を確証つきで排除） |
| cylinder (k[w=2]) の $M^*(p_{\min}+2)$ の $p_{\min}=9$ 切片<br/>`slice:fam:cylinder:k[w=2]:off2:p9` | 8 | 切片が**閉じている**ため次の点が存在しない（予想は出せても 1 点計算では検証できない）。検証するなら**次の切片で同じ形が成り立つか**を見る |
| Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ の $p_{\min}=8$ 切片<br/>`slice:fib:M*_p_min+0:p8` | 8 | 漸化式なし（$order\le2$, $degree\le1$ の 3 組を確証つきで排除） |
| Fibonacci 型メモ化 DAGの $M^*(p_{\min})$ の $p_{\min}=9$ 切片<br/>`slice:fib:M*_p_min+0:p9` | 8 | 漸化式なし（$order\le2$, $degree\le1$ の 3 組を確証つきで排除） |
| Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ の $p_{\min}=8$ 切片<br/>`slice:fib:M*_p_min+1:p8` | 8 | 漸化式なし（$order\le2$, $degree\le1$ の 3 組を確証つきで排除） |
| Fibonacci 型メモ化 DAGの $M^*(p_{\min}+1)$ の $p_{\min}=9$ 切片<br/>`slice:fib:M*_p_min+1:p9` | 8 | 漸化式なし（$order\le2$, $degree\le1$ の 3 組を確証つきで排除） |
| Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=8$ 切片<br/>`slice:fib:M*_p_min+2:p8` | 8 | 切片が**閉じている**ため次の点が存在しない（予想は出せても 1 点計算では検証できない）。検証するなら**次の切片で同じ形が成り立つか**を見る |
| Fibonacci 型メモ化 DAGの $M^*(p_{\min}+2)$ の $p_{\min}=9$ 切片<br/>`slice:fib:M*_p_min+2:p9` | 8 | 切片が**閉じている**ため次の点が存在しない（予想は出せても 1 点計算では検証できない）。検証するなら**次の切片で同じ形が成り立つか**を見る |
| cylinder (k[w=4]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=4]:off1` | 7 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| cylinder (k[w=4]) の $M^*(p_{\min}+2)$<br/>`fam:cylinder:k[w=4]:off2` | 7 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| 完全二分木の $M^*(T_h)$<br/>`hard:1` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| ピラミッドの $M^*(P_h, p_{\min})$<br/>`hard:2` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| 四つ組形式 $\mathrm{BB}^4_{\mathrm{rev}}(k)$<br/>`hard:8` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| cylinder (k[w=5]) の $M^*(p_{\min}+0)$<br/>`fam:cylinder:k[w=5]:off0` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| cylinder (k[w=5]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=5]:off1` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| cylinder (k[w=5]) の $M^*(p_{\min}+2)$<br/>`fam:cylinder:k[w=5]:off2` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| cylinder (k[w=6]) の $M^*(p_{\min}+0)$<br/>`fam:cylinder:k[w=6]:off0` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| cylinder (k[w=6]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=6]:off1` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| cylinder (k[w=7]) の $M^*(p_{\min}+0)$<br/>`fam:cylinder:k[w=7]:off0` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| cylinder (k[w=7]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=7]:off1` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| Pascal 型メモ化 DAGの $M^*(p_{\min})$<br/>`pascal:M*_p_min+0` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| Pascal 型メモ化 DAGの $M^*(p_{\min}+1)$<br/>`pascal:M*_p_min+1` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| Pascal 型メモ化 DAGの $M^*(p_{\min}+2)$<br/>`pascal:M*_p_min+2` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| 鎖の $M^*(p_{\min})$ の $p_{\min}=5$ 切片<br/>`slice:chain:M*_p_min+0:p5` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| 鎖の $M^*(p_{\min}+1)$ の $p_{\min}=5$ 切片<br/>`slice:chain:M*_p_min+1:p5` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| 鎖の $M^*(p_{\min}+2)$ の $p_{\min}=5$ 切片<br/>`slice:chain:M*_p_min+2:p5` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| edit_distance の steps<br/>`scaling:edit_distance:steps` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| edit_distance の final_live_bits<br/>`scaling:edit_distance:final_live_bits` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| knapsack の steps<br/>`scaling:knapsack:steps` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| knapsack の final_live_bits<br/>`scaling:knapsack:final_live_bits` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| lcs の steps<br/>`scaling:lcs:steps` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| lcs の final_live_bits<br/>`scaling:lcs:final_live_bits` | 6 | 漸化式なし（$order\le1$, $degree\le0$ の 1 組を確証つきで排除） |
| ピラミッドの $M^*(P_h, p_{\min})$（段差前のみ $h=1..5$）<br/>`hard:3` | 5 | **判定不能**（項数 5 では確証つきで評価できる $(order,degree)$ が 1 組も無い）→ 数列を伸ばす |
| $\Sigma_{\mathrm{rev}}(k)$（可逆 BB の最大 1 の個数）<br/>`hard:7` | 5 | **判定不能**（項数 5 では確証つきで評価できる $(order,degree)$ が 1 組も無い）→ 数列を伸ばす |
| cylinder (k[w=6]) の $M^*(p_{\min}+2)$<br/>`fam:cylinder:k[w=6]:off2` | 5 | **判定不能**（項数 5 では確証つきで評価できる $(order,degree)$ が 1 組も無い）→ 数列を伸ばす |
| cylinder (k[w=7]) の $M^*(p_{\min}+2)$<br/>`fam:cylinder:k[w=7]:off2` | 5 | **判定不能**（項数 5 では確証つきで評価できる $(order,degree)$ が 1 組も無い）→ 数列を伸ばす |
| $\mathrm{reach}(p, e=0)$<br/>`reach:e0` | 5 | **判定不能**（項数 5 では確証つきで評価できる $(order,degree)$ が 1 組も無い）→ 数列を伸ばす |
| $\mathrm{reach}(p, e=1)$<br/>`reach:e1` | 5 | **判定不能**（項数 5 では確証つきで評価できる $(order,degree)$ が 1 組も無い）→ 数列を伸ばす |
| $\mathrm{reach}(p, e=2)$<br/>`reach:e2` | 5 | **判定不能**（項数 5 では確証つきで評価できる $(order,degree)$ が 1 組も無い）→ 数列を伸ばす |
| $\mathrm{reach}(p, e=3)$<br/>`reach:e3` | 5 | **判定不能**（項数 5 では確証つきで評価できる $(order,degree)$ が 1 組も無い）→ 数列を伸ばす |
| $\mathrm{reach}(p, e=4)$<br/>`reach:e4` | 5 | **判定不能**（項数 5 では確証つきで評価できる $(order,degree)$ が 1 組も無い）→ 数列を伸ばす |

## 切片をまたぐ規則（1 本の切片より強い予想）

（該当なし）

## 所見（なぜ予想が少ないのか）

1. **この族の数列は本質的に区分的である。** $M^*(G,p_{\min})$ は $p_{\min}$ が上がる位置で**値が減る**（鎖 $n=9$、spinal $k=8,16$、fib $n=17,25$ など。段差は 2 冪の位置に来る）。区分をまたぐ数列に単一の漸化式が成り立つ理由は無いので、「漸化式なし」は失敗ではなく**構造の反映**である。
2. **切片は短い。** 段差が 2 冪で来るため、$p_{\min}$ を固定した切片の長さも 2 冪でしか伸びない。holonomic は $(r{+}1)(d{+}1)+r+\mathrm{slack}$ 項を要求するので、切片が 8 項では $(1,1)$ か $(2,0)$ 程度しか評価できない。
3. したがって**律速は項数**であり、計算時間を使う先は「新しい族を増やす」ことより「既存の切片を伸ばす」ことである。

### 末尾パターンの関門（2026-08-10 追加）

末尾 2 項を隠す held-out は**連の内側**を当てているだけで、**連がいつ終わるか**を検定していない（破れは定義上データの外で起きる）。そこで次の 2 つを追加の関門にした:

1. **遡及破れ検定**: その数列自身の既知の破れ点それぞれについて、直前までの接頭辞だけを手法に与え、外さないかを見る。1 つでも外したら出さない。
2. **前科の検定**: 末尾の連の長さが、過去に破れた連の最長以下なら出さない（同じ長さの連が既に破れているのに外挿するのは筋が通らない）。

通過した予想にも、連の履歴を「前科」として必ず併記する。

## 次に計算すべき点（判定不能を解消するのに必要な項数）

各行は「あと何項計算すれば、その $(order,degree)$ を**確証つきで**評価できるか」。
`slack=3`（推測に使わない検証式を 3 本残す）で計算した。

| 数列 | 現在 | (1,1) | (2,1) | (2,2) | (3,2) | (3,3) |
|---|---:|---:|---:|---:|---:|---:|
| cylinder (k[w=3]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=3]:off1` | 10 | ✅ | **+1** | +4 | +8 | +12 |
| cylinder (k[w=4]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=4]:off1` | 7 | **+1** | +4 | +7 | +11 | +15 |
| cylinder (k[w=4]) の $M^*(p_{\min}+2)$<br/>`fam:cylinder:k[w=4]:off2` | 7 | **+1** | +4 | +7 | +11 | +15 |
| 鎖の $M^*(p_{\min})$<br/>`hard:0` | 16 | ✅ | ✅ | ✅ | **+2** | +6 |
| spinal tree $S_k^*$ の $M^*(p_{\min})$<br/>`hard:4` | 16 | ✅ | ✅ | ✅ | **+2** | +6 |
| spinal tree $S_k^*$ の $M^*(p_{\min}+1)$<br/>`hard:6` | 16 | ✅ | ✅ | ✅ | **+2** | +6 |
| 飽和族の $M^*(p_{\min})$<br/>`saturation:M*_p_min` | 16 | ✅ | ✅ | ✅ | **+2** | +6 |
| 飽和族の $p_{\min}$<br/>`saturation:p_min` | 16 | ✅ | ✅ | ✅ | **+2** | +6 |
| cylinder (k[w=3]) の $M^*(p_{\min}+2)$<br/>`fam:cylinder:k[w=3]:off2` | 9 | ✅ | **+2** | +5 | +9 | +13 |
| 完全二分木の $M^*(T_h)$<br/>`hard:1` | 6 | **+2** | +5 | +8 | +12 | +16 |
| ピラミッドの $M^*(P_h, p_{\min})$<br/>`hard:2` | 6 | **+2** | +5 | +8 | +12 | +16 |
| 四つ組形式 $\mathrm{BB}^4_{\mathrm{rev}}(k)$<br/>`hard:8` | 6 | **+2** | +5 | +8 | +12 | +16 |
| cylinder (k[w=5]) の $M^*(p_{\min}+0)$<br/>`fam:cylinder:k[w=5]:off0` | 6 | **+2** | +5 | +8 | +12 | +16 |
| cylinder (k[w=5]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=5]:off1` | 6 | **+2** | +5 | +8 | +12 | +16 |
| cylinder (k[w=5]) の $M^*(p_{\min}+2)$<br/>`fam:cylinder:k[w=5]:off2` | 6 | **+2** | +5 | +8 | +12 | +16 |
| cylinder (k[w=6]) の $M^*(p_{\min}+0)$<br/>`fam:cylinder:k[w=6]:off0` | 6 | **+2** | +5 | +8 | +12 | +16 |
| cylinder (k[w=6]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=6]:off1` | 6 | **+2** | +5 | +8 | +12 | +16 |
| cylinder (k[w=7]) の $M^*(p_{\min}+0)$<br/>`fam:cylinder:k[w=7]:off0` | 6 | **+2** | +5 | +8 | +12 | +16 |
| cylinder (k[w=7]) の $M^*(p_{\min}+1)$<br/>`fam:cylinder:k[w=7]:off1` | 6 | **+2** | +5 | +8 | +12 | +16 |
| Pascal 型メモ化 DAGの $M^*(p_{\min})$<br/>`pascal:M*_p_min+0` | 6 | **+2** | +5 | +8 | +12 | +16 |
| Pascal 型メモ化 DAGの $M^*(p_{\min}+1)$<br/>`pascal:M*_p_min+1` | 6 | **+2** | +5 | +8 | +12 | +16 |
| Pascal 型メモ化 DAGの $M^*(p_{\min}+2)$<br/>`pascal:M*_p_min+2` | 6 | **+2** | +5 | +8 | +12 | +16 |
| 鎖の $M^*(p_{\min})$ の $p_{\min}=5$ 切片<br/>`slice:chain:M*_p_min+0:p5` | 6 | **+2** | +5 | +8 | +12 | +16 |
| 鎖の $M^*(p_{\min}+1)$ の $p_{\min}=5$ 切片<br/>`slice:chain:M*_p_min+1:p5` | 6 | **+2** | +5 | +8 | +12 | +16 |
| 鎖の $M^*(p_{\min}+2)$ の $p_{\min}=5$ 切片<br/>`slice:chain:M*_p_min+2:p5` | 6 | **+2** | +5 | +8 | +12 | +16 |
| edit_distance の steps<br/>`scaling:edit_distance:steps` | 6 | **+2** | +5 | +8 | +12 | +16 |
| edit_distance の final_live_bits<br/>`scaling:edit_distance:final_live_bits` | 6 | **+2** | +5 | +8 | +12 | +16 |
| knapsack の steps<br/>`scaling:knapsack:steps` | 6 | **+2** | +5 | +8 | +12 | +16 |

**読み方**: 「✅」は既にその $(order,degree)$ を評価済み（＝その範囲に漸化式は無いと確証つきで言えた）。「+k」はあと k 項要る。**+1 か +2 の行が費用対効果の高い計算依頼**である。

延長は `python3 scripts/extend_sequences.py fib --from A --to B` などで行い、結果は `data/sequences_extended.csv` に追記されて自動的にこの表へ合流する。

