# 左端 `n = 2^{S−1}` の下界と、増大率の移送 — 報告

*worktree `reversible-pebbling-lean-lowend` / branch `rate-transfer-lowend` / 2026-09-03*

## 決定点への答え（3行）

1. **閉じた。** `T(n, S_min(n)) = n^{log₂ c + o(1)}` を Lean 内で無条件に証明した
   （`RevPebbling.RateTransferLow.tendsto_log_gameT_Smin`、`sorry` ゼロ・標準3公理）。
2. 左端の下界は **`F(2^r+1, r+3) ≤ H(2^{r+2}, r+3)`（容量の鳩の巣）** に帰着し、
   そこから既存の `DispersionReal.dispersion_real` をそのまま使って
   `2·(2/λ)^{1/q}` を底とする幾何下界を得た。底の上限が `c` であることは `Final` の既定理。
3. **依頼の見立て（(4) `halfMarginals_countLe` を実際の行族に接続して `D_S` の
   supersolution を回す）は使わなかった。** 不要だったので接続していない（理由は下記）。

---

## 1. 証明した定理（成果物 `RevPebbling/RateTransferLow.lean`、906 行、新規）

主定理:

```lean
theorem RevPebbling.RateTransferLow.tendsto_log_gameT_Smin :
    Filter.Tendsto (fun n : ℕ => Real.log (gameT n (Smin n)) / Real.log n) Filter.atTop
      (nhds (Real.log RevPebbling.BlockSim.c / Real.log 2))
```

`gameT` は `GameCompleteCost.gameT`（完全計算の最適手数）、`Smin` は
`RateTransfer.Smin`（最小空間 budget）、`c` は `BlockSim.c`（Knill 定数）。

主要な中間定理:

| 定理 | 内容 |
|---|---|
| `cap` / `cap_sat` / `cap_full` | 容量 `cap S K = Σ_{i≤S} min(2^{i−1}, K)`。`cap (r+3) (2^r) = 2^{r+2} − 1` |
| `fpre_le_of_halfReachIn` | **容量の鳩の巣**: `HalfReachIn n S t → cap S K < n → Fpre (rowIter s) (K+1) ≤ t`（`S ≤ s+2`） |
| `fpre_le_gameH_left` | **左端の組合せ論的半分**: `Fpre (rowIter (r+1)) (2^r + 1) ≤ gameH (2^{r+2}) (r+3)` |
| `sum_ge_of_countLe` / `fpre_ge_of_countLe` | **計数→費用**: `2·(k − C_S(v))(v+1) ≤ F(k+1,S)` |
| `smerge_sum` / `sum_zipWith_ge` / `rowIter_sum_double` / `fRow_double` | 行和は毎段 2 倍以上: `2 f_S + 1 ≤ f_{S+1}`（`S ≥ 2`） |
| `sumF_le_two_mul` | `Σ_{i=1}^{S} f_i ≤ 2 f_S`（右端の上界を `f_S` に潰す） |
| `gameT_left_eq` | 左端でも `T = 2H` |
| `gameH_left_ge` | **左端の解析的半分**: 許容パラメータ `(M,q,λ,θ)` ごとに `(2Mλ)^{−1/q}·(2(2/λ)^{1/q})^r ≤ H(2^{r+2}, r+3)` |
| `exists_admissible_gt` | `y < c` なる `y` に対し `y < 2(2/λ)^{1/q}` となる許容パラメータが存在（底の上限が `c`） |
| `eventually_pow_le_gameT_left` | `0 < y < c` なら十分大きい `r` で `y^r ≤ T(2^{r+2}, r+3)` |
| `one_le_Smin` / `two_pow_Smin_sub_one_le` / `three_le_Smin` / `tendsto_Smin` / `log_n_bounds` | 最小空間区間の構造 |
| `gameT_left_le` / `gameT_Smin_le` / `two_le_gameT_Smin` | 区間内の挟み撃ち（`RateTransfer.gameT_mono_len` と `gameT_full` を使用） |

### 証明の筋（依頼の見立てとの差分）

依頼の見立ては「(4) を行族に接続して `D_S(x) = S + Σ_{i≤S} C_i(⌊x/2⌋)` を得て、
`D_S` に対して dispersion を回す」だった。**この道は取っていない。**

⚠ **訂正（2026-09-03、初版の記述を撤回）**: 初版はここに「`D_S` は下位の行だけで
`2^{S−1} − 1` に達するので、この道は塞がっている」と書いた。**これは誤りである。**
潰れるのは自明上界 `C_i ≤ 2^{i−1} − 1` を使ったときだけで、dispersion 上界
`C_i(v) ≤ M v^q λ^i` は `i` について幾何的なので、`λ < 1/q − log₂ρ` の下で
`Σ_{i≤S} C_i(x_S/2) = O(2^{qS(λ+log₂ρ)}) = o(2^S)` になる。Lean の外で実測しても、
`D_S(x_S)/2^{S−1}` は `S` とともに減る（λ=0.30 で S=12,16,20,24 に対し
0.483, 0.307, 0.279, 0.227）。**原稿 thm:complete の証明のこの段は正しい。**
しかも原稿の下界 `(2^{S−1} − D_S(x_S))·x_S` は本ファイルの下界より**強い**
（実測で `H(2^{S−1},S)` の約 0.45 倍。本ファイルの鳩の巣は約 0.20 倍）。

取らなかった本当の理由は塞がりではなく**費用**である。`D_S` の道は
「`H` の周辺費用列が `F(·,i)` の周辺費用列の整列多重集合和である」という
離散凸の infimal convolution の同定を、実際の行族に対して必要とする。
それが高価な未形式化部分であり、Lean には一切入っていない。
鳩の巣はこの同定を丸ごと回避する（最上段の行しか登場しない）。取った道はこう:

* (H) を展開すると半到達は checkpoint 列 `m_S, …, m_1`（`m_i ≤ 2^{i−1}`、費用 `Σ_i F(m_i, i)`）。
  **全部が `≤ K` なら鎖は `cap S K` 以下**。`K = 2^r`, `S = r+3`, `n = 2^{r+2}` で
  `cap = 2^{r+2} − 1` とちょうど 1 だけ足りないので、ある `m_i > K` が確定する。
* その 1 本の checkpoint だけを残し、残りを捨てる（`Fpre_antitone_chain` で最上段の行に落とす）。
  → **和が消えて、最上段の行の prefix `F(2^r+1, S)` だけになる。**
* prefix 和は `C_S(v)` の上界（既存 `dispersion_real`）でそのまま下から押さえられる。

捨てた分は定数倍の損失にとどまる。Python 独立実装（`gen`/`rowIter` を Lean 定義から再実装し、
`f_S = 3,9,25,71,193` で一致を確認）で `r = 1..19` を計算すると

| r | `F(2^r+1, r+3)` | `H(2^{r+2}, r+3)` | 比 |
|---|---|---|---|
| 1 | 5 | 12 | 0.417 |
| 5 | 123 | 546 | 0.225 |
| 10 | 13933 | 67757 | 0.206 |
| 15 | 1631261 | 8125774 | 0.201 |
| 19 | 72485475 | 368177074 | 0.197 |

比が `S` に対して安定（≈0.20）なので、増大率は損なわれない。

**`HalfReachMerge`（(4)）は結果として使っていない。** 実際の行族との接続は依然として存在しない。
これは「(4) が間違っている」という主張ではなく、「左端を閉じるのに要らなかった」という報告である。

---

## 2. `#print axioms` の実測結果

```
'RevPebbling.RateTransferLow.tendsto_log_gameT_Smin'      : [propext, Classical.choice, Quot.sound]
'RevPebbling.RateTransferLow.fpre_le_of_halfReachIn'      : [propext, Classical.choice, Quot.sound]
'RevPebbling.RateTransferLow.fpre_le_gameH_left'          : [propext, Classical.choice, Quot.sound]
'RevPebbling.RateTransferLow.fpre_ge_of_countLe'          : [propext, Classical.choice, Quot.sound]
'RevPebbling.RateTransferLow.gameH_left_ge'               : [propext, Classical.choice, Quot.sound]
'RevPebbling.RateTransferLow.exists_admissible_gt'        : [propext, Classical.choice, Quot.sound]
'RevPebbling.RateTransferLow.eventually_pow_le_gameT_left': [propext, Classical.choice, Quot.sound]
'RevPebbling.RateTransferLow.sumF_le_two_mul'             : [propext, Classical.choice, Quot.sound]
'RevPebbling.RateTransferLow.cap_full'                    : [propext, Quot.sound]
```

`sorry` は 0 件（`lake env lean` が `declaration uses 'sorry'` を 0 回報告。
ファイル内の文字列 "sorry" はドキュメント中の 1 箇所のみ）。

### 検算条項: 依頼の表の定理を現物で確認した

| 依頼の記述 | 実測 |
|---|---|
| `HalfReachRecurrence.halfReach_iff_decomposition` | 存在。`1 ≤ n → 1 ≤ S → (HalfReachIn n S t ↔ ∃ m tf th, …)`。標準3公理 ✔ |
| `HalfReachMerge.halfMarginals_countLe` | 存在。`1 ≤ x → countLe (halfMarginals rows) x = predictedCount rows x`。標準3公理 ✔ |
| `RateTransfer.le_two_pow_sub_one_of_halfReachIn` | 存在。`HalfReachIn n S t → n ≤ 2^S − 1`。標準3公理 ✔ |
| `RateTransfer.gameT_mono_len` | 存在。`1 ≤ m → m ≤ n → CompleteIn n p → gameT m p ≤ gameT n p`。標準3公理 ✔ |
| `RateTransfer.Smin` / `Smin_spec` | 存在。`Smin : ℕ → ℕ`、`1 ≤ n → n ≤ 2^{Smin n} − 1 ∧ (∀ S, 1 ≤ S → n ≤ 2^S − 1 → Smin n ≤ S)` ✔ |
| `RateTransfer.gameT_full` | 存在。`1 ≤ S → gameT (2^S − 1) S = 2 * sumF S` ✔ |

食い違いは無かった。

⚠ **訂正（2026-09-03）**: 初版はここに「`git fetch origin` は SSH 認証に失敗するので
リモートと照合できない」と書いたが、**「この環境では」は過大**だった。落ちるのは
このセッションの窓だけ（ssh-agent が届いていない）で、他の窓からは `git fetch` も
`git push --dry-run` も通る、と別セッションが実測して指摘した。私の窓からの push は
`git -c credential.helper='!gh auth git-credential' push https://…` で通した。
分岐時点の `origin/main` は `e70737e`。

---

## 3. ビルドの実測

* `lake exe cache get` は使わず、本体 worktree の `.lake/packages`（7.7 GB）と
  `.lake/build`（217 MB）を**読み取りコピー**して独立の `.lake` を作った
  （本体ツリーには一切書き込んでいない）。
* 最初の全体ビルド（コピー済み olean の replay 込み）: **3486 jobs / 2m08s / 最大 4384 MB**。
* `RateTransferLow` 追加後の全体ビルド: **3487 jobs / 28s / 最大 834 MB**（exit 0）。
* 成果物の実在とタイムスタンプ（ビルド開始 10:03:11 の後に生成されていること、
  最終ビルドで再生成されていることを確認）:

```
-rw-rw-r-- 1 a a 2420200 2026-09-03 10:08:32.680389930 +0900 .lake/build/lib/lean/RevPebbling/RateTransferLow.olean
-rw-rw-r-- 1 a a   16256 2026-09-03 10:04:07.952528211 +0900 .lake/build/lib/lean/RevPebbling.olean
```

* ファイル内の数値整合チェック（`decide`、すべて緑）:
  * `cap (r+3) (2^r) = 2^{r+2} − 1`（`r = 0..5`）
  * `sumF 1..6 = 1, 4, 13, 38, 109, 302`
  * `Fpre (rowIter 2) 3 = 5`, `Fpre (rowIter 3) 5 = 9`, `Fpre (rowIter 4) 9 = 23`, `Fpre (rowIter 5) 17 = 53`
    （Lean の外の独立実装が出した値と一致）
  * `Fpre (rowIter (r+2)) (2^{r+1}+1) ≤ sumF (r+4)`（`r = 0..3`）

---

## 4. 変異注入（対照つき）

**リポジトリ外のコピー**（`…/scratchpad/mut/`）に対してのみ実施。リポジトリ内のファイルは
書き換えていない。対照 = 無変異のコピー。

| 変異 | 内容 | 結果 |
|---|---|---|
| （対照） | 無変異 | rc=0, error 0 ✔ |
| M1 | `cap_full` の右辺を `2^{r+2} − 1` → `2^{r+2}` | rc=1, error 2 ✔検出 |
| M2 | `cap` の定義を `min (2^S) K` → `min (2^S) (K+1)` | rc=1, error 5 ✔検出 |
| M3 | 左端の prefix を `2^r + 1` → `2^{r+1} + 1` に伸ばす | rc=1, error 3 ✔検出 |
| M4 | 計数下界の `(v+1)` → `(v+2)` | rc=1, error 2 ✔検出 |
| M5 | `fpre_ge_of_countLe` の係数 `2` → `3` | rc=1, error 1 ✔検出 |
| M6 | `sumF_le_two_mul` を `sumF S ≤ fRow S` に強める | rc=1, error 2 ✔検出 |
| M7 | 幾何下界の定数 `(2Mλ)^{−1/q}` → `(Mλ)^{−1/q}` | rc=1, error 2 ✔検出 |
| M8 | 主定理の極限を `log c / log 2` → `log c / log 3` | rc=1, error 2 ✔検出 |
| N1 | 局所仮説名 `hK0` → `hKzero`（意味を変えない） | rc=0, error 0 ✔誤検出なし |
| N2 | 無害な `have htriv : (0:Nat) ≤ 1` を挿入 | rc=0, error 0 ✔誤検出なし |

**検出率 8/8 = 100%、誤検出 0/2。**

---

## 5. まだやっていないこと（正直に）

* **(4) `halfMarginals_countLe` と実際の行族 `rowIter` の接続は作っていない。** 原稿
  thm:complete の証明はこの接続（「`B_S` は `A_1,…,A_S` の整列多重集合和」＝離散凸の
  infimal convolution）を経由しており、**そこが thm:complete の証明で唯一 Lean に無い段**である。
  本ファイルはそれを回避する別ルートを通したので、散文と Lean の筋書きは**別物**になっている
  （結論は同じ、原稿の側が定数の意味で強い）。原稿には触っていない。
* **「楽な道は既に潰してある」（`gameF_succ_add_one_le_gameT` で挟む等）は独立に検証していない。**
  自分の道が通ったので確かめる必要が無かった。
* **左端の上界（`H(2^{S−1},S) ≤ c^{S+o(S)}`）を単独では証明していない。** 区間全体の上界は
  右端 `gameT_full` + `sumF_le_two_mul` から出しており、それで移送は閉じている。
  「左端そのものの増大率がちょうど `c`」という言明は（下からしか）出していない。
* **有効版（明示的な誤差項つきの `n^{log₂ c ± ε(n)}`）は作っていない。** 主定理は
  `Tendsto` の形（= `o(1)`）だけである。定数倍の損失は追跡可能だが、`exists_admissible_gt`
  の λ→ρ^q 極限が非構成的なので、ε(n) の明示形は別途の作業になる。
* **`proof-manifest.json` / `README.md` は更新していない**（依頼の「既存ファイルは触らない」に従った。
  更新するのは manifest の担当セッション）。台帳（`registry/`）にも触れていない。層の昇格判断もしていない。
* ~~push していない~~ → **2026-09-03 に著者の明示指示で push 済み**
  （`gh repo view` で private を確認のうえ `rate-transfer-lowend` を push。リモートの
  `18175bb` = ローカル HEAD を `gh api` で照合）。Notion 等の外部には書いていない。
* **manifest 登録**は同日、著者の明示指示で実施（`scripts/build_proof_manifest.py` に
  `rate_transfer_left_endpoint` ステージを追加して `proof-manifest.json` を再生成）。
  ⚠ **`RevPebbling.RateTransfer`（右端 `gameT_full` 等）は依然として manifest に未登録**である。
  本ファイルの定理が依存しているので `#print axioms` の推移閉包では射程に入るが、
  名前としては載っていない。
