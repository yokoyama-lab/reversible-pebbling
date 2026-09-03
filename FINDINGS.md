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

---

# 後始末 — (4) の始末、公理監査の道具、root 全体の緑

*worktree `reversible-pebbling-lean-lowend` / branch `rate-transfer-lowend` / 2026-09-03（後継セッション）*

## 0. 決定点への答え（1 行）

**(ii) を選んだ。理由: `-merge` が同日に埋めたのは「(4) を行族に接続する新定理」であり、
「既にある (4) の 4 定理を公理監査してステージに載せる」作業とは重複せず、しかも接続の成否に
関わらず必要な監査面だから。** ((iii) は「原稿は直す必要が無い」という提案として返した。
(i) の「待つ」は、待つ対象が私の作業時間中に完了したため消滅した。)

## 1. 決定の前に確かめた事実（すべて現物で）

| 依頼文が言っていたこと | 私の実測 | 一致 |
|---|---|---|
| `RateTransferLow` の import 錐は 99 モジュール | import 文を静的に推移閉包して **99**（自身込み） | ✔ |
| 錐外は 33 モジュール | root の錐 132 − 99 = **33** | ✔ |
| (H)`HalfReachRecurrence` と `HalfReachBridge` は錐に入る | 入る（`HalfReach` も入る） | ✔ |
| (4)`HalfReachMerge` は錐に入らない | 入らない。**import しているのは root 集約 `RevPebbling.lean` だけ**で、`fullMarginals` / `halfMarginals` / `predictedCount` は他のどのソースにも現れない（言及 2 件はいずれも docstring の散文） | ✔ |
| manifest に `RateTransfer` 鍵 2・定理 40 | `99a9706` の `proved_stages` 辞書で `rate_transfer_scaffold` 16 + `rate_transfer_left_endpoint` 24 = **40 定理・鍵 2**（`source_sha256` 辞書は別物で 135 件） | ✔ |
| ビルドは 2788 jobs | `lake build RevPebbling.RateTransfer RevPebbling.RateTransferLow` が **2788 jobs** で完了 | ✔ |

追加で分かったこと（依頼文に無いもの）:

* **`main` の `proof-manifest.json` は壊れている。** `source_sha256` が **124 件**しかないのに
  ツリーには対象ファイルが **134** ある。つまり `build_proof_manifest.py` を回すと
  `git diff --exit-code proof-manifest.json` が落ちる。
  本ブランチ（`99a9706` で 135/135）はこれを直しており、merge はその修理も運ぶ。
  ⚠ **訂正**: 私は最初これを「`main` の CI は赤」と書いたが、**過大だった**。
  `gh run list --workflow build.yml` を見ると、**直近 14 回の `main` の run はすべて
  `cancelled`**（2026-08-21 以降、push も schedule も）。**成功も失敗もしていない。**
  原因の候補は 2 つ: `timeout-minutes: 90` に対して README が言う実測が約 2.25 時間、
  および `concurrency.cancel-in-progress` が同じ `main` の run を互いに打ち切ること。
  **つまり GitHub 側の CI はここしばらく何の信号も出していない**ので、
  「manifest が古い」は**私が手元で回して確かめた事実**であり、CI が教えてくれたことではない。
* **README の数値は `99a9706` の時点で既にずれていた**（`check_claims.py`:
  定理数 861 対 901、ステージ数 67 対 69）。merge 前に直した。

## 2. テストファースト — 公理監査の道具を先に置いた

主張の前に検査を置いた。`scripts/check_axioms.py`（新規）は、**manifest のどのステージにも
載っていないモジュール**に `#print axioms` を当てて分類する
（`axiom_free` / `standard` / `native` / `DISALLOWED` / `MISSING`）。ライブラリの再ビルドは要らない。

**「走らなかった検査」と「異常なし」を区別するため、空の選択は 0 ではなく 2 を返す**
（`NOTHING CHECKED: … This is not a pass.`）。成功時も `CHECKED n declaration(s)` を必ず出す。

### 対照を先に取った

書いたあと、まず**無変異の対照**を回した: `HalfReach` / `HalfReachRecurrence` /
`HalfReachMerge` / `HalfReachBridge` の **34 宣言すべてが `standard`**
（`propext` / `Classical.choice` / `Quot.sound` のみ）、`native` 0・`DISALLOWED` 0・`MISSING` 0、
rc=0。1m22s / 最大 RSS 3765 MB。**これを見てから**ステージ登録に進んだ。

### 変異注入（対照つき、リポジトリ外のコピーのみ）

`scratchpad/mut/` に置いたコピーに対してのみ実施。リポジトリ内のファイルは書き換えていない。

**A. 検査器が棄却しなければならない入力（検出力）**

| # | 入力 | 期待 | 実測 |
|---|---|---|---|
| M1 | 存在しない定理名 | rc=1 | rc=1・`MISSING` ✔ |
| M2 | `sorry` で閉じた定理 | rc=1 | rc=1・`DISALLOWED [sorryAx]` ✔ |
| M3 | 局所 `axiom` に乗る定理 | rc=1 | rc=1・`DISALLOWED [probe_local_ax]` ✔ |
| M4 | `native_decide`（既定） | rc=0・`native` と表示 | rc=0・`native` ✔ |
| M5 | `native_decide`（`--forbid-native`） | rc=1 | rc=1 ✔ |
| M6 | 空の選択 | rc=2 | rc=2 ✔ |

**検出 5/5**（M4 は「棄却」ではなく「分類」なので分母に入れない）。

**B. 誤検出の対照（受理しなければならない入力）**

| # | 入力 | 実測 |
|---|---|---|
| N1 | ライブラリの実在定理 34 本 | rc=0・誤検出 0 ✔ |
| N1' | 実在定理 2 本 | rc=0 ✔ |
| N2 | `rfl` の定理＋`Classical.em` の定理 | rc=0（`axiom_free` 1・`standard` 1）✔ |

**誤検出 0/3。**

**C. 検査器そのものへの変異（テストが検査器の劣化に気づくか）**

| # | 変異（リポジトリ外のコピー） | 当てたテスト | 結果 |
|---|---|---|---|
| K1 | `classify` が `DISALLOWED` を返せないようにする | M2 | rc=0 に転落 → **検出** ✔ |
| K2 | 未出力の名前を `standard` 扱いにする | M1 | rc=0 に転落 → **検出** ✔ |
| K3 | 空選択のガードを外す | M6 | rc=0 に転落 → **検出** ✔ |

**3/3 検出。**さらに K1–K3 のいずれも N2 の対照は rc=0 のままで、誤警報は出なかった。

以上をリポジトリ内で再現できるように `scripts/test_check_axioms.py`（8 ケース）を置いた。
**実測 8/8 PASS。**⚠ **CI には組み込んでいない**（1 ケースごとに `import RevPebbling` の
コストがかかるため）。走らせるのは `check_axioms.py` を変えたとき。

## 3. 決定点 — なぜ (ii) か

作業中に `lean-merge` セッションから完了報告が届き、**(4) を実際の行族に接続する段は
同日に閉じた**（branch `half-reach-merge`、`RevPebbling/HalfReachQuantile.lean`）。
私は**そのワークツリーには入らず、git オブジェクトだけを読んで**次を確かめた:

* `half-reach-merge` は `18175bb` から分岐し 4 コミット（`5d60f1b..eb7b6d2`）。
  `HalfReachQuantile.lean`（トップレベル定理 34 本）と `HalfReachDispersion.lean`（同 11 本）が新規。
* 両ファイルとも `sorry` / `admit` / 局所 `axiom` は**静的 grep で 0 件**。
  ⚠ **私はこれをビルドしていない。** grep は「書かれていない」を示すだけで、緑の根拠ではない。
* **`half-reach-merge` の `proved_stages` は 67 鍵・861 定理**で、`main` と同じ。
  つまり**新 3 モジュールはどのステージにも載っていない**（先方の報告 ④ と一致）。

したがって「(4) の 4 定理を公理監査してステージに載せる」作業は**誰ともぶつからない**。
接続が入ろうと入るまいと、(4) 自身の監査面は空のままだったからである。これが (ii) を選んだ理由。

### (iii) は「提案」として: **原稿は直さなくてよい**

`.tex` には触っていない。提案は 1 行:

> **原稿 thm:complete が (4) を名指ししている段は、そのままでよい。**
> 前任が `18175bb` で確かめたとおり道は塞がっておらず、いまや Lean 側も
> （`half-reach-merge` が merge されれば）同じ道を通る。原稿を (H)+Bridge に
> 寄せると、かえって**定数の悪いほう**（実測で真値の 0.216 対 0.554）に寄せることになる。

なお `RateTransferLow` の docstring が (4) の道を「the expensive missing piece」と
呼んでいたのは**誤った見積り**だった（一般形は `DifferenceMergeProperty.
merged_prefix_is_min_split` として既にリポジトリにあった）。`30c648d` で訂正した。
同じコミットで、`RateTransfer` の docstring が挙げていた**実在しない定理名**
`Smin_eq_iff` / `Smin_interval` も直した（`grep` で不在を確認）。

## 4. manifest — どこまで埋めたか

`build_proof_manifest.py` に**ステージを 2 つ**足した（辞書 `proved_stages`）。

| 鍵（`proved_stages`） | モジュール | 定理数 | 錐の内外 |
|---|---|---|---|
| `half_reach_optimum_and_recurrence` | `HalfReach` / `HalfReachRecurrence` / `HalfReachBridge` | 30 | **錐内**（主定理の推移的判定が既に届いていた。名前で見えるようにしただけ） |
| `half_reach_marginal_merge` | `HalfReachMerge` | 4 | **錐外**（主定理の判定は届かない。**このステージが唯一の監査**） |

`half_reach_marginal_merge` の `scope` には、証明されていること（2 つのリスト論的事実）と
**証明されていないこと**（`rows` は任意の `List (List Nat)` で、`rowIter` にも
`HalfReachIn` の費用にも接続していない）を明記した。`status` は既存の語彙に無い
`proved_general_but_unused` を使った。

### 埋めなかったもの（正直に）

`proved_stages` に 0 件のモジュールは、依頼文の 9 個ではなく**実測 15 個**あった
（名前空間で数えた。`HalfReach` / `CutUpper` / `DispersionGeneral` / `PebblingGame` /
`DispersionBound5033` / `DispersionRecover` が依頼文の一覧に無かった）。
このうち埋めたのは `HalfReach` 系 4 つだけ。**残り 11 は埋めていない**:
`CapZone` / `CutUpper` / `DispersionBound5033` / `DispersionGeneral` / `DispersionRecover` /
`NearFull` / `PebblingGame` / `RetentionPremium` / `ShapeMonotone` / `TieBand` / `XLift`。

理由: これらは上界側の機械で、この依頼の射程（左端の後始末）の外にある。とくに
`NearFull.lean` は**本体ツリーに持ち主不明の未コミット変更 +131 行**があり、触るべきでない。

## 5. root 全体の緑 — 何を実行して何を見たか

依頼の指摘どおり、独立検算者は **import 錐の 99 モジュールしかソースからビルドしていない**。
錐外の 33 モジュールは「コピーしてきた olean を replay しただけ」で、誰も本当にはビルドしていなかった。
そこで **その 33 モジュールのビルド成果物を消してから** root を建て直した
（`.lake/build/lib/lean/RevPebbling/<M>.*` と `.lake/build/ir/RevPebbling/<M>.*`。
この worktree の `.lake` は本体ツリーとは inode が別の独立コピーであることを確認済み）。

`systemd-run --user`（`nice -n 19`、`MemoryMax=32G`、`RuntimeMaxSec=18000`）で切り離して実行。
`run_in_background` は約 60 分で殺されるので使っていない。

| 見たもの | 実測 |
|---|---|
| `lake build`（root target `RevPebbling`） | **rc=0**、**3487 jobs**、**1:32:14**、最大 RSS **4144 MB**、ログ中の `error` **0 行** |
| うち最重量 | `Built RevPebbling.AnchorCertify4798 (5510s)` — README の実測（5695 s / 6084 s）と同水準 |
| root 集約そのもの | `Built RevPebbling (7.0s)`、`.lake/build/lib/lean/RevPebbling.olean` は 19:14:05 に再生成 |
| olean の実在 | **138 本**。うち**開始スタンプより新しいものがちょうど 33 本**＝消した 33 モジュールが確かにソースから作り直された |
| `build_proof_manifest.py` | **rc=0**。`axiom audit OK: 935 theorems`（73 が native_decide、17 が公理ゼロ）、`statement audit OK`、`proof_bundle_sha256=c10924b56abaf81c58b33dcef622cd5cd0330913c66835c35546b9f979af4b5b` |
| `check_claims.py` | **rc=0**、`claims OK` |
| service の終了 | `SERVICE TERMINAL STATE: inactive (exit=0)` |

⚠ **正直に言うと**: 錐内の 99 モジュールは今回**replay である**（検算者が今日ソースから
建てたものを引き継いでいる）。「全 132 モジュールを今この場でソースから」ではない。
今回ソースから建てたのは**錐外の 33 と root 集約**である。

⚠ **打ち切りは起きていない。** 時間・メモリの上限（5 時間 / 32 GB）には触れていない。

### manifest の数値（ref と辞書名つき）

`c2f83a4` の `proof-manifest.json`、辞書 **`proved_stages`**: **71 鍵・935 定理**
（`99a9706` では 69 鍵・901 定理）。辞書 **`source_sha256`** は別物で **135 件**
（対象ファイル 135 と一致）。新しい 2 鍵の内訳は
`half_reach_optimum_and_recurrence` 30 定理・`half_reach_marginal_merge` 4 定理、
どちらも `native_decide_theorems` 0 件・`axiom_free_theorems` 0 件・`carried_hypotheses` 空
（＝ 34 本すべてが標準 3 公理ちょうど）。これは §2 の対照が独立に出した結果と一致する。

## 6. まだやっていないこと（正直に）

* **`half-reach-merge` の 2 ファイルをビルドしていない。** `sorry` 不在は**静的 grep**で見ただけで、
  緑の根拠ではない。あのブランチの検証はあちらのセッションの仕事であり、私は
  ワークツリーにも `.lake` にも触れていない。
* **`half-reach-merge` を merge していない。** 本ブランチを `main` に進めたので、
  あちらは `main` の上に載せ直すことになる。**`proof-manifest.json` は必ず衝突する**
  （両方が再生成している）。解き方は「どちらかを採ってから
  `python3 scripts/build_proof_manifest.py` を回し直す」で、手で継ぎ合わせない。
  ⚠ **その merge のとき、README の 3 つの数値（定理数・ステージ数・native/axiom-free）も
  一緒に動く。** 新 3 モジュールをステージに載せるなら必ず。
* **`proved_stages` に 0 件のモジュールが 11 個残っている**（上の §4）。
* **`RateTransfer` / `RateTransferLow` の 46 宣言のうち manifest に載っているのは 40 本。**
  残り 6 本は curated 一覧の外（`#print axioms` では全 46 本が標準 3 公理・native 0 を実測済み）。
* **左端そのものの上界（`H(2^{S−1},S) ≤ c^{S+o(S)}`）は依然として単独では証明していない**
  （前任の報告のまま。区間全体の上界は右端から出している）。
* **有効版（明示的な誤差項）も依然として無い。**
* **層の昇格判断はしていない。台帳（`topic-mining/registry`）には触れていない。**
* **原稿（`~/dev/overleaf/2026_exact_reversible_pebbling`）は開いても編集してもいない。**
  §3 の提案は、原稿を読まずに Lean 資産と前任の報告だけから書いたものである。
* **`scripts/test_check_axioms.py` を CI に入れていない**（§2）。

## 7. コミット

| ref | 内容 |
|---|---|
| `63f9403` | `scripts/check_axioms.py` と `scripts/test_check_axioms.py`（テストファースト） |
| `30c648d` | `RateTransfer` / `RateTransferLow` の docstring 3 点訂正（散文のみ） |
| `c2f83a4` | `proved_stages` に 2 ステージ（34 定理）、`proof-manifest.json` 再生成、README の数値 |
