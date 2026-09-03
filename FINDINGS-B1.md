# B1（言明設計）作業報告 — `H(n,S)` の閉形式

**決定点への答え: 固定できた。** `gameH n S = ((halfMarginals (rowsDownFrom S)).take n).sum`
（`n ≤ 2^S − 1`）を 1 本の言明に固定し、`RevPebbling/HalfReachQuantile.lean` に置いた。
**しかも `sorry` は残っていない。** 骨格として設計した補題がそのまま既存の補題で閉じたため、
このファイルは無条件（`propext` / `Classical.choice` / `Quot.sound` のみ）である。
**したがって B2（証明埋め）のセッションは、この段については不要である。**

⚠ 骨格を歪めていないことの確認: 補題の分割・仮定・名前は「先に設計した形」のままで、
証明を通すために言明を弱めた箇所はない。弱めていたら壊れることを変異 M6・M8・M9 で実測した（後述）。

**追記（同セッション・第 2 依頼「進めて」= 次の一手 2 番）**: 最小空間区間の系を追加した。
原稿の「uniformly for `S = S^T_min(n)`」に対応する `gameT_Smin` と、その前提である
`Smin` の区間性 `Smin_eq_iff` を証明した（§9）。ファイルは 563 → 659 行、`#print axioms` は 10 → 14 本。

---

## 1. 固定した言明

```lean
theorem gameH_eq_halfCost (S n : Nat) (hn : n ≤ 2 ^ S - 1) :
    gameH n S = halfCost S n
```

ここで（すべて計算可能・`RevPebbling.HalfReachQuantile` 名前空間）

```lean
def rowOf : Nat → List Nat            -- rowOf 1 = []、rowOf (i+2) = rowIter i
def rowsDownFrom : Nat → List (List Nat)   -- [row_S, …, row_1]（降順）
def Fcost (row : List Nat) (m : Nat) : Nat := ((fullMarginals row).take m).sum
def halfCost (S n : Nat) : Nat := ((halfMarginals (rowsDownFrom S)).take n).sum
```

`gameH` は `HalfReachBridge.gameH`（`sInf {t | HalfReachRecurrence.HalfReachIn n S t}`）。
`HalfReach.gameH` との橋は既存の `RateTransfer.gameH_bridge_eq`（`1 ≤ n` が要る）で、
`gameT_eq_two_mul_halfCost` の中でだけ使っている。

### なぜこの形か（捨てた形も含む）

| 決定 | 採った形 | 捨てた形と理由 |
|---|---|---|
| 費用関数 | `Fcost row m = ((fullMarginals row).take m).sum` | `Fpre` 単独。**`Fpre l 0 = 1`（Nat の `0−1=0`）** なので `F(0,S)=0` を表せず、min-plus 畳み込みの `m=0` 分岐が書けない。実測で確認した（下記 §5）。`Fcost` は `m=0` で `0`（`Fcost_zero`、`rfl`）、`m≥1` で `Fpre` に一致（`Fcost_eq_Fpre`）。**両方要る**: `RowExact.gameF_eq_row` が語るのは `Fpre`、merge が語るのは `Fcost`。 |
| 行の並び | **降順** `rowsDownFrom S = [row_S, …, row_1]` | 依頼文の候補 `rowsUpTo S = [row_1, …, row_S]`（昇順）。多重集合としては同じで数値も一致するが、`halfMarginals` の展開が `B_S = smerge A_S B_{S−1}` になるのは降順だけで、これは (H) の漸化式そのものの形。昇順だと帰納段が漸化式と別物になり、`halfReach_decompose` を当てる場所が消える。 |
| 添字 | **ペブル数 `S` で添字**（`rowOf : Nat → List Nat`） | `rowIter` の添字 `s = S−2` をそのまま使う形。`S = 1` に対応する `rowIter` が存在せず（`A_1 = [1]`）、基底を手書きで別扱いする必要が出る。`rowOf 1 = []` と置くと `rowsDownFrom` が単一の再帰で書け、`gameF_eq_Fcost` も `S ≥ 1` 全域で 1 本になる。 |
| `m = 0` の吸収先 | **`halfReach_mono_space`**（到達可能性側のみ） | `halfReach_compose` を `m = 0` に拡張する。`compose` は `1 ≤ m` を本質的に使う（チェックポイントのペブルを土台にする）ので拡張は嘘になる。`m = 0` の分割は「鎖全体が `S−1` 個で足りる」という**予算を上げる**主張であり、`mono_space` が正しい受け皿。最適性側は `halfReach_decompose` が `1 ≤ m` しか作らないので `m = 0` に出会わない。 |

---

## 2. 骨格の補題一覧（設計した順。すべて証明済み）

**§3 長さ・整列・正値**
- `rowOf_length : 1 ≤ S → (rowOf S).length = 2^(S−1) − 1`
- `fullMarginals_length`, `marginals_length : 1 ≤ S → (fullMarginals (rowOf S)).length = 2^(S−1)`
- `halfMarginals_length : (halfMarginals (rowsDownFrom S)).length = 2^S − 1`（＝半到達の限界と一致）
- `rowOf_invariant`, `fullMarginals_NDec`, `halfMarginals_NDec`

**§4 `Fcost`/`Fpre` の橋（言明設計の核心）**
- `sum_take_map_two_mul`
- `Fcost_eq_Fpre (row) {m} (1 ≤ m) : Fcost row m = Fpre row m`
- **`gameF_eq_Fcost (S m) (1 ≤ S) (1 ≤ m) (m ≤ 2^(S−1)) : gameF m S = Fcost (rowOf S) m`**
  ← `RowExact.gameF_eq_row`（仮定を逐語で: `(h1 : 1 ≤ m) (h2 : m ≤ 2 ^ (s + 1))`、水準は `s + 2`）
  ＋ `GameDecomposition.gameF_one (S) (hS : 1 ≤ S)` で 1 ペブル水準を足したもの。
  **これが `halfMarginals` を「リスト」から「`H` の周辺費用列」に変える唯一の段。**

**§5 右端との整合（無条件）**
- `smerge_sum`（`RateTransferLow` の同名補題をローカルに再証明。依存を dispersion 系に広げないため）
- `fullMarginals_sum_eq_fRow : 1 ≤ S → (fullMarginals (rowOf S)).sum = fRow S`
- `halfMarginals_sum : (halfMarginals (rowsDownFrom S)).sum = sumF S`
- `halfCost_full : halfCost S (2^S − 1) = sumF S`

**§6 交換定理を (H) の形に**
- `halfCost_le_split {S n m k} (m+k=n) (m ≤ 2^S) (k ≤ 2^S − 1) : halfCost (S+1) n ≤ Fcost (rowOf (S+1)) m + halfCost S k`
- `halfCost_split_exists {S n} (n ≤ 2^(S+1) − 1) : ∃ m k, …`
  ← `DifferenceMergeProperty.merged_prefix_is_min_split`。**常設仮定を逐語で**:
  `(a b : List Nat) (ha : NDec a) (hb : NDec b) (n : Nat) (hn : n ≤ a.length + b.length)`。
  `NDec` は `abbrev NDec (l : List Nat) : Prop := l.Pairwise (· ≤ ·)`。

**§7 本体**
- `halfReachIn_halfCost (S n) (n ≤ 2^S − 1) : HalfReachIn n S (halfCost S n)`（到達可能性）
- `halfCost_le_of_halfReachIn (S) {n t} : HalfReachIn n S t → halfCost S n ≤ t`（最適性）
- `gameH_eq_halfCost`（本体）
- `gameT_eq_two_mul_halfCost (S n) (1 ≤ n) (n ≤ 2^S − 1) : gameT n S = 2 * halfCost S n`

**§8 原稿の (4)**
- `dCount : Nat → Nat → Nat`（`D_S(x)`。`dCount (S+1) x = 1 + countLe (rowOf (S+1)) (x/2) + dCount S x`）
- `dCount_one : dCount 1 x = 1`（水準 1 は基底項のみ ＝ (4) が `i = 2` から和を取る理由）
- **`countLe_halfMarginals_eq_dCount (S x) (1 ≤ x) : countLe (halfMarginals (rowsDownFrom S)) x = dCount S x`**
  ＝ 原稿の (4)。`HalfReachMerge.halfMarginals_countLe`（仮定 `(hx : 1 ≤ x)`）を `rowsDownFrom` で具体化したもの。

**§9 最小空間区間（第 2 依頼で追加）**
- `Smin_eq_iff {n S} (1 ≤ n) (1 ≤ S) : Smin n = S ↔ 2^(S−1) ≤ n ∧ n ≤ 2^S − 1`
- `gameH_Smin (n) (1 ≤ n) : gameH n (Smin n) = halfCost (Smin n) n`
- **`gameT_Smin (n) (1 ≤ n) : gameT n (Smin n) = 2 * halfCost (Smin n) n`**
- `gameT_of_interval {n S} (1 ≤ n) (1 ≤ S) (2^(S−1) ≤ n) (n ≤ 2^S − 1) : Smin n = S ∧ gameT n S = 2 * halfCost S n`

### `sorry` の一覧

**なし（0 本）。** 骨格として `sorry` を置く予定だったのは次の 2 本で、両方とも埋まった:

| 予定していた `sorry` | 実際 |
|---|---|
| `halfReachIn_halfCost`（≤ 側・到達可能性） | 証明済み。`halfCost_split_exists` → `m=0` なら `halfReach_mono_space`、`1 ≤ m` なら `reachIn_iff`/`GameKnill.reachIn_one` → `reachIn_gameF` → `gameF_eq_Fcost` → `halfReach_compose` |
| `halfCost_le_of_halfReachIn`（≥ 側・最適性） | 証明済み。`halfReach_decompose` → `le_two_pow_of_reachIn` と `le_two_pow_sub_one_of_halfReachIn` で分割の両側を押さえ → `gameF_le`＋`gameF_eq_Fcost` → `halfCost_le_split` |

Stop フックの証明ゲートは `GATE-OK` 無しで通る（`sorry`/`admit` が 1 つも無いため）。

---

## 3. `#check` / `#print axioms` の実測

```
gameH_eq_halfCost : ∀ (S n : ℕ), n ≤ 2 ^ S - 1 → RevPebbling.HalfReachBridge.gameH n S = halfCost S n
gameT_eq_two_mul_halfCost : ∀ (S n : ℕ), 1 ≤ n → n ≤ 2 ^ S - 1 →
  RevPebbling.GameCompleteCost.gameT n S = 2 * halfCost S n
halfReachIn_halfCost : ∀ (S n : ℕ), n ≤ 2 ^ S - 1 →
  RevPebbling.HalfReachRecurrence.HalfReachIn n S (halfCost S n)
halfCost_le_of_halfReachIn : ∀ (S : ℕ) {n t : ℕ},
  RevPebbling.HalfReachRecurrence.HalfReachIn n S t → halfCost S n ≤ t
gameF_eq_Fcost : ∀ (S m : ℕ), 1 ≤ S → 1 ≤ m → m ≤ 2 ^ (S - 1) →
  RevPebbling.GameCost.gameF m S = Fcost (rowOf S) m
halfCost_full : ∀ (S : ℕ), halfCost S (2 ^ S - 1) = RevPebbling.RateTransfer.sumF S
Smin_eq_iff : ∀ {n S : ℕ}, 1 ≤ n → 1 ≤ S →
  (RevPebbling.RateTransfer.Smin n = S ↔ 2 ^ (S - 1) ≤ n ∧ n ≤ 2 ^ S - 1)
gameT_Smin : ∀ (n : ℕ), 1 ≤ n →
  gameT n (RevPebbling.RateTransfer.Smin n) = 2 * halfCost (RevPebbling.RateTransfer.Smin n) n
countLe_halfMarginals_eq_dCount : ∀ (S x : ℕ), 1 ≤ x →
  countLe (halfMarginals (rowsDownFrom S)) x = dCount S x
```

`#print axioms`（ファイル末尾に常設。14 本すべて）:

```
gameF_eq_Fcost              : [propext, Classical.choice, Quot.sound]
halfCost_full               : [propext, Classical.choice, Quot.sound]
halfCost_le_split           : [propext, Classical.choice, Quot.sound]
halfCost_split_exists       : [propext, Classical.choice, Quot.sound]
halfReachIn_halfCost        : [propext, Classical.choice, Quot.sound]
halfCost_le_of_halfReachIn  : [propext, Classical.choice, Quot.sound]
gameH_eq_halfCost           : [propext, Classical.choice, Quot.sound]
gameT_eq_two_mul_halfCost   : [propext, Classical.choice, Quot.sound]
Smin_eq_iff                 : [propext, Classical.choice, Quot.sound]
gameH_Smin                  : [propext, Classical.choice, Quot.sound]
gameT_Smin                  : [propext, Classical.choice, Quot.sound]
gameT_of_interval           : [propext, Classical.choice, Quot.sound]
countLe_halfMarginals       : [propext, Classical.choice, Quot.sound]
countLe_halfMarginals_eq_dCount : [propext, Classical.choice, Quot.sound]
```

（`#print axioms` は 14 本。上は実測の全文。）

**`sorryAx` は出ない。`Lean.ofReduceBool` も出ない**（`native_decide` は使っていない）。
`sorryAx` が出るのは変異注入したときだけで、実際に出た（§6）。

---

## 4. ビルドの実測

| 実行 | jobs | 所要 | 最大メモリ |
|---|---|---|---|
| 起点（新ファイル前、`18175bb`） | 3487 | 0h00m28s | 294 MB |
| 新ファイル ＋ `RevPebbling.lean` 変更後（ルートも再 elaborate） | 3488 | 0h01m56s | 2582 MB |
| 最終版・olean 削除して再ビルド（3487 replay ＋ 1 compile） | **3488** | 0h00m15s 〜 **0h01m49s** | 579 〜 **3107 MB** |
| 単体 `lake env lean RevPebbling/HalfReachQuantile.lean` | — | 約 4s | 431–470 MB |

すべて `runcap -m 12 -t 3600 -- nice -n 19 …`（`lean-lowend` の資源指示に従い `-m 40` → `-m 12`）。

**成果物の実在とタイムスタンプ**（`verify-build` の §1 に従い、終了コードでなく成果物で確認）:

```
ビルド開始 (UTC)  2026-09-03T06:46:56Z
-rw-rw-r-- 1 a a 827352 2026-09-03 15:47:56.698312611 +0900
  .lake/build/lib/lean/RevPebbling/HalfReachQuantile.olean
```

開始 60 秒後の生成。所要とメモリの幅（15s/579MB 〜 1m49s/3107MB）は、ルートモジュール
`RevPebbling.lean`（全モジュールを import する）の再 elaborate が入るかどうかと、
共用機の同時負荷（別セッションが `-verify` で proof-gatekeeper を実行中）による。
**上限 12 GB には到達していない**（`runcap` が実測を報告する）。ビルド前に olean を明示的に削除しているので、
前回の残骸ではない。`Build completed successfully (3488 jobs).`

---

## 5. 数値アンカーの検算（前工程の数値と一致したか）

**「終わったら何が言えるか」（測る前に書いた）**: 独立に組んだ DP と Lean の閉形式が
510 ケースで一致すれば、`halfCost` が指しているのが `H` であることの証拠になる。
一致しなければ、どちらが誤りかはこの測定だけでは決まらない（片側の結論しか出ない）。

**(a) Lean の外での独立計算**（`scratchpad/anchors.py`。`rowIter`/`gen` を一切使わない）
- `F(n,S)`: Knill の漸化式 `F(n,S) = min_{1≤m, m≤2^{S−2}, n−m≤2^{S−2}} [F(m,S)+F(m,S−1)+F(n−m,S−1)]`、`F(1,S)=1`
- `A_i(j) = F(j,i) − F(j−1,i)`、`B_S = sorted(A_1 ⊎ … ⊎ A_S)`、閉形式 `= sum(B_S[:n])`
- `H(n,S) = min_{0≤m≤min(n,2^{S−1})} [F(m,S) + H(n−m,S−1)]`、`H(0,S)=0`

結果: **`S = 1..8` の全 `n = 0..2^S−1`、510 ケースで一致、不一致 0。**

**(b) Lean 側（`#eval`）と (a) の突き合わせ** — すべて一致:

| 量 | 値 | 前工程の報告 |
|---|---|---|
| `halfCost 4 n`, `n=0..15` | `0,1,2,3,4,6,8,10,12,14,16,20,24,28,32,38` | 一致 |
| `halfCost 5 n`, `n=0..31` | `0,1,2,3,4,5,7,9,11,13,15,17,19,21,23,25,29,33,37,41,45,49,53,57,61,65,71,77,83,91,99,109` | 一致 |
| `halfCost S (2^S−1)`, `S=1..8` | `1,4,13,38,109,302,833,2264` | 一致（`sumF` とも一致） |
| `halfCost S (2^(S−1))`, `S=1..8` | `1,2,5,12,29,80,195,546` | 一致 |
| `halfMarginals (rowsDownFrom 4)` | `[1,1,1,1,2,2,2,2,2,2,4,4,4,4,6]` | — |
| `f_i = F(2^{i−1},i)`, `i=1..8` | `1,3,9,25,71,193,531,1431` | `RowExact` の `gameF 4 3 = 9` 等と一致 |

**(c) Lean の中で `decide`（カーネル）に固定した**アンカー（ファイル §2・§8）:
`fullMarginals (rowOf S)` の 5 本、`halfMarginals (rowsDownFrom 4)`、`halfCost 4` の 16 値、
`halfCost 5` の 32 値、右端 8 値、左端 7 値、長さ 8 値、`dCount 5 x`（`x=1..10`）の 10 値。

**(d) Lean の中での経路交差**（§8）: `gameH_eq_halfCost` ＋ `halfCost_full` から
`gameH (2^S−1) S = sumF S` を導き、既存の `RateTransfer.gameH_full`（容量ピジョンホールでなく
分割一点固定による別経路）と同じ命題であることをカーネルに確認させた。
`gameH 4 3 = 5`・`gameT 4 3 = 10` も `decide` で固定してある
（`RateTransferLow.fpre_le_gameH_left` の `r=0` は `3 ≤ H(4,3)` を主張し、`5` と矛盾しない）。

**前工程の数値は 4 つとも正しかった。訂正すべき点は無い。**

### 検算中に出た実測上の注意（前工程の報告に無かったもの）

- **`smerge` は `termination_by` を持つので整礎再帰でコンパイルされ、封印されている。
  `decide` も `rfl` もカーネル簡約で詰まる。** `unseal RevPebbling.DifferenceMergeProperty.smerge in`
  を各コマンドの直前（**doc コメントより前**）に置くと通る。これは可約性の変更だけで公理は増えない
  （上の `#print axioms` が実測）。最初にこれに気づかず `tail` で出力を切っていて
  「アンカーは通った」と誤読しかけた。**`decide` の失敗は `tail` で隠れる。**
- `List.range 1 8` は関数適用エラーになる。区間は `List.range' 1 7`。

---

## 6. 変異注入（射程・検出率・誤検出）

**射程**: `sorry` を含まないので、このファイルの**全体**が射程内（当初想定の
「`decide` のアンカーと補助定義だけ」より広い）。**変異はリポジトリ外のコピーにのみ**行い、
リポジトリ内のファイルは一度も書き換えていない
（`scratchpad/mut/*.lean` に対して `lake env lean` を実行）。

| 変異 | 内容 | 検出 | 最初に落ちた場所 |
|---|---|---|---|
| M0（対照） | 無変異 | — | **error 0 / rc 0** |
| M1 | `rowOf 1 = [1]`（基底の周辺費用列を誤る） | ✔ 14 errors | `decide` アンカー L144 |
| M2 | `Fcost` を `take (m−1)` に（**依頼文が名指しした境界の罠**） | ✔ 4 errors | `Fcost_eq_Fpre` L263 → `gameF_eq_Fcost` L281 |
| M3 | `rowOf (i+2) = rowIter (i+1)`（添字ずらし） | ✔ 12 errors | `decide` アンカー L144 |
| M4 | `halfCost` を `take (n+1)` に | ✔ 12 errors | `halfCost_succ` L114 |
| M5 | `rowsDownFrom (S+1) = rowOf S :: …`（行族の添字ずらし） | ✔ 14 errors | `rowsDownFrom_succ` L111 |
| M6 | `gameH_eq_halfCost` の仮定を `n ≤ 2^S` に弱める | ✔ 5 errors | `gameH_eq_halfCost` L459 |
| M7 | `dCount` から基底項 `1 +` を落とす | ✔ 4 errors | `predictedCount_rowsDownFrom` L490 |
| M8 | `halfCost_le_split` の仮定を `k ≤ 2^S` に弱める | ✔ 3 errors | `halfCost_le_split` L349 |
| M9 | `Smin_eq_iff` の区間下端を `2^(S−2) ≤ n` に誤る | ✔ 3 errors | `Smin_eq_iff` L554 |
| M10 | 区間アンカーの値を `[5,7,9,13]` → `[5,7,9,12]` に | ✔ 1 error | `decide` アンカー L592 |

**検出率 10/10 = 100%。誤検出 0/1（対照は無警告で通る）。**

読み取れること:
- **アンカーだけで捕まるのは 5/10**（M1・M3・M4・M5・M10）。
  **M2・M6・M8・M9 は証明でしか捕まらない。**
  すなわち数値アンカーは行族の同定と区間の値には効くが、`m = 0` の境界・仮定の強さ・
  区間の端の位置には効かない。
- **M6・M8・M9 が落ちることが「骨格を歪めていない」ことの実測**である。
  仮定 `n ≤ 2^S − 1`・`k ≤ 2^S − 1`・区間下端 `2^(S−1)` はいずれも荷重を担っている。
- M1・M3・M5 は `sorryAx` を 7〜8 本出す（後続が芋づるで壊れる）。M0 は 0 本。

---

## 7. 原稿との対応（原稿は読んだだけ。1 バイトも触っていない）

`ieice_letter_core_v2_1.tex` の `thm:complete`（L631〜）の 4 段のうち:

| 段 | 状態 |
|---|---|
| 1 時間反転 `T = 2H` | 既存（`HalfReach.gameT_eq_two_mul_gameH`） |
| 2 min-plus 漸化式 (H) | 既存（`HalfReachRecurrence.halfReach_iff_decomposition`） |
| **3 `B_S` は `A_i` の整列多重集合和 → 閾値計数 (4)** | **本ファイルで閉じた**（`gameH_eq_halfCost` ＋ `countLe_halfMarginals_eq_dCount`） |
| 4 dispersion 上界を (4) に当てて下界 | 既存（`DispersionReal.dispersion_real` ほか）だが **(4) 経由では未接続**（§10 の 1） |
| 結び「Monotonicity sandwiches every `2^{S−1} ≤ n ≤ 2^S − 1`」 | **挟み撃ちが不要になった**。`gameT_Smin` が区間内の全ての `n` で `T` の**正確な値**を与える（§9）。`RateTransfer.gameT_mono_len` による sandwich は、増大率の議論には引き続き使えるが、値を出すのにはもう要らない |

**なぜ「高価な欠落」ではなかったか**: 原稿が離散凸性の議論として書いている内容は、
リポジトリでは `merged_prefix_is_min_split`（任意の非減少リストに対する交換定理）として
**既に一般形で証明済み**だった。必要だったのは (i) `Fcost`/`Fpre` の境界の橋、
(ii) 行族の同定（`gameF_eq_Fcost`）、(iii) `m=0` の吸収先の決定、の 3 点だけで、
どれも新しい数学ではない。重みは全部 `RowExact.gameF_eq_row` に既に載っていた。

---

## 8. まだやっていないこと（正直に）

1. **原稿 (4) → 左端の下界の解析部分は接続していない。**
   `H(2^{S−1},S) ≥ (2^{S−1} − D_S(x_S))·x_S` と `Σ_{i≤S} C_i(x/2) = o(2^S)` は Lean に無い。
   `dCount S x` と dispersion の `C_i(v)`（`countLe (rowIter (i−2)) v`）を結ぶ補題も無い。
   **指数そのものは `RateTransferLow` が別経路（容量ピジョンホール）で既に取っている**ので、
   ここで得られるのは指数ではなく**定数**（外部実測で約 0.45 対 0.20）である。
2. ~~`Smin` との組み合わせは書いていない~~ → **第 2 依頼で解消**（§9）。
   `Smin_eq_iff` で区間性を証明し、`gameT_Smin` / `gameT_of_interval` を置いた。
   ⚠ **食い違いの報告（未解消）**: `RateTransfer.lean` の docstring は `Smin_eq_iff` /
   `Smin_interval` という名前を挙げているが、**そのファイルに実在するのは `Smin`・
   `completeIn_Smin`・`Smin_le`・`Smin_spec` の 4 本だけで、その 2 つの名前は存在しない**
   （`grep` で実測）。本ファイルの `HalfReachQuantile.Smin_eq_iff` は**同名だが別物**
   （`RateTransfer` 側には無い）。既存ファイルは触らない指示なので docstring は直していない。
3. **`halfCost` の計算量については何も主張していない。** カーネルの `decide` が通ったのは
   `S ≤ 7`（右端・左端・長さのアンカー）と、全値の列挙は `S ≤ 5` まで。`S = 8` の値
   （`2264` / `546`）は Lean の外（`#eval` と Python）でしか確認していない。
4. **`RateTransferLow.lean` の docstring "What is *not* used" は本ファイルによって古くなった**
   （「the row family is still not connected to it」「none of it is in Lean」は現在は誤り）。
   **既存ファイルは触らない指示なので直していない。** 誰かが直す必要がある。
5. **`proof-manifest.json` は再生成していない**（指示どおり触っていない）。
   `scripts/build_proof_manifest.py` は `RevPebbling/**/*.lean` を glob するので、
   **新ファイルを置いた時点で manifest は古くなり、CI の `git diff --exit-code proof-manifest.json` は落ちる。**
   `sorry` が無いので「proof holes」では落ちない。再生成すれば緑になるはずだが、
   台帳・manifest は本セッションの担当外。
6. **層の昇格判断はしていない。** `registry/`・`README.md`・`STATUS.md` に触っていない。
7. **`decide` アンカーの `unseal` は elaboration の可約性のみを変える**と `#print axioms` で
   確認したが、`unseal` 自体の健全性を独立に検証したわけではない（Lean の仕様に依存している）。
8. push していない。外部（Notion / Slack / Drive）へは何も書いていない。
