# n = 24・s = 7 で鎖に勝つ根つき木（Lean、2026-10-09）

## 結論

**緑。「n = 24・s = 7 で、鎖より少ない手数で解ける根つき木がある」は層 1。**

- 主定理は `Spooky.RootedTree.exists_tree_beats_chain_24_7`（`SpookyPebblingExtra/TreeN24.lean`）:
  頂点 24 個の根つき木 `t`（`t.isTree = true`）で、
  `t.TPK 7 < (chain 24).TPK 7`（KSS Def 2.6/2.7 の意味論）かつ `t.TP 7 < (chain 24).TP 7`（`Defs.lean` と同じ広いモデル）。
- 具体的には、木 (1,17,6) `((((((((((((((((((),),),),),),),),),),),),),),),),), ((((((),),),),),))`
  （根の下に長さ 17 と 6 の腕）で **`T_P(木, 7) ≤ 83 < 85 = T_P(鎖_24, 7)`**（`tree_1_17_6_beats_chain`）。
- **`native_decide` は使っていない。** 手順の検査は `decide +kernel` で、`#print axioms` は標準の 3 つ以下。`Lean.ofReduceBool` は載らない。
- 一般木と鎖の一致（`TP_chain`・`TPK_chain`）は前回の `RootedTree.lean`（main に取り込み済み、c9fbc3b）をそのまま使った。
- 範囲外（層 2 のまま）: n ≤ 23 の根つき木はどれも s = 7 で鎖に勝てないこと。

## 前回（n = 18）との違い: KSS の意味論への読み替え

83 手の証人は、**`ready` が真の状態で `ghost` を打つ手を 3 つ含む**（10 手目 `ghost 14`・30 手目 `ghost 5`・31 手目 `ghost 6`。
どれも子がペブル）。広いモデルでは合法だが、KSS Def 2.6/2.7 では許されない（親が揃っていればゴーストは生じない）。
実際、そのままでは KSS の意味論で通らないことを `tree_1_17_6_not_runK` で示した。

そこで `KSSModel.lean` の `tweakK`/`stripK` と同じ読み替えを木について定義した（`tweakKT`/`stripKT`、`TreeN24.lean` の中）:
`ready` が真のときの `ghost v` を `unpebble v` に、新しい走りで対象がゴーストでないときの `unghost v` を `pebble v` に置き換える。
長さは変わらない（`stripKT_length`、一般の証明）。読み替えた 83 手が KSS の意味論で妥当であること（`tree_1_17_6_runK`）は、
**一般の正規化定理ではなく、この手順についての `decide +kernel` の検査**で示した。
読み替えで変わるのは 6 手（上の ghost 3 つと、対応する 45・46・64 手目の unghost）で、ペブルの最大数は 7 のまま（Python での数え直し。判定は Lean）。

## 定理

| 定理 | 内容 |
|---|---|
| `tweakKT`・`stripKT`・`stripKT_length` | KSS の意味論への読み替え（木版）と、長さが変わらないこと |
| `tree_1_17_6_isTree` | 木 (1,17,6) は頂点 24 の根つき木（根 0、根の子は 1 と 18） |
| `tree_1_17_6_run` | **83 手が広いモデルで妥当**（全手が規則どおり、全時刻でペブル ≤ 7、終状態は根だけペブル・他は空） |
| `tree_1_17_6_not_runK` | そのままでは KSS の意味論で妥当でない |
| `tree_1_17_6_runK` | **読み替えた 83 手が KSS の意味論で妥当** |
| `tree_1_17_6_TP_le`・`tree_1_17_6_TPK_le` | `T_P(木, 7) ≤ 83`（両方の意味論） |
| `TP_24_7` | **`Spooky.TP 24 7 = 85`**（`TP_eq_slope6`: `θ(6) = 21 ≤ 23`・`24 ≤ B_4(6) = 52`。`pilot-s7/chain_lean_check.py` の具体化と同じ形） |
| `chain24_TP`・`chain24_TPK` | `(chain 24).TP 7 = 85`・`(chain 24).TPK 7 = 85` |
| `tree_1_17_6_beats_chain` | 上の 5 つを並べた形 |
| **`exists_tree_beats_chain_24_7`** | **主定理（存在）** |

## 検算条項（前工程の数字）

| 前工程の主張 | ここでの確認 |
|---|---|
| 鎖は `T_P(24,7) = 85` | **一致**（`TP_24_7`） |
| 木 (1,17,6) は 83 手・ペブル最大 7 | **一致**（`tree_1_17_6_run`。上限 6 では広いモデルでも読み替え後でも落ちる） |
| 手順は前順の番号（`verify_1-17-6.json`） | Lean に機械で転記し、転記後の Lean ファイルから抜き出した手順が JSON の `moves` と、親の配列が `tree` から独自に作った前順の親の配列と一致することをスクリプトで照合した |
| （依頼文に無い点） | JSON の手順は KSS の意味論ではそのまま通らない（上の 3 手）。広いモデルの手順としては正しく、読み替えで KSS の手順になる |

## ゲート（5 点）

### 作成者の検査（2026-10-09 08:2x〜、<host>。日中なので対象ファイルだけをビルドし、Mathlib は再ビルドしていない）

1. **ビルド成果物**: `lake build SpookyPebblingExtra.TreeN24` が rc=0、`TreeN24.olean` が 08:28:25 に生成された。
   44 秒、最大 RSS 9.6GB。新しいファイルの警告 0 件。再ビルドされたのは TreeN24 だけ。
2. **`#print axioms`**（リポジトリ外のファイルから、rc=0・olean 生成）:
   `exists_tree_beats_chain_24_7`・`tree_1_17_6_beats_chain`・`tree_1_17_6_run`・`tree_1_17_6_runK`・`tree_1_17_6_not_runK`・`TP_24_7`
   は `[propext, Classical.choice, Quot.sound]`、`tree_1_17_6_isTree`・`stripKT_length` は `[propext]`。
3. **計数**: `sorry`・`admit`・`axiom` 宣言・`native_decide`・`implemented_by`/`extern`・`opaque`・`unsafe` が 0 件
   （`native_decide` の文字列はコメント中の「使わない」という言及だけ）。
4. **変異注入**（`RootedTree.lean` と `TreeN24.lean` の本文を 1 ファイルに連結したコピーをリポジトリ外に作り、1 か所ずつ壊す。
   時間節約のため、コピーからは下の全数変異の 3 例を外した。対照も同じ）:
   **無変異の対照は通り、変異 11 種はすべて落ちた（11/11、未確定 0）**。変異は、読み替えの ghost→unpebble を外す・unghost→pebble を外す、
   `stripKT` が 1 手落とす、前提条件を常に真に、KSS の制限を外す、木の親を 1 つ動かす（18 の親を 1 に）、証人の 1 手目を変える、
   `TP 24 7 = 84` と主張する、広いモデルの上限を 6 に、上界を 82 と主張する、`example : False := by decide +kernel` を差す。
   どれも意味上のエラー（`decide` が偽と判定・`rfl` 失敗・型の不一致・`omega` 失敗）で落ちた。うち 2 種（unghost→pebble を外す・木の親を動かす）は
   KSS の手順の検査で `decide` が失敗し、エラー文の表示が時間切れになった（落ちた場所は狙った定理）。
   これとは別に、Lean の中に**1 か所変えた手順の全数の拒否**を置いている（`decide +kernel` で緑）:
   1 手削除 83 通り・操作の変更 249 通り・頂点の変更 1,992 通り（範囲外の頂点を含む）。どれも `Run` にならない。
5. **成果物の実在**: `TreeN24.olean` と、この文書。

### 独立の検査者（proof-gatekeeper）

作成者の結果を伏せて依頼した（2026-10-09 08:3x）。**5 点すべて緑**。

1. `TreeN24` の olean 類を消してから `lake build SpookyPebblingExtra.TreeN24` → rc=0（44 秒）。Mathlib のコンパイル 0 件。
   olean・ilean・trace・hash が 08:33:15〜16 に再生成された（削除前は 08:28:25）
2. `#print axioms`: 主要 6 定理は標準 3 つだけ、`stripKT_length`・`tree_1_17_6_isTree` は `[propext]`。`Lean.ofReduceBool`・`sorryAx` なし
3. 計数: コード中 0 件（ヒットはコメントの 1 行）
4. 変異注入（検査者が独自に選んだ 12 種、連結コピー・全数変異の 3 例は外す）: 対照は通り、12 種すべて落ちた。
   変異は tweakKT の ghost 分岐の条件を反転・`stripKT` が読み替えない・証人の 1 手目・木の親・上限 6・`TP 24 7 = 84`・上界 82・
   tweakKT の unghost 分岐の条件を反転・`ready` を「空でない」に・`ok` の上限を s+1 に・手数を 82 と主張・主定理の `<` を `>` に
5. 成果物の実在: 再生成された olean 類

目視: `tweakKT`/`stripKT` は `KSSModel.lean` の `tweakK`/`stripK` と構造が一致（違いは `ready` が `t.ready` になる点だけ）。
`sInf ∅ = 0` の抜け道は無い（上界は具体的な 83 手から）。`tree_1_17_6_not_runK` があるので読み替えが実際に効いている。

## 再現

```sh
lake build SpookyPebblingExtra.TreeN24
```

`SpookyPebblingExtra.lean` からは import していない（既存ファイルを改変しない約束のため）。

## まだやっていないこと

- **`T_P(木 (1,17,6), 7) = 83`（下界）**は示していない。上界 83 だけ
- **n ≤ 23 の根つき木はどれも s = 7 で鎖に勝てないこと**（範囲外、層 2 のまま）
- 木の上の KSS 版への正規化の一般定理（`TPK = TP`。`KSSModel.lean` の `stripK_ok` の木版）。この証人について具体的に確かめただけ
- `SpookyPebblingExtra.lean`・README の層の表・台帳・STATUS.md・TREE_STATUS.md・作業ログには反映していない
- main へのマージ・push はしていない
