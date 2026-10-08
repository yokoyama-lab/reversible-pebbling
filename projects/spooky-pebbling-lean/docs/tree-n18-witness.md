# n = 18・s = 6 で鎖に勝つ根つき木（Lean、2026-10-09）

## 結論

**緑。「n = 18・s = 6 で、鎖より少ない手数で解ける根つき木がある」は層 1。**

- 主定理は `Spooky.RootedTree.exists_tree_beats_chain`（`SpookyPebblingExtra/TreeN18.lean`）:
  頂点 18 個の根つき木 `t`（`t.isTree = true`）で、
  `t.TPK 6 < (chain 18).TPK 6`（KSS Def 2.6/2.7 の意味論）かつ `t.TP 6 < (chain 18).TP 6`（`Defs.lean` と同じ広いモデル）。
- 具体的には、木 1291836 `((((((((((),),),), (((),),)),),),),), (((((),),),),))` で
  **`T_P(木, 6) ≤ 61 < 63 = T_P(鎖_18, 6)`**（`tree1291836_beats_chain`）。
- **`native_decide` は使っていない。** 手順の検査は `decide +kernel`（カーネルの簡約）で、`#print axioms` は標準の 3 つ
  （`propext`・`Classical.choice`・`Quot.sound`）だけ。`Lean.ofReduceBool` は載らない。
- 一般木の定義が鎖の定義と一致することは**一般の `n`・`s` で証明した**（`TP_chain`・`TPK_chain`）。
  したがって主定理は「一般木のモデルで」と限定する必要がない。
- 範囲外（層 2 のまま）: n ≤ 17 の根つき木はどれも s = 6 で鎖に勝てないこと（n\*(6) = 18 の下側）。

## 定理とファイル

新規ファイルは 3 つ。既存ファイルは改変していない（したがって `SpookyPebblingExtra.lean` からは import されていない。下の「再現」を参照）。

| ファイル | 中身 |
|---|---|
| `SpookyPebblingExtra/RootedTree.lean` | 一般の根つき木のゲーム（定義）と、鎖との一致（一般の証明） |
| `SpookyPebblingExtra/RootedTreeTests.lean` | `decide +kernel` の陽性・陰性テスト（テストファーストで先に書いたもの） |
| `SpookyPebblingExtra/TreeN18.lean` | n = 18 の証人 2 本・`T_P(18,6) = 63`・主定理・61 手の変異 |

| 定理 | 内容 |
|---|---|
| `RootedTree.ready_chain`・`legal_chain`・`legalK_chain` | 鎖 `chain n` の上で前提条件・1 手の規則が `Defs.lean`・`KSSModel.lean` のものと一致（すべての配置・すべての手で） |
| `RootedTree.ok_chain`・`okK_chain` | 手順全体の判定が一致 |
| `RootedTree.PLengths_chain`・`PLengthsK_chain` | 手数の集合が一致 |
| `RootedTree.TP_chain` | `(chain n).TP s = Spooky.TP n s` |
| `RootedTree.TPK_chain` | `(chain n).TPK s = Spooky.TP n s`（`KSSModel.lean` の `TP_eq_K` 経由） |
| `RootedTree.isTree_chain` | 鎖は根つき木（`n ≥ 1`） |
| `RootedTree.tree9_runK`・`tree9_beats_chain` | n = 9・s = 4 の既知の証人 29 手が通り、`T_P(木, 4) ≤ 29 < 31 = T_P(鎖_9, 4)` |
| `RootedTree.TP_9_4` | `Spooky.TP 9 4 = 31` |
| `RootedTree.tree1291836_isTree` | 木 1291836 は頂点 18 の根つき木（根 0、根の子は 1 と 13） |
| `RootedTree.tree1291836_runK` | **61 手が KSS の意味論で妥当**: 全手が規則どおり、全時刻でペブル ≤ 6、終状態は根だけペブル・他は空（ゴーストも残らない） |
| `RootedTree.tree1291836_TPK_le`・`tree1291836_TP_le` | `T_P(木, 6) ≤ 61`（両方の意味論） |
| `RootedTree.TP_18_6` | **`Spooky.TP 18 6 = 63`**（`TP_eq_TUG_succ` と定理F `TUG_eq_slope6`） |
| `RootedTree.chain18_TP`・`chain18_TPK` | `(chain 18).TP 6 = 63`・`(chain 18).TPK 6 = 63` |
| `RootedTree.tree1291836_beats_chain` | `TPK ≤ 61`・`(chain 18).TPK 6 = 63`・`TP ≤ 61`・`(chain 18).TP 6 = 63`・`TP 18 6 = 63` を並べた形 |
| **`RootedTree.exists_tree_beats_chain`** | **主定理（存在）** |
| `RootedTree.tree1603216_runK`・`tree1603216_beats_chain` | もう 1 本の証人（木 1603216、葉 6）も 61 手で通り、`TPK < (chain 18).TPK` |

## モデル

- 根つき木は `RootedTree`（`n`・`par : ℕ → Option ℕ`・`root`）。`par u = some v` は辺 `u → v`（`u` は `v` の子）。辺は葉から根へ向かう（KSS の DAG の向き。根が sink）。
- `ready t c v` ⇔ `par u = some v` となる `u < n` がすべてペブル。`legal` / `ok` / `Run` / `PLengths` / `TP` は `Defs.lean` の同名のものと**同じ形**で、`ready` だけを差し替えた。
  `legalK` / `okK` / `TPK` は `KSSModel.lean` の `legalK` と同じ形（`ghost` は `ready` が偽のときだけ）。
- 終状態は `rootPebble`（根だけペブル）で、`AgreeOn n` で照合する（他の頂点は空、ゴーストも不可）。上限は全時刻（始状態・終状態を含む）で検査する。
- `isTree` は計算可能な検査: 根は `n` 未満で親なし、ほかの頂点は `n` 未満の親を持つ、どの頂点からも親を `n` 歩たどれば根の外に出る（閉路なし）。
  閉路・根が 2 つ・親が範囲外・根から離れた閉路を拒むことをテストで確かめた。
- 61 手の証人は KSS の意味論でも妥当（`ghost(13)` は 13 の子 14 がペブルでないときに打たれている）。したがって木の側で KSS 版への正規化（`KSSModel.lean` の木版）を証明する必要がなかった。

## 検算条項（前工程の数字）

| 前工程の主張 | ここでの確認 |
|---|---|
| 鎖は `T_P(18,6) = 63`（closed2・spooky_bfs） | **一致**。Lean で `TP_18_6`。依頼文の「`TUG 17 5 = 62` になるはず（未確認）」も成り立つ（`TUG_eq_slope6` から `T_UG(17,5) + 40 = 102`）。依頼文は `TUG_eq_envelope`（`SpookyPebblingExtra/Envelope.lean`）を挙げていたが、本体ライブラリの定理F（`Slope6Exact.lean`、`θ(5) = 15 ≤ 17`・`18 ≤ B_4(5) = 32`）で足りたのでそちらを使った |
| 木 1291836 は 61 手・ペブル最大 6 | **一致**（`tree1291836_runK`。上限 5 では落ちる） |
| 木 1603216 も 61 手 | **一致**（`tree1603216_runK`） |
| 親の配列・手順（`verify_*.json`） | Lean に機械で転記し、転記後の Lean ファイルから抜き出した親の配列・手順が JSON の `par_preorder`・`moves`、および木の文字列から独自に作った前順の親の配列と一致することをスクリプトで照合した（2 本とも一致）。木の id と文字列の対応は `pilot-n18/lists/n18_witness.json` と一致 |
| n = 9・s = 4 の証人 29 手 | `pilot-n18/out/` に手順は保存されていなかったので、`pilot-n18/bin/spooky_path 4 -1 0 1 2 3 4 0 6 7` で取り出した（`spooky_path` の出力は信用せず、Lean の検査が判定）。`T_P(9,4) = 31` も Lean で閉じた（`TP_9_4`） |

食い違いは無かった。

## ゲート（5 点）

### 作成者の検査（2026-10-09 01:4x〜01:5x、<host>）

1. **ビルド成果物**: `lake build SpookyPebblingExtra.RootedTree SpookyPebblingExtra.RootedTreeTests SpookyPebblingExtra.TreeN18` が rc=0。
   olean 3 つが今回生成された（`RootedTree.olean` 01:45:21、`TreeN18.olean` 01:47:18、`RootedTreeTests.olean` 01:53:54）。
   ビルド時間は 6〜26 秒、最大 RSS 7.9GB（Mathlib の読み込みが大半）。新しい 3 ファイルの警告 0 件。Mathlib・既存モジュールの再ビルドは 0 件。
2. **`#print axioms`**（リポジトリ外のファイルから `lake env lean --root=… -o …`、rc=0・olean 生成）:
   `exists_tree_beats_chain`・`tree1291836_beats_chain`・`tree1291836_runK`・`TP_18_6`・`tree1603216_beats_chain`・`TP_chain`・`TPK_chain`・`ok_chain`・`okK_chain`・`tree9_beats_chain`・`TP_9_4`
   はすべて `[propext, Classical.choice, Quot.sound]`。`isTree_chain` は `[propext, Quot.sound]`。
3. **計数**: 3 ファイルとも `sorry`・`admit`・`axiom` 宣言・`native_decide`・`implemented_by`/`extern`・`opaque`・`unsafe` が 0 件
   （`native_decide`・`ofReduceBool` の文字列はコメント中の「使わない」という言及だけ）。
4. **変異注入**（3 ファイルを 1 ファイルに連結したコピーをリポジトリ外に作り、1 か所ずつ壊す。判定は 3 値）:
   **無変異の対照は通り、変異 20 種はすべて落ちた（20/20、未確定 0）**。
   変異は、前提条件（常に真・辺の向きを逆に・子がゴーストでも可）、pebble の空の検査を外す、unpebble / unghost の前提を外す、
   KSS の制限を外す、終状態の上限検査を外す、上限を 1 緩める、`okK` のペブル数で 1 頂点を数えない、終状態の頂点をずらす、
   `Run` から終状態の照合を外す、`isTree` から閉路の検査を外す、鎖の親をずらす、木の親を 1 つ動かす、証人の `unghost(13)` を `pebble(13)` に、
   `TP 18 6 = 62` と主張する、主定理の上限を 5 に、上界を 60 と主張する、`example : False := by decide +kernel` を差す。
   このうち unpebble / unghost の前提を外す・閉路の検査を外す の 3 種は、最初は一般の証明（`legal_chain`・`isTree_chain`）だけが止めていた。
   具体例でも捕まるよう陰性テストを 3 本足し（子が欠けた根の unpebble・unghost、根から離れた閉路）、再検査で 3 種ともそのテストで落ちることを確かめた。
   これとは別に、Lean の中に**1 か所変えた手順の全数の拒否**を置いている（すべて `decide +kernel` で緑）:
   n = 9 は 1 手削除 29 通り・操作の変更 87 通り・頂点の変更 261 通り（範囲外の頂点を含む）、
   n = 18 は 1 手削除 61 通り・操作の変更 183 通り・頂点の変更 1,098 通り。どれも `Run` にならない。
5. **成果物の実在**: 上の olean 3 つと、この文書。

### 独立の検査者（proof-gatekeeper、2026-10-09 01:54〜02:01）

作成者の結果を伏せて依頼した。**5 点すべて緑**。

1. 3 モジュールの olean・ilean・trace・hash を消してから `lake build` → rc=0。再ビルドは 3 モジュールだけ（Mathlib の行 0）。
   新しい olean は `RootedTree` 01:54:59・`RootedTreeTests` 01:55:07・`TreeN18` 01:55:24
2. `#print axioms`: 主要 9 定理は `[propext, Classical.choice, Quot.sound]`、`isTree_chain` は `[propext, Quot.sound]`、
   `tree1291836_isTree` は `[propext]`。`Lean.ofReduceBool`・`sorryAx` なし
3. 計数: 実コードの該当 0 件（ヒットはコメントの言及 3 行）。`noncomputable def` は `TP`・`TPK`（sInf）の 2 つだけ
4. 変異注入（検査者が独自に選んだ 13 種、連結コピー）: 対照は通り、13 種すべて意味上のエラー（`decide` が偽・`rfl` 失敗・型の不一致）で落ちた。
   変異は ready が子を無視・pebble / unghost の ready を削除・ghost を常に可・上限を s+1（ok・okK）・終状態を空に・証人の 1 手目を変更・
   `TP_18_6 = 62`・上界 ≤ 60・legalK の ghost 条件を反転・閉路検査を true に・鎖の親を `v+2` に
5. 成果物の実在: 削除後に再生成された olean と、対照の olean

定義の目視でも問題なし: `sInf ∅ = 0` の抜け道は主定理に効かない（木の側は証人を `TPK_le`・`TP_le` に渡し、鎖の側は等式で出している）、
`isTree` は何でも通すものではない（陰性テスト 4 種と変異で確認）、主定理の言明は空虚でない。

## 再現

```sh
cd <作業ツリー>
lake build SpookyPebblingExtra.RootedTree SpookyPebblingExtra.RootedTreeTests SpookyPebblingExtra.TreeN18
```

3 つは `SpookyPebblingExtra.lean` から import されていないので、`lake build SpookyPebblingExtra` では建たない。
本体に入れるなら `SpookyPebblingExtra.lean` に `import SpookyPebblingExtra.TreeN18` と `import SpookyPebblingExtra.RootedTreeTests` を足す（既存ファイルの改変なので、この依頼ではしていない）。

## まだやっていないこと

- **`T_P(木 1291836, 6) = 61`（下界）**は示していない。上界 61 だけ。存在の主張には上界で足りる
- **n ≤ 17 の根つき木はどれも s = 6 で鎖に勝てないこと**（n\*(6) = 18 の下側）。依頼の範囲外で層 2 のまま
- 木の `T_P` が番号の付け替えで変わらないこと。ここでは木を前順の 1 つの番号付けで与え、鎖は `Defs.lean` の番号付けで与えている
- 一般の木での KSS 版への正規化（`TPK = TP`。`KSSModel.lean` の木版）。証人が KSS の意味論でそのまま通るので主定理には要らなかった
- 試走の証人 62 本のうち、Lean で検査したのは 2 本（1291836・1603216）だけ
- 偶奇の議論（根つき木では `T_P` が奇数）は Lean に無い
- `SpookyPebblingExtra.lean`・README の層の表・台帳（topic-mining/registry）・STATUS.md・TREE_STATUS.md・作業ログには反映していない（依頼で禁止。反映は艦長2 の判断）
- main へのマージ・push はしていない
