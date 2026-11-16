# EXTREMAL_MANIFEST — 極値予想の反証の形式化（2026-09-05 着手・2026-09-06 完了）

> **判定（1 行）**: **(A) `M(5) ≥ 12` は層 1 に到達した**（`native_decide` 不使用・
> 証人 1 個の存在証明・公理は Mathlib 標準の `[propext, Classical.choice, Quot.sound]`）。
> **(B) 「鎖 `L_12` はピーク 5 に収まらない」は有界全数検査**（`native_decide`）なので
> 台帳の規則「有界事例の機械検証は層 1 にしない」に当たり**層 1 にしない**。
> **合成命題「極値予想は偽」は (B) に律速されるので層 2 が上限**——ただし証拠は
> 「SAT の DRAT のみ」から「Lean の機械検査でも独立に再現」へ二重化された。
> ⚠ **層の昇格判断はしていない。以下は判定材料である。**
>
> 5 点ゲート: **ビルド緑**（84 秒）・**`.olean` 883,480 バイトを今回の実行で生成**・
> **`sorry` 0 / `axiom` 宣言 0 / `sorryAx` 0**・**変異注入 14/14 検出（うち 7 本は
> `native_decide` の計算そのものが落とした）・対照 4/5 通過（誤検出 1・理由は §2 ゲート 5）**。

対象: `lean/Revgarbage/ParPebbleExtremal.lean`（新規）。
台帳の行: `topic-mining` の `registry/results.tsv` の **R-Q2-14**（**本セッションは触っていない**）。

---

## 0. 模型が既存の形式化と一致するかの確認（着手前）

REQUEST の指示「深さの数え方が頂点数か辺数かでずれる。ずれていたら判断して書く」への答え。

| 項目 | REQUEST の模型 | 既存 `ParPebbleDAG` | 一致 |
|---|---|---|---|
| 1 歩の合法性 | 在否が変わる `v` について `par(v) ⊆ C_t ∩ C_{t+1}` | `LegalStep pa P Q := ∀ v, Changed P Q v → ∀ u ∈ pa v, u ∈ P ∧ u ∈ Q` | ✅ 逐語で同じ |
| 始状態 | `C_0 = ∅` | `Pebbling.start : P 0 = ∅` | ✅ |
| 深さ `d` | sink で終わる最長路の**辺数** | `dep sink = d`、例 `paD`（`0→2←1`、辺 1 本）で `depD 2 = 1` | ✅ **辺数**で一致 |
| 時間最適 | `T = 2d+1` | `par_time_exact_dag` が `2 * d + 1` | ✅ |

⚠ 既存ファイルの**コメント**は `T_par = 2·depth − 1` と書いており、そこでの `depth` は
**頂点数**（`= d+1`）である。`2(d+1) − 1 = 2d+1` なので**数式としては同じ**。
コードの識別子 `d` は一貫して辺数。**ずれは無かったので、既存の定義をそのまま再利用した。**

したがって本ファイルは `ParPebbleDAG.Changed` / `LegalStep` / `Pebbling` を再定義せず import し、
時間最適性の証明も既存の `ParPebbleWindow.par_time_exact_dag_two_sided` をそのまま当てている。

---

## 1. 定理の書き分け — **無条件 / 有界全数検査**（1 行ずつ）

`#print axioms` の実測に基づく。**`native_decide` を使った定理は補助公理
`<名前>._native.native_decide.ax_1_1` が公理欄に現れる**ので機械的に判別できる。

### 1.1 無条件（有界全数検査ではない）

| 定理 | 内容 | 公理 |
|---|---|---|
| `legalStep_iff_legalOn` | 合法性を `P ∪ Q` に制限しても同値（決定可能化の橋） | `propext, Classical.choice, Quot.sound` |
| `CleanRun.restrict` | 走行を頂点集合 `V` に切り落としても走行のまま・ピークは増えない | `propext, Quot.sound` |
| `mem_reach` | `V` に収まるピーク `p` 以下の走行の配置は必ず `reach t` に入る（全数検査の健全性） | `propext, Classical.choice, Quot.sound` |
| `chain_class` | 任意の `n` で鎖は `D(n)` に属する | `propext, Classical.choice, Quot.sound` |
| `chain_depth` | 任意の `n` で鎖の深さは `n−1` | 同上 |
| `chain_time_lower` | 任意の `n ≥ 2` で鎖の時間下界 `T ≥ 2(n−1)+1` | 同上 |
| `Achieves_of_chainAchieves` | `n*(p) ≤ M(p)`（鎖も `D(n)` の一員） | 同上 |
| `not_chainAchieves_of_unreachable` | 到達集合に `{sink}` が無ければ走行は存在しない（一般の橋渡し） | 同上 |
| `witness_class` | 証人 `∈ D(12)`（トポロジカル順・入次数 ≤ 2・sink 一意・12 以上に辺なし） | 同上 |
| `witness_depth` | 証人の深さ `= 10` | 同上 |
| `witness_time_optimal` | 証人では `T ≥ 21`（`T = 21` は時間最適） | 同上 |
| `witness_run` | 与えたスケジュールは合法な clean 走行でピーク 5 | 同上 |
| ⭐ **`M5_ge_12`** | **(A) `M(5) ≥ 12`** | 同上 |
| `chain11_peak5` | 鎖 `L_11` はピーク 5 で走れる（`n*(5) ≥ 11`） | 同上 |
| `chain12_peak6` | 鎖 `L_12` はピーク 6 なら走れる | 同上 |

⚠ `Classical.choice` は**私の証明が古典論理を使っているからではなく**、Mathlib の
`Finset.mem_union_left` が既に依存しているため（実測: `#print axioms Finset.mem_union_left`
＝ `[propext, Classical.choice, Quot.sound]`）。`CleanRun.restrict` のように
`Finset.mem_union` を経由しない補題は `[propext, Quot.sound]` で閉じている。

### 1.2 有界全数検査（`native_decide`。⚠ 層 1 にしない）

| 定理 | 何を全数で調べたか | 追加公理 |
|---|---|---|
| `chain12_sink_unreachable` | 鎖 `L_12`・頂点集合 `{0..11}`・ピーク ≤ 5・23 歩の**到達配置全体**（1,586 通りの配置 × 23 段）に `{11}` が無い | `chain12_sink_unreachable._native.native_decide.ax_1_1` |
| `chain11_sink_unreachable_p4` | 鎖 `L_11`・ピーク ≤ 4・21 歩の到達配置全体に `{10}` が無い | `chain11_sink_unreachable_p4._native.native_decide.ax_1_1` |
| ⭐ **`chain12_peak5_impossible`** | **(B)**。上の 1 本目 ＋ 無条件の `not_chainAchieves_of_unreachable` | 1 本目と同じ |
| `chain11_peak4_impossible` | `p_min(L_11) = 5` の下側 | 2 本目と同じ |
| ⭐ **`chain_not_extremal`** | **(A)+(B)**。「鎖が極値グラフ」の点ごとの形は偽 | (B) と同じ |
| `extremal_false_of_chain_monotone` | 鎖の単調性を**仮定**したうえで `M(5) ≥ 12 ∧ n*(5) ≤ 11` | (B) と同じ |

**`native_decide` が使われているのは `chain12_sink_unreachable` と
`chain11_sink_unreachable_p4` の 2 行だけ**（ファイル中の `native_decide` は 2 箇所）。
それ以外の (B) 側の定理は、この 2 本に**無条件の補題を合成**しているだけである。
すなわち**符号化の正しさは証明されていて、計算だけが信頼の対象**になっている:

* 「合法な走行なら到達集合に入る」は `mem_reach`（無条件）。
* 「頂点集合の外にペブルを置いてもよい走行」も `CleanRun.restrict`（無条件）で
  `{0..n−1}` の中に落とせるので、全数検査の枠を `V` の部分集合に限ってよい。
  ⭐ **`CleanRun` に「配置は `V` の中」を課していない**のはこのためで、
  (B) の非存在主張はその分だけ強い。
* 「`T = 2d+1` が時間最適」は `witness_time_optimal` / `chain_time_lower`（無条件、
  既存の `par_time_exact_dag_two_sided` を経由）。

### 1.3 形式化していないこと（**ここが (B) の残る隙間**）

`M(5) ≠ n*(5)` を厳密に閉じるには、`n*(5) = max{n : p_min(L_n) ≤ 5}` なので
**`n ≥ 13` の鎖もすべて落ちること**が要る。本ファイルが閉じたのは **`n = 12` の 1 点**だけ。

* 台帳 `R-Q2-01` は「`T_par(n,p) = 2n−1 ⟺ n ≤ n*(p)`」＝**鎖の族は下に閉じている**を
  層 2 の事実として持っている。これを仮定として**明示的に受け取る**形で
  `extremal_false_of_chain_monotone` を書いた（仮定は Lean の引数として見える）。
* **その単調性は本ファイルでは証明していない。** 証明の道筋も分かっていない
  （窓定理で `w_{n−2}` の窓が幅 2 に潰れることは使えるが、`L_n` の走行から
  `L_{n−1}` の走行を切り出す素直な構成は見つからなかった）。
* 仮定なしで完全に閉じているのは `chain_not_extremal`＝「極値予想の**点ごとの形**は偽」
  （`D(12)` に走れる DAG が在るのに 12 頂点の**鎖**は走れない）である。
  これは `M(p) = n*(p)` より**強い**命題の否定なので、`M(p) = n*(p)` 自体の否定には
  上の単調性が要る。**この差は誇張してはならない。**

---

## 2. 5 点ゲート

### ゲート 1 — ビルド

```
$ runcap -m 32 -t 3000 -- lake build
✔ [8568/8570] Built Revgarbage.ParPebbleExtremal (84s)
Build completed successfully (8570 jobs).
runcap: 成功 / 最大メモリ 1034 MB（上限 32 GB）
```

道具: `leanprover/lean4:v4.31.0`、Mathlib `fabf563a7c95`（`v4.31.0`）。
**素で起動していない**（すべて `runcap -m <GB> -t <秒> --` 経由）。打ち切りは 1 件も無い。

### ゲート 2 — 成果物の実在（⚠ 沈黙を成功と読まない）

```
$ ls -l --time-style=full-iso .lake/build/lib/lean/Revgarbage/ParPebbleExtremal.olean
-rw-rw-r-- 1 a a 883480 2026-09-05 23:57:19 …/ParPebbleExtremal.olean
$ date  →  2026-09-05 23:57:24
```

**883,480 バイトの `.olean` が、この実行で（5 秒前に）作られている。**
`lake build` の直前に当該 `.olean` を消して作り直させたので、キャッシュ済みビルドではない。

### ゲート 3 — 公理検査 `#print axioms`

§1 の表がその実測結果。**再実行せずに確認できるよう、要となる 4 行を逐語で貼る**
（`lake env lean` で `import Revgarbage.ParPebbleExtremal` して `#print axioms` した出力）:

```
'ParPebbleExtremal.M5_ge_12' depends on axioms: [propext, Classical.choice, Quot.sound]
'ParPebbleExtremal.witness_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'ParPebbleExtremal.chain12_peak5_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 chain12_sink_unreachable._native.native_decide.ax_1_1]
'ParPebbleExtremal.chain_not_extremal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 chain12_sink_unreachable._native.native_decide.ax_1_1]
```

⭐ **(A) 側（`M5_ge_12` / `witness_run`）に `native_decide` の補助公理が付いておらず、
(B)（`chain12_peak5_impossible`）と合成後（`chain_not_extremal`）には付いている。**
「合成は (B) に律速されて層 2 が上限」の根拠は、この出力そのものである。
（2026-09-06 に `ren-fe` が独立に再実行して同じ 4 行を得ている。）

要点だけ再掲:

* (A) 側 15 本 … `[propext, Classical.choice, Quot.sound]`（Mathlib 標準）。
  **`native_decide` 由来の補助公理は 1 つも無い。**
* (B) 側 6 本 … 上に加えて `chain12_sink_unreachable._native.native_decide.ax_1_1`
  ないし `chain11_sink_unreachable_p4._native.native_decide.ax_1_1`。
* `sorryAx` は **1 本も現れない**。

### ゲート 4 — `sorry` / `axiom` 計数

```
$ grep -c -E '\bsorry\b|\badmit\b' Revgarbage/ParPebbleExtremal.lean   →  0
$ grep -c -E '^\s*axiom '          Revgarbage/ParPebbleExtremal.lean   →  0
$ grep -n 'native_decide'          Revgarbage/ParPebbleExtremal.lean
  （chain12_sink_unreachable の証明 1 行）
  （chain11_sink_unreachable_p4 の証明 1 行）
```
（他 2 件はコメント中の言及。）**`native_decide` は 2 箇所のみ。**

### ゲート 5 — 変異注入（検出率と誤検出を**対で**）

**⚠ 変異は (a) 自分が書いた `ParPebbleExtremal.lean` にだけ、(b) リポジトリ外のコピー
（`…/scratchpad/mut/*.lean`）に対して行った。リポジトリ内は 1 バイトも書き換えていない。**
生成器は「置換対象がちょうど 1 箇所でなければ異常終了」する fail-closed にしてある
（置換が当たらないまま緑になる＝空虚な試験を防ぐため）。全 19 本を
`runcap -m 24 -t 900 -- lake env lean <コピー>` で走らせた。

> **検出 14/14（不活性 0）・対照 4/5 通過（誤検出 1）。**
> ⭐ うち **7 本は `native_decide` の計算そのものが落とした**（＝有界全数検査が
> 空回りしていない証拠）、5 本はカーネル `decide`、2 本は型検査。

| # | 変異 | 落ちた場所 | 判定 |
|---|---|---|---|
| M1 | 証人の辺 `3→4` を削る | カーネル `decide`（`witness_class.child`。頂点 3 が子を失い sink 一意が壊れる） | ✅ 検出 |
| M2 | スケジュール `t=8` から頂点 8 を落とす | カーネル `decide`（`wSched_legal`） | ✅ 検出 |
| M3 | 証人の走行を `T=21 → 20` に縮める | カーネル `decide`（`finish`）＋ 型不一致 | ✅ 検出 |
| M4 | 深さラベル `wDep` を壊す | カーネル `decide`（`witness_depth` の上からの証明書） | ✅ 検出 |
| M13 | 最長路 `wPath` を壊す | カーネル `decide`（`witness_depth` の**下からの**証明書） | ✅ 検出 |
| M5 | 到達集合の初期値を `{∅}` → 全配置 | ⭐ `native_decide`（`{11} ∉ reach … 5 23` が false） | ✅ 検出 |
| M6 | 到達集合のピーク上限を `p → p+1` | ⭐ `native_decide` ＋ 型不一致 | ✅ 検出 |
| M7 | 鎖から辺をすべて削る | ⭐ `native_decide` ＋ 証明スクリプト | ✅ 検出 |
| M8 | **(B) の主張のピークを 5 → 6** | ⭐ `native_decide`（`{11} ∉ reach … 6 23` が **false**） | ✅ 検出 |
| M9 | 合法性から「後」側の親の要求を外す | ⭐ `native_decide` ＋ 型不一致 | ✅ 検出 |
| M10 | **(B) の的を `{11}` → `{10}`** | ⭐ `native_decide` ＋ 型不一致 | ✅ 検出 |
| M11 | 鎖 `L_11` の非存在主張を `p=4 → 5` | ⭐ `native_decide`（`{10} ∉ reach … 5 21` が **false**） | ✅ 検出 |
| M12 | 時間下界を `2(n−1)+1 → 2(n−1)+2` に強めすぎる | 型不一致 | ✅ 検出 |
| I1 | 証人の走行を `T=21 → 22` に**伸ばす** | 型不一致（`Achieves` が `T = 2d+1` を型で固定している） | ✅ 検出（⚠ 下記） |
| C0 | **無変異**（原本と `cmp` で同一） | — | ✅ 通過（89 秒） |
| C1 | `{2, 3}` → `{3, 2}`（同じ Finset） | — | ✅ 通過 |
| C2 | スケジュールに冗長な分岐 `21` を足す（同じ関数） | — | ✅ 通過 |
| C3 | `wPath` の条件を `j ≤ 2` → `j < 3`（同値） | — | ✅ 通過 |
| C4 | `cfgs` の述語を `s.card ≤ p` → `¬ (p < s.card)`（同値） | `mem_cfgs` の `exact ⟨h1, h2⟩` | ⛔ **誤検出** |

**⚠ 正直な但し書き 3 つ**

1. **C4 は誤検出（対照 5 本中 1 本）。** 述語としては同値だが、`Nat` の `≤` と `¬ <` は
   **定義的に等しくない**ので `mem_cfgs` の証明スクリプトが壊れた。
   **健全性の欠陥ではない**（検査が過敏な側に外れただけ）が、対照として立てた以上
   「通るはずが落ちた」は誤検出として数える。⚠ **結果を見てから対照を差し替える
   ことはしていない**（それをすると対照が意味を失う）。
2. **I1 は事前に「不活性のはず」と予想して立てたが、検出された。** 予想は外れた。
   理由は `Achieves` の定義が `CleanRun … (2 * d + 1) …` と**時間最適性を型で固定**して
   いるため、`T` を伸ばすと `M5_ge_12` が型検査を通らないこと。
   **予想が外れたことをそのまま記録する**（分母から外していない）。
3. **M8 / M11 の副産物**: `native_decide` は「ピーク 6 なら鎖 `L_12` に到達できる」
   「ピーク 5 なら鎖 `L_11` に到達できる」を**計算として**返した。これは別途
   `chain12_peak6` / `chain11_peak5` で**明示スケジュール**として証明した内容と一致する。
   ⇒ 到達計算と明示証人が**独立に同じことを言っている**（両極性が出ている）。


---

## 3. 検算条項 — 鵜呑みにしなかったもの（食い違い 0）

REQUEST の「証人・`n*(5)=11`・既存 Lean の `sorry 0` も鵜呑みにせず確かめる」への答え。
**EXT-alloy と ren-fe のコードは 1 行も import していない**（`exp/extremal/*.py` を読まずに
`FINDINGS` §2 の定義文だけから独立の Python 検査器を書いた）。

| 検算対象 | やったこと | 結果 |
|---|---|---|
| 証人が定義を満たすか | 独立 Python: トポロジカル順・入次数 ≤ 2・sink 一意を `assert`、深さ 10・`T=21`、21 歩を 1 歩ずつ合法性判定 | ✅ 一致（ピーク 5） |
| 証人の `p_min` | 独立 Python の `2^n` 全数 BFS | ✅ `p_min = 5`（4 では不能） |
| `n*(5) = 11` | 独立 Python の全数 BFS | ✅ 鎖 `n=11 → 5`・`n=12 → 6` |
| 同上（Lean でも） | `chain11_peak5` ∧ `chain11_peak4_impossible` ⇒ `p_min(L_11) = 5`；`chain12_peak6` ∧ `chain12_peak5_impossible` ⇒ `p_min(L_12) = 6` | ✅ 台帳 `Q13` / `R-Q2-01` の値を再現 |
| 既存 Lean の「`sorry` 0」 | 本ファイル以前からある 10 ファイルすべてで `grep -c '\bsorry\b'` = 0。加えて `#print axioms` を主要 5 定理に実行（`sorryAx` は現れない） | ✅ 主張どおり |
| 既存 Lean の「公理は `[propext, Quot.sound]`」 | `par_time_exact_dag` / `time_lower_bound_seg` / `time_window_seg` / `par_time_exact_paD` / `par_time_exact_dag_two_sided` の 5 本 | ✅ 全部 `[propext, Quot.sound]` |
| 模型の一致（深さの数え方） | §0 の表 | ✅ 辺数で一致・ずれ無し |

**食い違いは 1 件も出なかった。**（出ていれば採用せず、食い違いそのものを報告する約束だった。）

⚠ **`M(5) = 12` の上端性・`M(6) = 18`・族が `p ≤ 9` で成立、は検算していない。**
本セッションが触ったのは `M(5) ≥ 12` と `p_min(L_11)`・`p_min(L_12)` だけである。

### テストファーストの形

`#eval` ではなく **`example … := by decide` を 8 本**置いた。理由: `#eval` は
**間違った数を印字してもビルドは緑のまま**なので回帰検出にならない。`example` なら
値がずれた瞬間にビルドが落ちる（実際、変異注入で落ちることを確認した）。
そのうち 1 本は**否定形** `¬ (∀ t ≤ 21, (wSched t).card ≤ 4)`——
「ピークが 5 未満ではない」を陽に検定しており、片極性だけの検査になっていない。

---

## 4. 層の判定材料（⚠ 昇格判断はしていない）

台帳の規則（`~/dev/CLAUDE.md`）を 1 つずつ当てる。

| 規則 | (A) `M(5) ≥ 12` | (B) 鎖 `L_12` はピーク 5 不可 |
|---|---|---|
| 「層 1 は定理証明系が緑にしたものだけ」 | ✅ Lean で緑（`M5_ge_12`） | ✅ Lean で緑（`chain12_peak5_impossible`） |
| 「有界事例の機械検証は層 1 にしない」 | **当たらない**。証人 1 個を検査しただけで、事例を**枚挙していない**。公理欄にも `native_decide` 由来のものが無い | ⛔ **当たる**。1,586 通りの配置 × 23 段を枚挙している。`native_decide` の補助公理が公理欄に立つ |
| 「ただし存在・反例の主張は 1 つの証人で一般の言明が閉じるので別扱い」 | ✅ この例外に該当（存在主張） | 該当しない（**非存在**主張） |
| 「judge が迷ったら上げずに保留（fail-closed）」 | 迷いなし | — |

**⇒ 判定材料**

1. **(A) は層 1 に届く。** 存在主張・証人 1 個・`native_decide` 不使用・
   公理は Mathlib 標準・`sorry` 0・変異注入で検出力を確認済み。
2. **(B) は層 1 にしない。** 有界全数検査なので台帳の規則に真正面から当たる。
   ただし**証拠の質は上がった**: これまで `cake_lpr` 検査済みの LRAT だけだったものが、
   **「符号化の正しさ自体が機械証明されている」**形（`mem_reach` ほかが無条件）で
   独立に再現された。SAT 側と Lean 側は符号化も探索原理も別なので、二重化の意味がある。
   ⚠ **反対意見も併記しておく**（判定材料として）: 「`native_decide` は未検証の神託ではなく
   Lean の証明手段の一つで、(B) は閉じた数学的言明として緑になっている」という読み方は
   在りうる。ただしそれを採ると `R-CBT-01` の線引きが動くので、**本セッションは
   fail-closed に倒して「層 1 にしない」を材料として出す**。決めるのは人間。
3. **合成命題「極値予想は偽」は (B) に律速される。** `chain_not_extremal` の公理欄には
   (B) 由来の `native_decide` 公理が立つ。よって**層 2 が上限**。
4. ⚠ **台帳 `R-Q2-14` の行をそのまま層 1 に上げることはできない。**
   行の `layer_note` は「層 1 は未達（証人が 12 頂点・21 ステップと小さいので **Lean 化すれば
   届く見込み**）」と書いている。**その Lean 化は本セッションで済み、(A) は届いた。**
   しかし行の `title` / `claim` が述べているのは「極値予想は偽」＝
   `M(5) ≥ 12`（＝(A)）**と** `n*(5) = 11`（＝(B) ＋ 鎖の下閉性）の**合成**であり、
   合成は弱いほうに律速される。したがって:
   * `M(5) ≥ 12` を独立した行に切り出せば、その行は層 1 の材料が揃っている。
   * 行をそのまま残すなら層 2 のままが規則に整合する。
   **どちらにするかは人間の判断。**（本セッションは `registry/` に一切触っていない。）
5. ⚠ **`M(5) ≠ n*(5)` の完全形には、まだ形式化されていない前提が 1 つある**（§1.3）。
   鎖の族の下閉性。Lean では `extremal_false_of_chain_monotone` の**引数として可視化**した。

---

## 5. まだやっていないこと

1. ⭐ **鎖の族の単調性（下閉性）を証明していない。** `ChainAchieves n p → ChainAchieves m p`
   (`m ≤ n`)。これが無いと `n*(5) ≤ 11` は `n = 12` の 1 点しか押さえられず、
   `M(5) ≠ n*(5)` は仮定つきのままになる。窓定理（`time_window_seg`）で
   `w_{n-2}` の窓が幅 2 に潰れることは使えるが、`L_n` の走行から `L_{n-1}` の走行を
   切り出す構成は見つからなかった。**別解として、`p` ペブルで鎖は `2^(p-1)` 頂点までしか
   届かない**（Knill 1995 Thm 2.3・台帳 `R-Q2-01` の注記）が使えれば
   `n ≤ 16` に落ちるので、`n = 13,14,15,16` の 4 点を全数検査すれば閉じる。
   ⚠ **その reach 上界も本ファイルでは形式化していない。**
2. **`p_min(証人) = 5` を Lean で閉じていない**（`≤ 5` までしか言っていない）。
   ピーク 4 が不能であることは独立 Python の全数 BFS で確認済み（層 2）。
   Lean 化するなら `reach wPa (range 12) 4 21` の全数検査（約 80 秒の追加ビルド）。
3. **`M(5) = 12`（上端）・`M(6) = 18`・族の `p ≤ 9` 成立は触っていない**（検算もしていない）。
   これらは `FINDINGS` §4.3 / §4.4 の主張のままである。
4. **(B) を `native_decide` なしで閉じていない。** 素朴な前向き到達計算は
   `1,586 × 1,586 × 23 ≈ 2,400 万`回の合法性判定になり、Lean の**カーネル** `decide` では
   桁が足りない（native で約 65 秒）。前後両方向から詰める中間一致法なら
   約 10 分の 1 になる見込みだが、健全性補題がもう 1 本要る。**やっていない。**
5. **入次数 3 以上のクラスは見ていない**（予想の定義外）。
6. **新規性の確認をしていない。** `R-Q2-14` の `novelty_check` は空欄のまま。
   本セッションの仕事は形式化であって文献調査ではない。
7. **`registry/` を一切触っていない**（台帳は ren-fe が持っている）。
   `notes/pbcert/`・`scripts/pbcert_*`・`notes/ic3/`・`scripts/ic3_*` にも触っていない。
8. **`git commit` していない**（ユーザー判断待ち）。push もしていない。

---

## 6. 成果物

| ファイル | 中身 |
|---|---|
| `lean/Revgarbage/ParPebbleExtremal.lean` | 本体（新規） |
| `lean/Revgarbage.lean` | `import Revgarbage.ParPebbleExtremal` を 1 行追加 |
| `lean/EXTREMAL_MANIFEST.md` | 本文書 |

再現手順:

```bash
cd lean
runcap -m 32 -t 3000 -- lake build          # 約 90 秒（うち native_decide が約 85 秒）
ls -l .lake/build/lib/lean/Revgarbage/ParPebbleExtremal.olean
```
