# P5 定理 1 の Lean 4 形式化 — 結果（2026-10-15 23:40 更新。履歴は末尾）

依頼: `p5/lean/REQUEST.md`。対象: 原稿 `2026-WiNF/P5-tree-exponent.tex` 定理 1
「任意の根付き木 T で M(T, R•(T)) ≤ 3^{R•(T)−1}」。

## 0. 結論（先に）

- **決定点の向き「T が S 個で可逆ペブリングできる ⇒ 深さ S 以下の strategy tree がある」は証明できた。**
  KSS Lemma 10 の両向きが `RootedTree.stratTree_iff_pebbling` として緑（追加公理なし・sorry なし）。
  KSS は Chan の Theorem 5（DT = R• = RM）に帰着しているが、ここでは Chan CCC 2013 の
  Lemma 3.22（構成）と Lemma 3.23/3.25（可逆戦略の値 ≥ Raz–McKenzie 値）を一般 DAG で直接形式化した。
- **定理 1 は `RootedTree.theorem1` として緑**。一般 DAG 版 `exists_fast_pebbling`（任意の非巡回有向グラフで
  M(G, R•(G)) ≤ 3^{R•(G)−1}）の系として得ている。
- **原稿の形 M(T,k) ≤ F(T,k) ≤ 3^{k−1}（中間項 F = 木の Knill 型再帰）も `RootedTree.theorem1_F` として緑**（§2.3）。
- **仮定なしの形も緑**: どの根付き木も可逆ペブリングできる（`exists_pebbling`）ので `R•(T)` が無条件に定義でき、
  `M_Rbullet_le : M(T, R•(T)) ≤ 3^{R•(T)−1}`・`theorem1_Rbullet`・`theorem1_F_Rbullet`（§2.4）。
- 公理は `propext, Classical.choice, Quot.sound` のみ（主定理 20 本すべて）。変異注入 13/13 検出・対照 5/5 緑。
- 層の判定は依頼元が行う（私見: `theorem1`・`stratTree_iff_pebbling`・`exists_fast_pebbling` は「定理証明系が
  公理なしで緑にしたもの」に当たる。テストファイルは有界事例で層 1 ではない）。

## 1. 置き場所（新規ファイルのみ。既存ファイルは未編集。`Revgarbage.lean` には未追加）

| ファイル | 行数 | 内容 |
|---|---|---|
| `lean/Revgarbage/P5TreeGame.lean` | 873 | 一般 DAG の可逆ペブリング・`ValLE`・構成（手数計数）・難しい向き・主定理 |
| `lean/Revgarbage/P5TreeStrat.lean` | 397 | 根付き木・strategy tree（KSS Def. 9）・Lemma 10 両向き・定理 1 |
| `lean/Revgarbage/P5TreeF.lean` | 260 | 木の Knill 型再帰 `F`（原稿 §4 定義 1）・`M ≤ F`・`F ≤ 3^{d−1}`・`theorem1_F` |
| `lean/Revgarbage/P5TreeExists.lean` | 70 | どの木もペブリングできる（深さ `|W|` の strategy tree）→ 仮定なしの `R•` と定理 1 |
| `lean/Revgarbage/P5TreeTests.lean` | 125 | 有界事例の計算チェック（`decide`/`native_decide`。層 1 の根拠ではない） |

## 2. 証明した定理（Lean の文、逐語）

### 2.1 一般 DAG 版（`P5TreeGame.lean`）

模型（`P5TreeGame.lean:39–65`）:
```lean
def Step (pred : V → Finset V) (B P Q : Finset V) : Prop :=
  ∃ v, pred v ⊆ P.erase v ∪ B ∧ ((v ∉ P ∧ Q = insert v P) ∨ (v ∈ P ∧ Q = P.erase v))
def Pebbling (pred : V → Finset V) (B a b : Finset V) (k n : ℕ) : Prop :=
  ∃ L : List (Finset V), L.head? = some a ∧ L.getLast? = some b ∧ L.IsChain (Step pred B) ∧
    (∀ Q ∈ L, Q.card ≤ k) ∧ L.length ≤ n + 1
inductive ValLE (pred : V → Finset V) : Finset V → Finset V → ℕ → Prop
  | base {B R h} (r : V) (hr : r ∈ R) (hp : pred r ⊆ B) (hh : 1 ≤ h) : ValLE pred B R h
  | step {B R h} (v : V) (h1 : ValLE pred B (insert v R) h) (h2 : ValLE pred (insert v B) R h) :
      ValLE pred B R (h + 1)
```
`pred v` = `v` の入近傍（木では子）。`B` = 仮定（置いてあるとみなす）集合（Chan Def. 3.20 の S）。
`Pebbling pred ∅ ∅ {t} k n` = 「空の盤から `{t}` へ、常に `k` 個以下、`n` 手以下」= persistent 可逆ペブリング
（KSS Def. 3 の persistent 版。KSS の常設仮定 "In the rest of the paper, we use the term pebbling to refer to
persistent reversible pebbling unless explicitly stated otherwise."）。
`ValLE pred B R h` = Chan Prop. 3.18 の Raz–McKenzie 値の再帰を「値 ≤ h」の帰納的述語にしたもの。

構成（Chan Lemma 3.22 "run P1, then run P2, and finally run P1 in reverse" の手数を数える）`P5TreeGame.lean:397`:
```lean
theorem ValLE.pebbling {pred : V → Finset V} {B R : Finset V} {h : ℕ} (hv : ValLE pred B R h) :
    ∃ t ∈ R, Pebbling pred B ∅ {t} h (3 ^ (h - 1))
```
難しい向き（Chan Lemma 3.25 / 3.23）`P5TreeGame.lean:468, 667`:
```lean
theorem hard_aux (pred : V → Finset V)
    (hacyc : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ pred b) v v) :
    ∀ ℓ (B R : Finset V) (P : ℕ → Finset V) (c : ℕ), 0 < ℓ →
      (∀ i, i + 1 < ℓ → Adj pred B (P i) (P (i + 1))) →
      (∃ r ∈ R, pred r ⊆ P (ℓ - 1) ∪ B) →
      (∀ i < ℓ, (P i \ (stay P 0 ℓ ∪ B)).card ≤ c) →
      ValLE pred (stay P 0 ℓ ∪ B) R (c + 1)
theorem valLE_of_pebbling {pred : V → Finset V}
    (hacyc : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ pred b) v v)
    {B : Finset V} {t : V} {k n : ℕ} (h : Pebbling pred B ∅ {t} k n)
    {R : Finset V} (ht : t ∈ R) : ValLE pred B R k
```
主定理 `P5TreeGame.lean:790, 821`:
```lean
theorem exists_fast_pebbling {pred : V → Finset V}
    (hacyc : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ pred b) v v)
    {B : Finset V} {t : V} {k : ℕ} (h : ∃ n, Pebbling pred B ∅ {t} k n) :
    Pebbling pred B ∅ {t} k (3 ^ (k - 1))
theorem M_Rb_le_three_pow {pred : V → Finset V}
    (hacyc : ∀ v, ¬ Relation.TransGen (fun a b => a ∈ pred b) v v)
    {B : Finset V} {t : V} (h : ∃ k n, Pebbling pred B ∅ {t} k n) :
    Mval (Nat.find_spec h) ≤ 3 ^ (Rb h - 1)
```
（`Rb h = Nat.find h` = R•、`Mval = Nat.find` = M。原稿 §5 の「任意の DAG G で M(G,R•(G)) ≤ 3^{R•(G)−1}」そのもの。）

### 2.2 木の側（`P5TreeStrat.lean`）

```lean
structure RootedTree (V : Type*) [Fintype V] [DecidableEq V] where
  root : V
  parent : V → V
  depth : V → ℕ
  parent_root : parent root = root
  depth_lt : ∀ u, u ≠ root → depth (parent u) < depth u
inductive StratTree (T : RootedTree V) : Finset V → V → ℕ → Prop      -- KSS Def. 9、深さ ≤ d
  | leaf {d : ℕ} (x : V) (hd : 1 ≤ d) : StratTree T {x} x d
  | split {W : Finset V} {x : V} {d : ℕ} (u : V) (hu : u ∈ W) (hux : u ≠ x)
      (hl : StratTree T (W ∩ T.desc u) u d) (hr : StratTree T (W \ T.desc u) x d) :
      StratTree T W x (d + 1)
```
`P5TreeStrat.lean:324, 341, 353, 362`:
```lean
theorem stratTree_iff_pebbling (k : ℕ) :
    StratTree T univ T.root k ↔ ∃ n, Pebbling T.children ∅ ∅ {T.root} k n            -- KSS Lemma 10（両向き）
theorem StratTree.pebbling_three_pow {d : ℕ} (hs : StratTree T univ T.root d) :
    Pebbling T.children ∅ ∅ {T.root} d (3 ^ (d - 1))                                 -- 深さ d ⇒ d 個で 3^{d−1} 手
theorem theorem1 {k : ℕ} (h : ∃ n, Pebbling T.children ∅ ∅ {T.root} k n) :
    StratTree T univ T.root k ∧ Pebbling T.children ∅ ∅ {T.root} k (3 ^ (k - 1))   -- 定理 1
theorem M_Rb_le (h : ∃ k n, Pebbling T.children ∅ ∅ {T.root} k n) :
    Mval (Nat.find_spec h) ≤ 3 ^ (Rb h - 1)                                         -- M(T,R•(T)) ≤ 3^{R•(T)−1}
```

### 2.3 原稿の形（`P5TreeF.lean`）

```lean
def F (W : Finset V) (x : V) : ℕ → ℕ∞                      -- 原稿 §4 定義 1（S = 0 で ⊤ = ∞）
  | 0 => ⊤
  | S + 1 =>
    if hx : x ∈ W then
      if W = {x} then 1
      else
        (T.splitters W x).attach.inf (fun u =>
          F (W ∩ T.desc u.1) u.1 (S + 1) + F (W ∩ T.desc u.1) u.1 S + F (W \ T.desc u.1) x S)
    else ⊤
```
（`splitters W x` = `W.erase x` のうち `x` が子孫でないもの。部分問題では `W.erase x` 全体（`SubProb.splitters_eq`）。）
`P5TreeF.lean:123, 155, 232, 246`:
```lean
theorem F_le_three_pow {W : Finset V} {x : V} {d : ℕ} (hs : StratTree T W x d) (h : T.SubProb W x) :
    T.F W x d ≤ ((3 ^ (d - 1) : ℕ) : ℕ∞)                                   -- 原稿 定理 1 の帰納法そのもの
theorem pebbling_of_F : ∀ (W : Finset V) {x : V} {S n : ℕ}, T.SubProb W x →
    T.F W x S = (n : ℕ∞) → Pebbling T.children (univ \ W) ∅ {x} S n          -- M ≤ F（構成）
theorem theorem1_F {k : ℕ} (h : ∃ n, Pebbling T.children ∅ ∅ {T.root} k n) :
    ∃ n : ℕ, T.F univ T.root k = (n : ℕ∞) ∧ Pebbling T.children ∅ ∅ {T.root} k n ∧ n ≤ 3 ^ (k - 1)
theorem M_le_F {k n : ℕ} (h : ∃ n, Pebbling T.children ∅ ∅ {T.root} k n)
    (hF : T.F univ T.root k = (n : ℕ∞)) : Mval h ≤ n
```
`theorem1_F` が原稿の定理 1「M(T,R•(T)) ≤ F(T,R•(T)) ≤ 3^{R•(T)−1}」の形（`k = R•(T)` を入れる）。
`F` は `S` について非増加（`F_antitone`。原稿の「F は S について非増加なので」）。

### 2.4 仮定なしの形（`P5TreeExists.lean`）

```lean
theorem exists_stratTree : ∀ (W : Finset V) {x : V}, T.SubProb W x → StratTree T W x W.card
theorem exists_pebbling : ∃ k n, Pebbling T.children ∅ ∅ {T.root} k n
noncomputable def Rbullet : ℕ := Nat.find T.exists_pebbling                          -- R•(T)
theorem M_Rbullet_le : Mval (Nat.find_spec T.exists_pebbling) ≤ 3 ^ (T.Rbullet - 1)  -- M(T,R•(T)) ≤ 3^{R•(T)−1}
theorem theorem1_Rbullet :
    StratTree T univ T.root T.Rbullet ∧
      Pebbling T.children ∅ ∅ {T.root} T.Rbullet (3 ^ (T.Rbullet - 1))
theorem theorem1_F_Rbullet :
    ∃ n : ℕ, T.F univ T.root T.Rbullet = (n : ℕ∞) ∧
      Pebbling T.children ∅ ∅ {T.root} T.Rbullet n ∧ n ≤ 3 ^ (T.Rbullet - 1)         -- 原稿の形、仮定なし
```

## 3. `#print axioms`（2026-10-15 23:19・23:33、10-16 00:07 実行）

```
'P5Tree.ValLE.pebbling' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.hard_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.valLE_of_pebbling' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.exists_fast_pebbling' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.M_le_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.M_Rb_le_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.stratTree_iff_pebbling' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.StratTree.pebbling_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.theorem1' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.theorem1_pebbling' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.M_Rb_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```
'P5Tree.RootedTree.F_le_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.pebbling_of_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.theorem1_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.M_le_F' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.F_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
```
```
'P5Tree.RootedTree.exists_pebbling' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.M_Rbullet_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.theorem1_Rbullet' depends on axioms: [propext, Classical.choice, Quot.sound]
'P5Tree.RootedTree.theorem1_F_Rbullet' depends on axioms: [propext, Classical.choice, Quot.sound]
```
ソース中の `sorry`/`admit`: 0（5 ファイル）。`axiom` 宣言: 0。

## 4. ビルドの証拠（`lake env lean -o … -i …` で単体検査。成否は `.olean` の生成で確認）

```
.lake/build/lib/lean/Revgarbage/P5TreeGame.olean   2542192  2026-10-15 23:20:58 +0900（初回 23:12:39、gatekeeper が再生成）
.lake/build/lib/lean/Revgarbage/P5TreeStrat.olean   760368  2026-10-15 23:21:10 +0900（初回 23:14:36、同上）
.lake/build/lib/lean/Revgarbage/P5TreeF.olean       669328  2026-10-15 23:27:33 +0900
.lake/build/lib/lean/Revgarbage/P5TreeTests.olean   115120  2026-10-15 23:27:51 +0900
.lake/build/lib/lean/Revgarbage/P5TreeExists.olean  120368  2026-10-16 00:06:35 +0900
```
各 4〜28 秒・最大 1.8GB。終了コード 0・`error` 0。

## 5. 変異注入（リポジトリ外の写し。`packagesDir` を本体の Mathlib に向けた一時プロジェクト）

対照（無変異）: Game / Strat / F / Tests / Exists の 5 本とも rc=0・error 0（**誤検出 0**）。変異 **13/13 検出**:

| 変異 | 場所 | 結果 |
|---|---|---|
| M1 `ValLE.pebbling` の `3^(h-1)` → `3^(h-2)` | Game:398 | 検出（omega 失敗 4 件） |
| M2 `Step` の合法性条件 → `True` | Game:40 | 検出（12 件。定義が証明で使われている） |
| M3 `ValLE.step` の `insert v B` → `B`（仮定を忘れる） | Game:62 | 検出（18 件） |
| M4 `hard_aux` の結論 `c + 1` → `c` | Game:473 | 検出（5 件） |
| M5 `theorem1` のペブル数 `k` → `k - 1` | Strat:354 | 検出（2 件） |
| M6 `StratTree.of_valLE` の深さ `d` → `d - 1` | Strat:285 | 検出（3 件） |
| M7 `exists_fast_pebbling` の `3^(k-1)` → `3^(k-2)` | Game:793 | 検出（2 件） |
| M8 `F_le_three_pow` の `3^(d-1)` → `3^(d-2)` | F:124 | 検出（4 件） |
| M9 `F_antitone_succ` の向きを逆に | F:91 | 検出（3 件） |
| M10 `pebbling_of_F` の手数 `n` → `n - 1` | F:156 | 検出（7 件） |
| M11 `F` の葉の値 `1` → `2` | F:53 | 検出（1 件。`F_leaf` が値を固定） |
| M12 `exists_stratTree` の深さ `W.card` → `W.card - 1` | Exists:18 | 検出 |
| M13 `M_Rbullet_le` の `3^(R•-1)` → `3^(R•-2)` | Exists:51 | 検出 |

M1・M4〜M10・M12・M13 は偽の主張（必ず落ちるべきもの）、M2・M3・M11 は定義の改変（主張が弱くなる／偽になる）。

## 6. テスト（`P5TreeTests.lean`。期待値は `p5_tree_count.py` の `bfs_M`、2026-10-15 実行）

- 模型: 原稿 図 1 の 5 手（∅,{a},{a,b},{a,b,r},{b,r},{r}）が `Pebbling T2.children ∅ ∅ {0} 3 5` の証人（`decide`）。
  違法手の棄却（子が無い根を外す・根だけの盤から根を外す）も `decide`。
- BFS（Lean 内で `Step` を使って独立に書いた `bfsM`）と Python の BFS の一致:
  T_2: (3)→5, (2)→なし; star3: (4)→7, (3)→なし; chain4: (3)→9, (4)→7, (2)→なし; T_3: (5)→17, (6)→15, (4)→なし。
- `ValLE`（= strategy tree の深さ）: T_2 は 3 で可・2 で不可、star3 4/3、chain4 3/2、T_3 5/4（p_min と一致）。
- `StratTree`（KSS Def. 9 を直接）: T_2 3/2、chain4 3/2、T_3 5/4。
- 鎖 4 頂点では 9 = 3^{3−1} で上界に等号（Bennett）。
- `F`（Lean の再帰）と Python の `F`: T_2 (3)→5, (2)→⊤; star3 (4)→7, (3)→⊤; chain4 (3)→9, (4)→7;
  T_3 (5)→17, (6)→15, (7)→13, (4)→⊤（`native_decide`。原稿 表 2 の T_3 の列と一致）。

## 7. 一次資料との対応と注意

- Chan Lemma 3.25 の証明（txt 979–1040 行）は "Decrease ℓ if necessary"（最初に δin(r) ⊆ P_ℓ ∪ B となる時刻で打ち切る）
  から始まるが、**打ち切ると P̃（居続ける集合）が大きくなり、Val(P̃,R) の単調性は逆向きなので、そのままでは帰納法の
  結論を元の P̃ に戻せない**。本形式化では打ち切りを使わず（`hard_aux` は与えられた長さのまま）、
  「最初に最後まで居続ける頂点 v」で Pebbling case（v を仮定へ）と Unpebbling case（v の真の先行頂点へ制限して逆走）
  の**両方**の部分戦略を無条件に作り、`ValLE.step` で合成した（Chan は "at least one of the following is true" の
  場合分けだが、帰納的述語では両方要り、両方とも成り立つ）。Chan の V_v(v) への制限は非巡回性を使う唯一の箇所
  （`hacyc`。木では `RootedTree.acyclic`）。
- `Step` の合法性は `pred v ⊆ P.erase v ∪ B`（Chan Def. 3.20 の「δin(v) ⊆ P₁ ∪ S、同値に ⊆ P₂ ∪ S」のとおり前後対称）。
  自己ループが無い（非巡回）なら `P ∪ B` と同じで、原稿 §3・`p5_tree_count.py` の `bfs_M`（`(x & need[v]) == need[v]`）と一致する。
- 停留（同じ配置の繰り返し）は `Adj` で許し、`Pebbling` は真の手 `Step` の列（`exists_destutter` で除去）。
  手数 = 配置列の長さ − 1。
- `ValLE` は Chan の再帰で `v ∉ R ∪ B` の側条件を落としている（落としても導出できるものは単調性で既に導出可能。
  構成の証明でも側条件は不要）。
- R• と M は `Nat.find`（`Mval`/`Rb`）。存在の仮定 `∃ k n, Pebbling …` は木なら常に成り立つが、その証明は未着手（§8）。
- **F = M は証明していない（証明したのは M ≤ F だけ）。** 別セッション p5/fm（2026-10-15）が 15 頂点・S=6 で
  M=51 < F=53 の反例を見つけており（`p5/fm/RESULT.md`）、F は一般の木では M の厳密値ではない。
  本形式化の主張（M ≤ F ≤ 3^{R•−1}・M ≤ 3^{R•−1}）はその反例と矛盾しない。原稿の「F=M が成り立つなら厳密値」の
  条件文もそのまま。

## 8. まだやっていないこと（2026-10-15 23:30 時点）

1. （済: F の形式化は `P5TreeF.lean` で完了。§2.3）
2. 系（完全二分木）`R•(T_h) ≤ h + O(log* h)`（Královič 2004・CLNV Thm 3.3）: 私は未着手。
   **別セッションが `lean/Revgarbage/P5TreeCBT.lean`（2026-10-16 00:06、未追跡）で、本形式化の `M_Rb_le`・
   `stratTree_iff_pebbling` の上に `R•(T_h) ≤ h + ⌈log₂ h⌉` と `M(T_h,R•(T_h)) ≤ n^{log₂3+o(1)}` を書いている**
   （ヘッダのみ確認。検査はそのセッションの責任）。
3. （済: `exists_pebbling`。`M_Rbullet_le` は仮定なし。§2.4）
4. `proof-gatekeeper` の独立検査: 実行中（結果は §9 に追記）。
5. `Revgarbage.lean` への登録: 未実施（既存ファイルは触らない）。
6. `git commit`: Lean 4 ファイルは **別セッション（依頼元 "sf2"）が `e909c34`（2026-10-15 23:52）でコミット済み**
   （その時点の内容 = 現在の内容。差分なし。コミット文に「独立の proof-gatekeeper を sf2 で通過・変異 9/9 検出」とある）。
   私からは `lean/Revgarbage/P5TreeExists.lean`（e909c34 の後に追加）と `p5/lean/RESULT.md`・`REQUEST.md` だけを
   ファイル名を列挙してコミットする（push しない）。

## 9. gatekeeper の判定（独立検査。`proof-gatekeeper` サブエージェント、2026-10-16 00:09 報告）

対象はコミット `e909c34` の 4 ファイル（Game / Strat / F / Tests）。**総合判定: 緑（5 点ゲート通過）。**
- ビルド: 4 ファイルとも rc=0、`.olean` を再生成（内容ハッシュは私のものと同一。リポジトリへの書き込みはそれ以外なし）。
- 公理: 4 ファイルの**全 328 定数**が `propext` / `Classical.choice` / `Quot.sound` のみ。
- sorry / axiom: 0。
- 変異注入: **27 本すべて検出**、中立変異 5 本の**誤検出 0**（私の 13 本とは独立に選んだもの）。
- 照合: Lean の `bfsM`・`ValLE`・`StratTree`・`F` を Python（`p5_tree_count.py`）と **85 本の木**で突き合わせ、不一致 0。
- 未検査（gatekeeper の申告）: `lake build` そのもの（`Revgarbage.lean` 未登録のため単体検査のみ）、KSS 原文の深さ規約の照合、
  `P5TreeExists.lean`（追加で依頼中）と別セッションの `P5TreeCBT.lean`、F のビルド時間の差。
- gatekeeper 自身の Notion 作業ログ追記は、依頼の「外部へ書き込まない」に従い未実施（依頼元が 1 日 1 行を書く）。

## 履歴
- 2026-10-15 23:30 中間報告（構成・難しい向き・木の両向き・定理 1 まで緑）。
- 2026-10-15 23:40 F（原稿の中間項）を追加。`theorem1_F` 緑。変異 11/11・対照 4/4。gatekeeper は実行中。
- 2026-10-16 00:07 仮定なしの形（`P5TreeExists.lean`）を追加。変異 13/13・対照 5/5。
