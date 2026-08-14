# サーベイ: `reach(p,e)` の既知性（2026-08-10）

**このファイルの目的**: 同じ調査を二度やらないため。将来のセッションは、
`reach(p,e)` の新規性を論じる前に**まずここを読むこと**。

対象: 定理 B2 `reach(p,e) = (e+2)·2^{p-2}`（消去予算 e つき可逆ペブリングで、
p 個のペブルと e 回の不可逆消去で到達できる鎖の最大長）。

---

## 0. 結論（3 行）

1. **モデルは新しくない。** 消去予算つき可逆ペブリングは
   **Buhrman–Tromp–Vitányi 1997（quant-ph/9703009）が導入**している
2. **構成の形も新しくない。** 同論文 Lemma 1 が `(e+1)·2^{p-2}` を与える。
   **我々の B1 は `(e+2)·2^{p-2}` で、定数が 1 だけ良い**
3. **一般 e での「これが最適」（上界＝不可能性）は、BTV には見当たらない。**
   同論文 Theorem 2(i) の不可能性は**消去なしの場合のみ**。
   → **新規性があるとすれば「厳密性（一致する上界）」と「定数の +1」**

⚠ **定数の差は、数え方の違いである可能性が残っている**（§4）。ここを詰めるまで
「改善した」と書いてはいけない。

---

## 1. 一次情報（本文 PDF で確認済み）

### Buhrman, Tromp, Vitányi (1997) — **消去予算モデルの初出**

- `Reversible Simulation of Irreversible Computation by Pebble Games`
- arXiv **quant-ph/9703009**、本文 PDF: `https://homepages.cwi.nl/~paulv/papers/pebbles.pdf`
- Paperpile には**未収録**（2026-08-10 時点）。上の URL から直接取れる

アブストラクトに明記:

> We also **introduce irreversible steps** and give a **theorem on the tradeoff between
> the number of allowed irreversible steps and the memory gain** in the pebble game.
> In this resource-bounded setting the limited erasing needs to be performed at
> precise instants during the simulation.

**Lemma 1（本文で確認・逐語）**:

> There is a winning strategy with **`n+2` pebbles and `m-1` erasures** for pebble games
> `G` with **`T_G = m·2^n`**, for all `m ≥ 1`.

`p := n+2`、`e := m-1` と置くと

$$\mathrm{reach}_{\mathrm{BTV}}(p,e) \;\ge\; (e+1)\cdot 2^{p-2}$$

構成は「**2 個のペブルを踏み台（springboard）として交互に `2^n` ずつ前へ置き、
残り `n` 個で距離を橋渡しする。後方の踏み台は、それと前方の踏み台の間から
`n` 個が全部退いた時点で消去できる**」。擬似 PASCAL の手続き `A(n,m,G)` が本文にある。

**Theorem 2（Space-Irreversibility Trade-off、本文で確認・逐語）**:

> (i) Pebble games `G` of size `2^n − 1` can be won using `n` pebbles but **not using
> `n−1` pebbles**.
> (ii) If `G` is a pebble game with a winning strategy using `n` pebbles without erasures,
> then there is also a winning strategy for `G` using `E` erasures and `n − log(E+1)`
> pebbles (**for `E` an odd integer at least 1**).

- **(ii) は達成可能性（構成側）だけ。** 「これ以上は無理」は述べていない
- **(i) の不可能性は `E = 0` の場合のみ**
- **`E` が奇数に制限**されている。我々の定式化は全ての `e` を扱う

**Corollary 2**:

> The maximum reachable node with `n` pebbles is `Σ_{i<n} 2^i = 2^n − 1`.

→ **これが `τ_0 = 2^p − 1`**（`data/ic3_b2_tight_support.md` が Královič と一致すると
書いたもの）。BTV にも同じ形で載っている。

### Královič (2004) — **消去は扱っていない**

- `Time and Space Complexity of Reversible Pebbling`
- Paperpile: `All Papers/K/Královič 2004 - Time and space complexity of reversible pebbling.pdf`
  （博士論文 `kralovic-thesis-2004.pdf` も同ディレクトリ）
- **`Corollary 4.5: S^{-1}(p) = 2^p − 1`** を確認。`τ_0` と一致
- **本文の "irreversible" はすべて Bennett 型の「不可逆計算の可逆シミュレーション」**。
  **消去予算つきのペブリングゲームは扱っていない**（`grep -i erasur|budget` の結果 0 件）

---

## 2. 隣接する研究（今回の主張とは別のモデル）

**混同しやすいので、違いを明記する。**

| 研究 | 何を緩めているか | 我々のモデルとの関係 |
|---|---|---|
| **spooky pebble game**（Gidney、2110.08973 / 2401.10579 / 2510.08432） | **測定**（Hadamard 基底）で量子ビットを再利用。spooky pebble は後で解消が必要 | **別モデル**。消去は「予算を消費して恒久的に捨てる」のに対し、spooky は「後で払う借金」 |
| Komarath–Sarma–Sunil（1604.05510） | 木上の可逆ペブリング数と彩色の関係 | 消去なし |
| 2305.19104 | ペブルゲームの判定問題の困難性 | 消去なし |
| Meuli et al. 2019 | 量子メモリ管理への応用（Paperpile 収録） | 消去なし |

**memory `kornerup-not-a-misattribution` に関連**: spooky pebble game は 2024/2025 の実在の研究。
年を確認してから言及すること。

---

## 3. したがって、新規性があるとすれば

| 主張 | 既知か | 根拠 |
|---|---|---|
| 消去予算つきペブリングというモデル | **既知**（BTV 1997） | 本文で確認 |
| `τ_0 = 2^p − 1` | **既知**（BTV Cor.2 / Královič Cor.4.5） | 本文で確認 |
| 構成が `m·2^{p-2}` の形 | **既知**（BTV Lemma 1） | 本文で確認 |
| **定数 `(e+2)` vs BTV の `(e+1)`** | **要確認**（§4） | 数え方の違いの可能性 |
| **一般 `e` での一致する上界（＝最適性）** | **BTV には見当たらない** | Thm 2(i) は `E=0` のみ |
| **機械証明（Lean、標準3公理のみ）** | 見当たらない | 前方引用は未調査（§5） |

---

## 4. ⚠ 最優先で潰すべき穴: 定数の +1 は本物か

`(e+2)` と `(e+1)` の差は、**次のどれかで説明がつく可能性がある**:

1. **踏み台ペブルの数え方。** BTV は「node 0 の permanent pebble を勘定に入れると `n+1`」と
   別の箇所で書いている（本文 9 頁）。`p = n+2` の +2 が何を含むかの定義がずれていないか
2. **消去イベントの数え方。** BTV の `m-1` は「最後の踏み台は消さない」ことから来る。
   我々の `e` が同じイベントを数えているか
3. **鎖の長さの数え方。** `T_G` が辺の数か頂点の数か。`reach` が到達する頂点番号か長さか

**やること**: BTV の手続き `A(n,m,G)` を我々の意味論で実行し、
`scripts/revpebble.py` の `bfs` で**同じ入力に対する両者の値を突き合わせる**。
一致すれば数え方の違い、我々の方が 1 大きければ本物の改善。

**これが済むまで「BTV を改善した」と書かないこと。**

---

## 5. まだやっていないこと（正直に）

- **前方引用の追跡**（BTV 1997 を引用している論文で、一般 `e` の最適性を論じたものが無いか）。
  Semantic Scholar の citations API で辿れる。**未実施**
- BTV の**ジャーナル版**（この PDF はプレプリント。SIAM J. Comput. 版があるはず）の確認
- Bennett 1989 の原論文における erasure の扱い
- **「無い」ことの証明にはなっていない。** 上の表の「見当たらない」は
  「検索した範囲で見つからなかった」であって、存在しないことの根拠ではない

---

## 6. 調査に使った手段（再現用）

```sh
# Paperpile の現物
rclone lsf gdrive:Paperpile -R | grep -i pebbling
rclone copy "gdrive:Paperpile/All Papers/K/Královič 2004 - ....pdf" /tmp/survey/

# BTV は Paperpile 未収録。直接取得
curl -sSL -o pebbles.pdf https://homepages.cwi.nl/~paulv/papers/pebbles.pdf
pdftotext -layout pebbles.pdf bt.txt     # -raw も併用（数式の欠落が違う）
```

**`pdftotext -layout` は数式を壊す**（`2^n − 1` が `2n 1` になる）。
**`-raw` と併用**して両方で読むこと。定数を読むときは特に。

---

## 7. ⚠ §0〜§4 の訂正（2026-08-10、同日中に自己訂正）

**「定数が 1 だけ良い」は誤り。比較していた 2 つの量が別物だった。**

arXiv の **LaTeX ソース**（`https://arxiv.org/e-print/quant-ph/9703009`）で
定義まで読んだ結果:

BTV §Reachable Pebble Configurations の `pebble(s,n)` は

> the task of **pebbling nodes `s+1,…,s+2^n−1`** … then placing a free pebble
> on node `s+2^{n-1}`, then unpebbling … and finally pebbling nodes
> `s+2^{n-1}+1,…,s+2^n−1` using these pebbles

**終了時に `n` 個のペブルが盤上に残る**（`s+2^{n-1}`, `s+2^{n-1}+2^{n-2}`, … と
最終ノード）。**clean ではない。**

一方、我々の `reach(p,e)` は **clean 到達**（最後は目標だけが載っている）。
`scripts/cpsat_interval.py` の定式化がそうなっている。

**したがって:**

| | BTV | 我々 |
|---|---|---|
| 終端条件 | ペブルが `n` 個残る（non-clean） | **目標のみ（clean）** |
| `e=0` の値 | `2^p − 1`（Thm 2(i)） | `2^{p-1}`（B2） |
| 対応する我々の量 | **`τ_0`（触れる限界）** | `reach`（clean 到達） |

**`(e+1)` と `(e+2)` を並べたのは、`τ` 系の量と `reach` 系の量を並べたことになる。
比較として成立していない。**

### 何が残るか

- **`τ_0 = 2^p − 1` は BTV Thm 2(i) と一致**（既知。Královič Cor 4.5 とも一致）
- **BTV の Lemma 1 は `τ`（non-clean）側の消去つきトレードオフ**。
  `τ(p,e) ≥ (e+1)·2^{p-2}` に相当する
- **我々の `reach`（clean）側に、消去つきの先行結果があるかは未確認。**
  §5 の「まだやっていないこと」に、この観点での再調査を追加する

### 教訓（この誤りの型）

**OCR の誤りと、意味の取り違えは別の問題である。**
- `2^n − 1` が `2n 1` になる → **arXiv ソースで解決した**
- **`τ` と `reach` を混同した → どんな抽出ツールでも防げない。**
  定義を読むことと、具体値での検算でしか防げない

今回は「`e=0` で BTV が `2^p−1`、我々が `2^{p-1}`」という**数値の食い違い**に
気づいたことで発覚した。**式を読んだら必ず小さい具体値を入れて突き合わせること。**

---

## 8. 前方引用の全数追跡（2026-08-10、§5 の宿題を消化）

**BTV 1997 の被引用 22 件を全数確認した。`clean` 側で消去予算つきの
トレードオフ／最適性を論じたものは無い。**

```sh
# paperId は quant-ph/9703009 → e3c4e5caeee4b0b87ffc871367bb164e79e14d6d
curl -s "https://api.semanticscholar.org/graph/v1/paper/<id>/citations?fields=title,year,abstract,externalIds&limit=100"
```

⚠ **1 回目の呼び出しは `citationCount:22` なのに `data:[]` を返した。**
再試行で 22 件が出た。[[api-error-parsed-as-zero-hits]] の型。
**存在確実な論文で健全性チェックを挟むこと**（今回それで気づいた）。

### 紛らわしくて潰したもの

| 論文 | なぜ先行研究でないか |
|---|---|
| **Are all reversible computations tidy?** (quant-ph/0403079, 2004) | **"tidy" は Bennett の後始末＝clean に近い用語**だが、対象は**量子**。「Bennett の uncompute が量子で一般化できるか（＝できない類がある）」の話で、**空間と消去のトレードオフではない** |
| Grochow–Wolpert, *Beyond Number of Bit Erasures* (SIGACT News 2018) | 非平衡統計力学の新しいコスト概念に基づく**未解決問題の提起**。ペブリングの量ではない |
| Nullstellensatz Size-Degree Trade-offs from Reversible Pebbling (2019) | 証明複雑性への応用。**消去なし** |
| Tight Bounds on the Spooky Pebble Game (2021) | 別モデル（測定で再利用）。§2 参照 |

### したがって現時点の判定

- **`reach(p,e)`（clean・一般 `e`・一致する上界）の先行研究は、
  BTV の被引用を全数見た範囲で見つからない**
- **これは「無い」ことの証明ではない。** BTV を引用せずに同じ量を扱った文献は
  この方法では見つからない。ただし**このモデルの初出が BTV である以上、
  取りこぼしの確率は低い**と判断する
- 残る宿題: BTV の**ジャーナル版**（SIAM J. Comput.）、**Bennett 1989** の erasure の扱い

---

## 追記（2026-08-11）: RC 2025 の鮮度確認

RC（Reversible Computation）2011–2026 の会議録が全巻そろったので、**最新巻 RC 2025**
（17th, Odense, Glück–Kaarsgaard 編, 175 頁）を走査した。

- **可逆ペブリング（pebbling）の論文は 0 件**（全文検索で該当なし）。
  → 定理 B1/B2・予想 U/G と**衝突する新結果は無い**。
- 隣接して注意すべき 1 本: **ゼロガベージ計算の暗黙的計算量**（`ForNo` 言語で
  FPTIME 健全性をゼロガベージ両方向全単射により特徴づける）。
  これは `docs/idea10_minimum_garbage.md`・memory `garbage-minimality-yardstick` の
  「ゴミ最小性」テーマに**直接隣接する**。ゴミ量の研究に着手する前に本文精読が要る。
- RC 2025 の PC には横山（本研究室）が入っている。

**運用**: 会議録の所蔵状況は `~/dev/infra/idea-factory/CORPUS_GAPS.md` が正本。
新規性を論じる前にそこで「自分が読める範囲がどこで切れているか」を確認すること
（2026-08-11 の RLEM 2-17 の事故＝所蔵外で解決済みだった、の再発防止）。
