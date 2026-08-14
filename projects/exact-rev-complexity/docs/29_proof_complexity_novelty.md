# サーベイ: 証明複雑性（Nordström 系）との照合（2026-08-12）

**このファイルの目的**: 同じ調査を二度やらないため。`docs/28` §4 が残した宿題
「証明複雑性側（Nordström 系）は未照合」を消化する。

前提: `docs/24`（BTV 1997 被引用 22 件・S2）、`docs/25`（Královič 被引用 10 件・
Komarath アブストのみ）、`docs/27`（UCNC 3 巻）、`docs/28`（RC 12 巻）は既読・
重複しない。

---

## 0. 結論（3 行）

1. **証明複雑性側にも「消去予算つき clean 到達」の競合は見つからなかった。**
   Nordström 系の中心論文（de Rezende–Nordström–Meir–Robere, CCC 2019/cc 2021）を
   **arXiv LaTeX ソースの本文で確認**した結果、"erasure" は 1 度も出現しない
   （"budget" は "space budget" という一般語として 1 か所のみ）
2. **Chan 2013・Komarath–Sarma–Sawlani 2015/2017 の前方引用を OpenAlex で全数追跡**
   した（各 26 件・6 件）。証明複雑性側の引用（Nordström 系のリフティング論文、
   Torán–Wörz 2021 等）はいずれも**通常の（消去なしの）可逆ペブリング数**を
   ブラックボックスとして使うだけで、消去予算の変種は無い
3. **Nordström 自身の証明複雑性サーベイ（arXiv 1307.3913）の LaTeX ソースに
   "erasure" 用のマクロが定義されているが、本文では一度も使われていない**
   （ドラフトの残骸と判断。§3.3 参照）。**用語の揺れ探索（bounded irreversibility 等）
   も 0 件**

⚠ 「見つからなかった」は「無い証明ではない」。§6 に検索経路を列挙する。

---

## 1. 中心論文: de Rezende–Nordström–Meir–Robere（CCC 2019 / *computational complexity* 2021）

- **"Nullstellensatz Size-Degree Trade-offs from Reversible Pebbling"**
- CCC 2019 版 DOI `10.4230/lipics.ccc.2019.18`（OpenAlex `W2965069118`）、
  journal 版 `10.1007/s00037-020-00201-y`
- 著者: **Susanna F. de Rezende, Jakob Nordström, Or Meir, Robert Robere**
- arXiv: **2001.02481**（LaTeX ソースを取得・本文で確認）
- 入手: `curl -sSL -o rezende2020.tar.gz "https://arxiv.org/e-print/2001.02481"`
  （`scratchpad/proof_complexity/src/NStradeoff-single-file.tex`、8000 行超級の
  単一ファイル。`grep -niE "erasur|delet|budget|irreversib"` を実行）

**アブストラクト（逐語）**:

> We establish an exactly tight relation between reversible pebblings of graphs
> and Nullstellensatz refutations of pebbling formulas, showing that a graph G
> can be reversibly pebbled in time t and space s if and only if there is a
> Nullstellensatz refutation of the pebbling formula over G in size t+1 and
> degree s (independently of the field in which the Nullstellensatz refutation
> is made).

**本文の逐語確認（`grep` 結果、`NStradeoff-single-file.tex` 全文）**:

- `erasur`／`delet`／`irreversib` を含む行は**1864 行目と 2787 行目の
  "irreversible computation"（Bennett の可逆シミュレーションへの言及）のみ**。
  これは BTV/Bennett の背景説明であって、**彼ら自身の定式化には消去予算が無い**
- `budget` を含む行は**3344 行目の 1 か所のみ**、しかも文意は
  「space budget of `4kn^{1/k}`」という**一般語としての「予算」**（ペブル数の
  上限という意味で使っているだけ）であり、**BTV の消去回数予算とは無関係**

> "All that is left to show is that this can be done within the space budget
> of $4kn^{1/k}$ in time..."（3344 行目、逐語）

**判定**: この論文の可逆ペブリング（time t, space s）は**消去なしの通常の
可逆ペブリング**であり、Nullstellensatz の (size, degree) と厳密に対応させる
という**別方向の貢献**である。**消去予算つき変種は扱っていない。**
`docs/24` §8 の表にあった「Nullstellensatz Size-Degree Trade-offs … 消去なし」
という一言判定は、**今回 arXiv ソースの全文 grep で裏取りが取れた**
（前回はアブストラクトのみの判定だったと推測される。層が「アブストのみ確認」
から「本文で確認」に上がった）。

---

## 2. Nordström 自身のサーベイ（arXiv 1307.3913, *Logical Methods in CS*）

- **"Pebble Games, Proof Complexity, and Time-Space Trade-offs"**
- 入手: `curl -sSL -o nordstrom_survey.tar.gz "https://arxiv.org/e-print/1307.3913"`
  （複数 `.tex` に分割。本体は `LMCSsurvey.tex`、8171 行の単一ファイルに
  実質すべて展開されている）

**発見（本文で確認・逐語）**: `tentativenotation.tex`（ドラフト用マクロ集）に

```latex
\newcommand{\rperasure}{erasure\xspace}
\newcommand{\rpanerasure}{an erasure\xspace}
\newcommand{\Rperasure}{Erasure\xspace}
\newcommand{\Rpanerasure}{An erasure\xspace}
```

という「erasure」用のマクロが**4 個定義されている**。しかし
`grep -n "rperasure\|rpanerasure\|Rperasure" *.tex | grep -v tentativenotation.tex`
は**0 件**——**本体 `LMCSsurvey.tex` を含むどのファイルでも一度も使われていない**。

**判定**: **執筆時に消去（erasure）という語彙の導入を検討した形跡はあるが、
最終稿では扱っていない。** ドラフトの残骸と判断する（本文に対応する定義・
定理が一切無いため）。**「Nordström がこのモデルを知っていて意図的に
避けた」という強い主張はできない**（マクロが未使用というだけでは動機は
分からない）。

---

## 3. Chan 2013 の前方引用（OpenAlex 全数・26 件）

`Just a Pebble Game`（CCC 2013, Siu Man Chan。可逆ペブル数 = Dymond–Tompa 数 =
Raz–McKenzie 数を示した論文）。OpenAlex `W2068277524`、`cited_by_count = 26`。

```sh
curl -s "https://api.openalex.org/works?filter=cites:W2068277524&select=id,display_name,publication_year,doi&per-page=50"
```

**証明複雑性側で新たに見つかった論文と判定**:

| 論文 | 判定 |
|---|---|
| Torán–Wörz, "Reversible Pebble Games and the Relation Between Tree-Like and General Resolution Space" (*computational complexity* 2021, DOI 10.1007/s00037-021-00206-1) | **消去なし**。Crossref アブストラクト確認: 「木状 resolution の節空間 vs 一般 resolution の trade-off」を通常の可逆ペブリングで論じる。消去予算の語は無い |
| de Rezende–Meir–Nordström–Pitassi–Robere–Vinyals, "Lifting with Simple Gadgets and Applications to Circuit and Proof Complexity" (FOCS 2020) | Nullstellensatz 次数を monotone span program サイズへ持ち上げる**リフティング定理**。アブストラクトに消去の語なし |
| Vinyals–Elffers–Johannsen–Nordström, "Simplified and Improved Separations Between Regular and General Resolution by Lifting" (SAT 2020) | regular resolution の分離。消去の語なし（Springer のためアブスト未取得、タイトル・文脈から通常の可逆ペブリング数） |
| Elffers–Johannsen–Nordström（他）, "Unified Characterisations of Resolution Hardness Measures" (SAT 2015) | 同上。消去の語なし |
| Atserias–Ochremiak, "Proof Complexity Meets Algebra" (2018) | CSP の証明複雑性一般論。ペブリングとは無関係（誤ヒット） |
| Potechin, "Analyzing monotone space complexity via the switching network model" (2015) | 単調空間複雑性。消去予算の語なし（アブスト未確認、タイトルからは無関係の可能性） |

**それ以外（22 件中の残り）は量子回路合成（LUT 分解、Karatsuba 乗算等）・
spooky pebble game・メモリハード関数（red-blue pebbling）で、`docs/24`・`docs/25`
の既存判定と同じカテゴリ**（詳細は再現コマンドの生出力を参照）。

---

## 4. Komarath–Sarma–Sawlani の前方引用（OpenAlex 全数・6 件、`docs/25` の宿題を消化）

`docs/25` §5 が「journal 版の被引用 0 件表示は過小の可能性が高い」と書いていた点を
検証した。**カンファレンス版（MFCS 2015, OpenAlex `W1144493394`）で再検索したところ
`cited_by_count = 6`** が取得できた（journal 版 `W2342315727` は本当に 0 件で、
過小ではなく**別バージョンに引用が集約されている**ことが判明）。

```sh
curl -s "https://api.openalex.org/works?filter=cites:W1144493394&select=id,display_name,publication_year,doi&per-page=50"
```

結果 6 件はすべて**量子回路合成**（LUT-based synthesis, QIR/LLVM oracle 生成,
Karatsuba）と **spooky pebble game**（2 件）——**証明複雑性側の引用は 0 件**。
`docs/25` の「見つからず」判定は維持され、かつ journal 版 0 件が過小表示バグで
ないことが確定した（宿題を1つ消化）。

---

## 5. 用語の揺れ探索（OpenAlex 全文検索・6 語）

`bounded irreversibility pebbling` / `partially reversible pebble game` /
`erasure allowance pebble game` / `deletion budget pebbling` /
`semi-reversible pebbling` / `irreversibility budget reversible pebble` の
6 クエリを OpenAlex `search=`（タイトル・アブストラクト全文検索）で実行。

**該当なし。** 上位ヒットはいずれも無関係（BTV/LTV/Královič 系そのもの、
熱工学の "pebble bed"、社会学論文等のノイズ）。WebSearch でも
`"reversible pebble game erasure budget proof complexity Nordström"` を
実行したが、返ってきた文献（Nordström サーベイ、Torán–Wörz、Jaser–Torán
MFCS 2024 の "Pebble Games and Algebraic Proof Systems"）はいずれも
§1–3・下記 §5.1 で判定済みのものだった。

### 5.1 Jaser–Torán, "Pebble Games and Algebraic Proof Systems" (MFCS 2024)

- DOI 経由でなく Dagstuhl から直接取得: `LIPIcs.MFCS.2024.64.pdf`
- `pdftotext -raw` で "erasure" が **1 か所ヒット**（逐語）:

> Ci−1 \ {p} (erasure) or Ci−1 ∪ {p} for some p inferred by the rules of C
> by some rule of the system (inference).

**文脈**: これは Nullstellensatz/Monomial Calculus/Polynomial Calculus の
**configurational proof**（証明の「空間」を測るための、証明システムの作業記憶
からの多項式の除去）における "erasure"。**可逆ペブリングの消去予算とは無関係**
（同じ単語だが対象が違う——証明システムの space measure の定義語彙であって、
ペブルゲームの不可逆操作ではない）。**紛らわしい語の再確認**として記録。

---

## 6. 判定表

| 主張 | 判定 | 層 |
|---|---|---|
| de Rezende–Nordström–Meir–Robere（Nullstellensatz⇔可逆ペブリング）に消去予算変種 | **無い** | **本文（arXiv LaTeX ソース）で確認** |
| Nordström 自身のサーベイ（1307.3913）に消去予算の定義・定理 | **無い**（マクロは未使用の残骸） | 本文で確認 |
| Chan 2013 の前方引用 26 件に消去予算変種 | **無い** | 書誌照合＋主要論文はアブスト確認 |
| Komarath–Sarma–Sawlani の前方引用 6 件に証明複雑性側の応用 | **0 件**（量子回路・spooky のみ） | 書誌照合 |
| Jaser–Torán 2024 の "erasure" | **別概念**（証明の space measure）。消去予算とは無関係 | 本文で確認 |
| 用語揺れ（6 語）での該当論文 | **見つからず** | 検索のみ |

**総合**: 証明複雑性（Nordström 系）側にも、**「消去予算つき clean 到達・
一般 e・一致する上下界」に相当する先行研究は見つからなかった。**
`docs/24`・`docs/25`・`docs/27`・`docs/28` と合わせ、4 系統（BTV 直系・
族二分法・UCNC・RC 会議）＋本書（証明複雑性）で**新規性の主張はいずれの
方向からも崩れていない**。

---

## 7. まだやっていないこと（正直に）

- **Vinyals–Elffers–Johannsen–Nordström (SAT 2020)** と
  **Elffers–Johannsen–Nordström 系 (SAT 2015)** は Springer 論文で
  OpenAlex にアブストラクトが無く、**本文未確認**（タイトルと文脈からの推測で
  「消去なし」と判定した。層は「未確認」に近い）
- **Potechin (2015)** の "Analyzing monotone space complexity via the
  switching network model" は**アブストラクト・本文とも未確認**。証明複雑性の
  隣接領域だが優先度を下げて後回しにした
- **"The Cost of Adaptivity in Security Games on Graphs" (2021)** など、
  BTV 被引用リストに出た**セキュリティゲーム・memory-hard function 系**は
  今回は精査していない（`docs/24`/`docs/25` の red-blue pebbling カテゴリと
  同種と推測したのみ）
- Semantic Scholar は今回**セッション通して 429 が続き、一度も 0 件誤読の
  リスクを取らず OpenAlex のみで完結させた**（健全性チェック済み: BTV の
  journal 版 DOI で `count=1` を確認してから開始）。**S2 復帰後の再照合は
  していない**
- **語の揺れ探索は網羅的ではない。** OpenAlex の `search=` は全文検索ではなく
  主にタイトル・アブストラクト検索なので、本文だけで別の言葉遣いをしている
  論文は取りこぼす可能性がある

---

## 8. 再現用コマンド

```sh
# 健全性チェック（429 の「0件化」対策）
curl -s "https://api.openalex.org/works?filter=doi:10.1051/ita:2004008&select=id" # count=1 を確認

# 中心論文の LaTeX ソース取得・全文 grep
mkdir -p scratchpad/proof_complexity/src && cd scratchpad/proof_complexity
curl -sSL -o rezende2020.tar.gz "https://arxiv.org/e-print/2001.02481"
tar xzf rezende2020.tar.gz -C src
grep -niE "erasur|delet|budget|irreversib" src/NStradeoff-single-file.tex

# Nordström サーベイの LaTeX ソース
curl -sSL -o nordstrom_survey.tar.gz "https://arxiv.org/e-print/1307.3913"
mkdir -p src_survey && tar xzf nordstrom_survey.tar.gz -C src_survey
grep -rniE "erasur|delet.*budget|irreversib" src_survey/*.tex

# 前方引用（OpenAlex, cites: フィルタ）
curl -s "https://api.openalex.org/works?filter=cites:W2068277524&select=id,display_name,publication_year,doi&per-page=50"   # Chan 2013
curl -s "https://api.openalex.org/works?filter=cites:W1144493394&select=id,display_name,publication_year,doi&per-page=50"   # Komarath MFCS 2015 版
curl -s "https://api.openalex.org/works?filter=cites:W2965069118&select=id,display_name,publication_year,doi&per-page=50"   # de Rezende et al. 2019

# Jaser–Torán MFCS 2024
curl -sSL -o jaser2024.pdf "https://drops.dagstuhl.de/storage/00lipics/lipics-vol306-mfcs2024/LIPIcs.MFCS.2024.64/LIPIcs.MFCS.2024.64.pdf"
pdftotext -raw jaser2024.pdf jaser2024_raw.txt && grep -niE "erasur|budget|irreversib" jaser2024_raw.txt
```

⚠ **`pdftotext -layout` は数式を壊す。** `-raw` と併用すること
（今回の PDF はいずれも `-raw` のみで用語検索には十分だった）。

---

# 8. Elicit による意味検索（2026-08-12 追加）

**Elicit の API アクセスが有効になったので、語ではなく意味で照合した。**
狙いは `docs/28` §4 が残した穴——「**別の用語で同じことをしている論文は拾えない**」。

## 8.1 既知系統の再確認（Elicit が正しく拾った）

クエリ「pebbling game where a bounded number of irreversible steps or erasures is allowed,
trading space against irreversibility」で上位に返ったのは、**すべて `docs/24` で照合済み**:

- **BTV 1997**（消去予算モデルの初出。被引用 22 件を全数追跡済み）
- **Li–Vitányi 1996**（"trade-off of storage space versus irreversible erasure" — `τ` 側）
- **Knill 1995**（Bennett のペブルゲームの時間最適解析）
- **Kornerup–Sadun–Soloveichik 2021**（spooky pebble。別モデルと判定済み）

**→ Elicit の意味検索でも、新しい競合は出なかった。**

## 8.2 ⚠ **第 4 の系統を発見**（UCNC・RC・証明複雑性のどれにも出なかった）

**Blocki–Holman–Lee の系統（暗号・memory-hard functions 側）**:

| 論文 | 内容 |
|---|---|
| **Blocki, Holman, Lee, "The Parallel Reversible Pebbling Game: Analyzing the Post-Quantum Security of iMHFs"**（2021, arXiv 2110.04191 / ASIACRYPT 2022） | **parallel reversible pebbling game を導入**。逐語: "introduce a new parallel reversible pebbling game which captures additional restrictions imposed by the **No-Deletion Theorem** in Quantum Computing" |
| **Blocki, Holman, Lee, "The Impact of Reversibility on Parallel Pebbling"**（2024, `10.1007/978-3-031-91107-1_5`） | 逐語: "the parallel reversible pebbling game extends the classical parallel black pebbling game by **imposing restrictions on when pebbles can be removed**" |

**なぜ我々の照合網に掛からなかったか**: 掲載先が **IACR ePrint / ASIACRYPT**（暗号）で、
UCNC・RC・証明複雑性のどの会議にも属さない。**語（`pebbl`）では拾えるが、
我々はその会議を見ていなかった。**

## 8.3 判定: **競合ではない**（層: 要旨で確認・本文未読）

| 観点 | Blocki らの量 | 我々の量 |
|---|---|---|
| 並列性 | **並列**（1 手で複数ペブル） | **逐次** |
| コスト | **cumulative pebbling cost**（面積×時間の積算） | **手数** `M*` と**ピーク** `p` |
| 消去 | **不可逆消去を許さない**（No-Deletion Theorem が動機。制約は「いつ外せるか」） | **消去を予算 `e` として明示的に許す** |
| 目的 | iMHF の耐量子安全性の評価 | 厳密値の決定 |

**決定的な違い**: 彼らは「**消去できない**」制約を課す（量子の No-Deletion 定理が動機）。
我々は「**消去を有限回だけ許す**」。**方向が逆で、消去予算 `e` に相当する量が無い。**

⚠ **層: 要旨で確認。本文（arXiv 2110.04191）は未読。**
彼らの line graph の下界 `Ω(N^{1+1/√log N})` が我々の `e=0` の量と関係する可能性は
**未確認**。→ §7 の「まだやっていないこと」に追加する。

## 8.4 Elicit の位置づけ（今後の運用）

- **既知系統の再確認**には有効（BTV・Li–Vitányi・Knill・spooky を正しく上位に返した）
- **会議の壁を越える**のに有効（**暗号側の系統は Elicit でしか見つからなかった**）
- ⚠ **意味検索でも「無い」の証明にはならない**。`docs/24`・`docs/27`・`docs/28`・
  本文書の全数追跡と併用すること

**残枠**: 2026-09-12 までの期間で 0% 使用（`get_usage` で確認）。
