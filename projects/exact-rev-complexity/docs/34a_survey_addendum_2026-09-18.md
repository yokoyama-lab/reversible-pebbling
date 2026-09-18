# 34_survey §4 の残り 2 項目を埋める調査 — Semantic Scholar 鍵つき再調査と被引用の全数追跡

取得日: **2026-09-18**（13:04–13:25 UTC ＝ 22:04–22:25 JST）。対象文書:
`exact-rev-complexity/docs/34_survey_parallel_pebbling_novelty.md`（読むだけ。リポジトリと台帳は未編集）。
生データ: 作業時のスクラッチ（25MB・リポジトリには入れていない。再取得は下のスクリプトで可能）。スクリプト: `scripts/survey34/s2.py`（API）・`sieve.py`（統合とふるい）。
S2 の鍵は環境変数から読むだけで、値はどのファイルにも書いていない（`grep -rlF` で 0 件を確認）。

## 0. 結論を先に

1. **新顔が 1 本あり、R-Q2-01 の「問いの形」に先例があった。**
   Kahanamoku-Meyer, Ragavan, Van Kirk, *Parallel Spooky Pebbling Makes Regev Factoring More Practical*,
   EUROCRYPT 2026（LNCS, pp. 402–430, DOI 10.1007/978-3-032-25291-3_14, arXiv:2510.08432。v1 2025-10-09・v2 2026-07-03）。
   §2.4・Fig. 2 左が「**鎖で最適深さ 2ℓ を達成できる最小ペブル数 s** を ℓ の関数として A\* 探索で厳密に求めた図」で、
   これは $n^*(p)$ の逆関数に当たる量である。**ただし模型が違う**（並列 **spooky**＝測定つき・ゴーストあり。空間の数え方も違う）。
   純可逆の並列模型（BHL Def. 1）での値 $7, 11, 17, 25, \dots$ は同論文にも公開コード v0.1 にも**無い**。
   → **34_survey §5 の「問い自体は依然として見当たらない」は、このままでは書けない。**「問いの形には先例があり、純可逆模型での値が新しい」へ直す。
2. **R-Q2-03（窓・余裕ゼロ・最早配置）と同方向の記述が、同じ論文に鎖・非形式で 2 か所ある**（Remark 2.7 と付録 B）。
   一般 DAG・全頂点・両端で必ず存在・Lean、という我々の形は見当たらない。Královič Lemma 3.2 と並べて言及が要る。
3. **R-Q2-02 は方針どおり**（同論文 Remark 2.7 が鎖の下界 $2\ell$ を “straightforward” の 3 行で済ませている。新規性を主張しない方針を補強）。
4. **34_survey の「全数」は全数ではなかった。** §11 の「Královič の前方引用 16 件」は OpenAlex の **MFCS 2001 会議版レコード**の件数で、
   RAIRO 2004 版は別レコード（9 件）。S2 は 28 件、和集合は 32 レコード（著作単位で 27）。§3 の「BHL 続編 被引用 0 件・打ち止め」も S2 では 1 件（上の新顔そのもの）。
5. それ以外に R-Q2-01/03 の問いに触れる文献は**見つからなかった**（範囲: §2 の表。引用元 610 レコードを固定 10 語でふるい、要旨なし 205 件は題名を全件目視、16 本は全文で語を計数）。

---

## 1. 検索式・件数・取得日時

すべて 2026-09-18 取得。S2 は `x-api-key` つき、1.2 秒間隔、429 は 2 秒〜の待ちを挟んで再試行（最大 8 回。全リクエスト成功）。

### 1.1 Semantic Scholar `/paper/search/bulk`（ブール式・全件取得）

| ID | 検索式 | total | 取得 | うち「可逆/量子 ∧ pebbl」（ノイズ除去後） | 核文献 / 被引用集合に既出 / 新顔 |
|---|---|---:|---:|---:|---|
| B1 | `reversible + (pebble \| pebbling \| pebbles \| pebblings)` | 62 | 62 | 33 | 8 / 18 / 7（**新顔 7 は全て無関係**: 確率論の教科書、蓄熱材、木変換器、*Reversible Pebble Transducers*（オートマトン）等） |
| B2 | `parallel + (pebbling \| pebblings)` | 877 | 877 | 8 | 2 / 4 / 2（新顔: 文学論 1、Beame–Kornerup *Cumulative Memory Lower Bounds…* 1。後者は計算モデル一般の累積メモリ下界で鎖の厳密値は無い・要旨のみ） |
| B3 | `spooky + (pebble \| pebbling)` | 4 | 4 | 4 | 0 / 4 / 0 |
| B4 | `Bennett + (pebble \| pebbling)` | 22 | 22 | — | 新顔に関連なし（*Pebble-Depth* arXiv:2009.12225 は論理深さの話） |
| B5 | `uncomputation + (depth \| parallel \| schedule \| scheduling)` | 22 | 22 | — | ペブリングで時間最適を問うものなし（題名・要旨で確認） |
| B6 | `(pebble \| pebbling) + ("time-optimal" \| "time optimal" \| "minimum time" \| "minimal time" \| makespan \| "optimal depth" \| "minimum depth")` | 19 | 19 | — | 可逆ペブリングの該当なし（マルチロボット経路計画の pebble motion 等） |

B2 の 877 件の大半は graph pebbling（組合せ論の別概念）と MHF の並列黒ペブリング。「可逆/量子」を含むのは 8 件だけだった。

### 1.2 Semantic Scholar `/paper/search`（関連度順・上位 100 件まで）

| ID | 検索語 | total | 取得 |
|---|---|---:|---:|
| R1 | parallel reversible pebbling | 10023 | 100 |
| R2 | reversible pebbling parallel | 10023 | 100 |
| R3 | reversible pebble game time-space tradeoff | 264 | 100 |
| R4 | reversible pebbling time optimal chain | 264 | 100 |
| R5 | reversible pebble game line graph depth | 74 | 74 |
| R6 | Bennett pebble game parallel moves | 10 | 10 |
| R7 | reversible pebbling SAT solver | 48 | 48 |
| R8 | reversible pebbling minimum time number of pebbles | 61 | 61 |
| R9 | parallel pebbling depth optimal space | 344 | 100 |
| R10 | uncomputation scheduling qubits depth tradeoff pebbling | 4 | 4 |

B1–B6 と R1–R10 の和集合は 1445 件。うち「小集合（B1, B3–B6）の全件」＋「可逆 ∧ pebbl を含むもの」112 件を被引用集合・既知文献と突き合わせ、
どちらにも無い 76 件の題名を全件目視した。**実質的な新顔は 0 件**（＝可逆ペブリングを扱うものは、被引用追跡で既に全部拾えていた）。

### 1.3 OpenAlex `title_and_abstract.search`（独立の検算）

| ID | 検索式 | total | 題名ノイズ除去後 | 被引用集合にも核にも無いもの |
|---|---|---:|---:|---|
| O1 | `reversible AND (pebble OR pebbling OR pebbles)` | 88 | 52 | 21（版違いの題名ゆれ 4、無関係 12、査読なしの Zenodo/Research Square 4、de Rezende の KTH 学位論文 1） |
| O2 | `spooky AND (pebble OR pebbling)` | 7 | 3 | 0 |
| O3 | `parallel AND pebbling AND (reversible OR quantum)` | 16 | 13 | 5（Karatsuba の題名ゆれ 1、EU 報告書 1、Beame–Kornerup の 3 版） |

### 1.4 できなかったこと

* **DBLP API**: `dblp.org`・`dblp.uni-trier.de`・`dblp.dagstuhl.de` の 3 ホストとも bot 判定の HTML を返し取得不可。
  34_survey が「次の手」に挙げていた会議単位の目視は**未実施**。S2 は DBLP を索引に含む（`externalIds.DBLP`）ので B1 が部分的な代替になっている。

---

## 2. 被引用の全数

### 2.1 文献ごとの件数（S2 / OpenAlex）と食い違い

「S2」は `/paper/{id}/citations` をページングで全件取得した数（全文献で `citationCount` と一致）。
「OA」は OpenAlex のレコードごとの `cites:` 全件取得数。「統合」は DOI → 正規化題名で突き合わせた和集合のレコード数。

| 核文献 | S2 paperId（先頭 8 桁） | S2 | OpenAlex（レコード別） | OA 和 | 両方 | S2 のみ | OA のみ | 統合 | 要旨あり | 題名のみ |
|---|---|---:|---|---:|---:|---:|---:|---:|---:|---:|
| **Královič 2004** | `dc57a49e` | **28** | W1892407853（MFCS 2001 会議版）**16** ＋ W1976150152（RAIRO 2004）**9** | 24 | 20 | 8 | 4 | **32** | 22 | 10 |
| **Meuli+ 2019** | `dc9e5c17` | **46** | W2926868949 **2** | 2 | 2 | 44 | 0 | **46** | 43 | 3 |
| BHL 2022 | `d873bdee` | 3 | W4312698707 5 ＋ W4286907950（arXiv）0 | 5 | 2 | 1 | 3 | 6 | 4 | 2 |
| BHL 2025（続編） | `99629830` | **1** | W4409846353 **0** | 0 | 0 | 1 | 0 | 1 | 1 | 0 |
| Komarath+ 2016 | `5dae4b0a` | 9 | W2342315727 **0** | 0 | 0 | 9 | 0 | 9 | 7 | 2 |
| Knill 1995 | `1a8120d3` | 25 | W1525622236 9 | 9 | 8 | 17 | 0 | 25 | 17 | 8 |
| Levine–Sherman 1990 | `3c89dd19` | 84 | W2022763264 71 | 71 | 57 | 27 | 5 | 89 | 63 | 26 |
| Chan 2013 | `ac5bf4ba` | 33 | W2068277524 25 ＋ W2399930771（ECCC）4 | 28 | 23 | 10 | 4 | 37 | 23 | 14 |
| Bhattacharjee+ 2019 | `3ea0218d` | 10 | W2962612432 13 | 13 | 8 | 2 | 4 | 14 | 11 | 3 |
| Bennett 1989 | `500470be` | 442 | W2061073612 413 | 413 | 299 | 143 | 77 | 519 | 350 | 169 |
| （追加）Parent–Roetteler–Svore 2015 | `a149bbf2` | 37 | 未取得 | — | — | — | — | 37 | 30 | 7 |
| （追加）Li–Vitányi 1996 | `395f3659` | 37 | 未取得 | — | — | — | — | 37 | 13 | 24 |
| **全体（重複除去）** | | | | | | | | **610** | 405 | **205** |

追加 2 本は S2 の題名検索で核文献と並んで出た隣接核（REVS コンパイラ／可逆シミュレーションの古典）。調べる範囲を広げる方向の追加なので入れた。
「OA 和」と「両方＋OA のみ」が合わない行（Bennett・Levine–Sherman・Chan・Knill・Bhattacharjee）は、OpenAlex 内の版違いが統合で同じ行に畳まれたため。

**食い違いの原因（実測で確認できたもの）**

1. **OpenAlex は版ごとにレコードを分け、被引用も分かれる。** Královič は会議版 16＋雑誌版 9（重複 1）＝ 24。
   **34_survey §11 の「16 件を全数見て」は会議版レコードだけを見ていた。** 見えていなかった 16 レコードには
   de Rezende+ 2019、Torán–Wörz 2021、Chan–Lauria–Nordström–Vinyals 2015、Kamath+ 2021（ePrint 版）、Glück–Yokoyama 2022 などが入る（下の §2.3）。
2. **OpenAlex は参照リスト未取り込みの論文が多い。** Meuli+ 2019 は 2 対 46。新顔の KRV 2025 は OpenAlex に収録済み（W4416385180）だが
   `referenced_works_count = 0` なので BHL の被引用に現れない。**8 月の OpenAlex による「BHL 系列の全数確認」がこれを落とした原因はこれ。**
3. **S2 は版を併合する。** Královič の S2 レコードは year=2001・venue=RAIRO・DOI=10.1051/ita:2004008 と、会議版の年と雑誌版の書誌が混ざっている
   （書誌として使うときは要注意。正しくは RAIRO-ITA 38(2), 2004）。
4. **S2 には断片・重複が混じる。** 例: 同じ ETH 学位論文が 2 レコード、`1 Adaptive Secret Sharing for Monotone Circuits`（PDF の断片）。
   Královič の 32 レコードは版違い 5 組を含み、著作単位では 27。
5. Komarath+ 2016 は 34_survey §12 に「前方引用（9 件）」とあるが、現在の OpenAlex は 0 件と返す。S2 は 9 件（§2.4）。

### 2.2 ふるい

**語は結果を見る前に固定した**（`sieve.py` の `TERMS`）。指定の 10 語を大文字小文字無視の部分一致で、題名＋要旨に当てる。

`parallel`, `depth`, `makespan`, `simultaneous`, `window`, `earliest`, `slack`, `schedule`, `time-optimal`, `minimum time`

結果を見る前に加えた変更は 3 つ（理由つき）:

* `schedule` は語幹 `schedul` で当てる（scheduling は `schedule` の部分文字列にならないため）。`time-optimal` は `time optimal` も拾う。
* `minimum time` に `minimal time` を加える（Královič 自身の言い回しが “minimal time” で、当人の流儀を落とすため）。
* 第 2 のふるい `pebbl` を併用する（概念語が要旨に出ない論文を落とさないため。ペブリングを主題にする引用元は少なく全件目視できる）。

| 集合 | 統合 | 10 語のどれかにヒット | `pebbl` にヒット | どちらか | 両方 | 目視 |
|---|---:|---:|---:|---:|---:|---|
| **Královič 2004** | 32 | 13 | 12 | 19 | 6 | **32 件全件**（題名と書誌）。うち 19 件は要旨を通読 |
| **Meuli+ 2019** | 46 | 19 | 8 | 22 | 5 | **46 件全件**。うち 22 件は要旨を通読 |
| BHL 2022 / BHL 2025 | 6 / 1 | 3 / 1 | 5 / 1 | 5 / 1 | 3 / 1 | 全件 |
| Komarath+ 2016 | 9 | 3 | 5 | 6 | 2 | 全件 |
| Knill 1995 | 25 | 7 | 6 | 11 | 2 | 全件（題名）。ヒット 11 件は要旨 |
| Chan 2013 | 37 | 15 | 18 | 24 | 9 | ヒット 24 件の要旨 |
| Bhattacharjee+ 2019 | 14 | 4 | 3 | 5 | 2 | ヒット 5 件の要旨 |
| Levine–Sherman 1990 | 89 | 11 | 12 | 20 | 3 | ヒット 20 件 |
| Bennett 1989 | 519 | 76 | 44 | 101 | 19 | ヒット 101 件（語の前後 90 字の文脈。必要なものは要旨全文） |
| Parent+ 2015 / Li–Vitányi 1996 | 37 / 37 | 6 / 3 | 2 / 6 | 7 / 8 | 1 / 1 | ヒット分 |
| **全体（重複除去 610）** | 610 | **92** | 47 | **118** | **21** | **118 件を目視**（小集合に属する 61 件は要旨を通読、大集合のみの 57 件は語の文脈）。**要旨なし 205 件は題名を全件目視** |

語ごとのヒット数（610 件中）: parallel 37・depth 49・simultaneous 9・schedule 8・window 5・earliest 2・time-optimal 1・minimum time 1・**makespan 0・slack 0**。

* `time-optimal` の 1 件は Knill 1995 自身（“a recursion for the time optimal solution of the pebble game given a space bound”＝**空間を固定して時間を問う**側。既知）。
* `earliest` の 2 件と `window` の 5 件は無関係（パイプラインの最初の故障段、windowed arithmetic、化学の総説など）。
* `depth` の 49 件は回路深さ・T-depth・単調回路の深さ下界が大半。ペブリングの時間としての depth は BHL 2 本と KRV 2025 だけ。

**弱点**: 610 件中 205 件は S2・OpenAlex のどちらからも要旨が取れず、ふるいは題名にしか効いていない（題名は全件目視した）。
統合スクリプトは題名が空のレコードを誤って同一視しうる（該当は Bennett 集合で最大 1 件）。

### 2.3 Královič 2004 の被引用 32 レコード — 34_survey が見ていなかった 16 レコード

OpenAlex 会議版レコード（34_survey が見た 16 件）に**無い**もの。いずれも R-Q2-01/03 の問いには触れない（判定材料つき）。

| 年 | 題 | 判定材料 |
|---|---|---|
| 2012 / 2014 | Chan–Potechin, *Tight bounds for monotone switching networks via Fourier analysis*（STOC／ToC） | 要旨: スイッチングネットワークの大きさ。ペブリングの時間は扱わない |
| 2013 | Chan, *Pebble Games and Complexity*（学位論文） | 要旨: ペブル**数**の等価性と回路深さ。34_survey §12 の Chan 2013 と同じ側 |
| 2015 | Chan–Lauria–Nordström–Vinyals, *Hardness of Approximation in PSPACE…*（FOCS） | 要旨: 可逆ペブル数の PSPACE 完全性と近似困難性。**空間のみ** |
| 2017 | Jafargholi+, *Adaptive Secret Sharing for Monotone Circuits*（断片）／ 2021 Kamath+ *On the Cost of Adaptivity in Graph-Based Games*（ePrint 版） | 要旨なし・題名のみ。適応的安全性の証明に逐次の可逆ペブリングを使う系列 |
| 2017 | Soeken+, *Logic Synthesis for Quantum Computing* | 要旨: 階層的可逆論理合成。ペブリングの語なし |
| 2017 | Vinyals, *Space in Proof Complexity*（学位論文） | 要旨なし・題名のみ |
| 2019 | **de Rezende–Meir–Nordström–Robere, *Nullstellensatz Size-Degree Trade-offs from Reversible Pebbling*** | **全文**: parallel 3（多重辺 1・文献題 2）・depth 12（Prop. 4.6「入次数 ℓ・深さ d の DAG は $d\ell+1$ 個で可逆ペブリングできる」＝**空間**の上界）。逐次の時間–空間トレードオフ。並列手も時間最適点も無い |
| 2021 | Blocki–Lee, *Parallel Quantum Pebbling…*（BHL 2022 の旧題） | BHL 2022 と同一著作 |
| 2021 | Larasati+, *Quantum Circuit Design of Toom 3-Way Multiplication* | 要旨: 乗算器。応用側 |
| 2021 | **Torán–Wörz, *Reversible Pebble Games and the Relation Between Tree-Like and General Resolution Space*** | **全文（STACS 2020 版）**: parallel 1（文献題）・depth 3・simultaneous 3（節空間の定義）。木状導出の節空間 ≤ space·log time。**空間側** |
| 2022 | Glück–Yokoyama, *Reversible computing from a programming language perspective* | 総説 |
| 2026 | Yokoyama, *The Exact Growth Rate of Space-Optimal Reversible Pebbling on Chains*（arXiv:2609.15062） | 自著。**空間最適側**（反対の隅） |
| 2026 | Wardhani–Putranto, *Toward Optimal Quantum Multipliers…* | 要旨: Toom–Cook 乗算器。応用側 |

OpenAlex にだけあって S2 に無いもの 4 件: Bahi, Eisenbeis, *Spatial complexity of reversibly computable DAG*（CASES 2009, pp. 47–56, DOI 10.1145/1629395.1629404。Crossref で確認。
要旨: 可逆 DAG の**レジスタ数**の下界とヒューリスティック。時間は扱わない）、ToC 2014（上記）、量子乗算器 2 件（2024）。

### 2.4 その他、34_survey で「未」だったもの

* **Komarath+ 2016 の前方引用**（§12 に「9 件」）: S2 で 9 件を全件確認。*The Compilation of Reversible Circuits and a New Optimization Game*（2016・要旨なし）、
  Parent–Roetteler–Mosca 2017、de Rezende+ 2019、Meuli+ 2019、Ding–Chong 2020（書籍）、SQUARE 2020、*Preliminary Seminar Program*（2021・断片）、
  Lancellotti+ 2024、Zhang–Li–Ying 2025。**木の時間最適側を問うものは無い**（ヒットは parallel 2 件・depth 2 件で、いずれも回路の並列度・T-depth）。
* **Královič の量子回路合成系の引用元**（§12 に「未読」）: LUT-Based HRS 2019、Soeken–Roetteler 2020、Toom 系 4 件は要旨で確認。ペブリングは道具として引くだけで、問いは現れない。
* **spooky 系の前方引用**（KRV 2025 を見つけた後に追加）: KRV 2025 の被引用 1 件（*Space-Optimized and Experimental Implementations of Regev's…*, arXiv:2511.18198。要旨に pebbl なし）、
  KSS の 9 件、Quist–Laarman 2024 の 3 件。並列可逆ペブリングの追加はなし。

---

## 3. 新顔の近接文献

「新顔」＝ 34_survey に名前が出てこない文献。全文は arXiv（既定＝最新版）／ePrint／LIPIcs の PDF を `pdftotext -layout` にかけ、固定語を数えた
（`survey34_raw/fulltext/`・`fulltext_term_counts.json`）。
書誌は S2 の返り値に加え、DOI のあるものは Crossref で著者・掲載誌・年を確認した（`survey34_raw/crossref_checks.json`。
Parent–Roetteler–Mosca の LIPIcs DOI だけは Crossref に無く（DataCite 登録）、S2 の返り値のみ）。
Jaser–Torán の LMCS 版の題は Crossref では *Pebble Games and Algebraic Proof Systems*（arXiv 版の “Meet Again” が落ちている）。

| 書誌（API で確認） | 範囲 | 語の出現（全文） | 何をしているか | R-Q2-01/03 との差分 |
|---|---|---|---|---|
| ⭐ **Kahanamoku-Meyer, Ragavan, Van Kirk**, *Parallel Spooky Pebbling Makes Regev Factoring More Practical*, **EUROCRYPT 2026**, LNCS pp. 402–430, DOI 10.1007/978-3-032-25291-3_14, arXiv:2510.08432（Crossref と arXiv API で確認） | **全文**（v2。§1・§2.1–2.4・付録 B を通読） | parallel 110・depth 122・window 18（全て windowed arithmetic）・simultaneous 3・pebbl 390・makespan/earliest/slack/schedule/time-optimal/minimum time 0 | 並列 **spooky** ペブリングを定義。鎖で深さ $2\ell$（最適）を $\le 2.47\log\ell$ 個で達成（Thm 2.12）。**§2.4・Fig. 2 左: 最適深さ $2\ell$ を達成できる最小ペブル数を A\* で厳密に求め、$\ell \lesssim 100$ まで図示。** 同右: $s = 4..11$ を固定したときの最小深さ | **下の §3.1** |
| Kornerup, Sadun, Soloveichik, *Tight Bounds on the Spooky Pebble Game*, Quantum 2025, arXiv:2110.08973（34_survey §3 に題名だけ既出） | 全文 | time-optimal **5**・parallel 4（BHL の紹介と文献題）・depth 52 | **逐次** spooky。ペブル数を固定した時間の漸近的にタイトな上下界。Def. 4.4 “sweep-first”: 時間最適戦略を「$v_n$ に置くのは 1 回、それまで各 $v_i$ に高々 1 回」の正規形に直せる | 「時間最適なら構造が固まる」型の補題だが、**空間固定・逐次**（Královič Lemma 3.2 と同じ隅）。R-Q2-03 の差分表に 1 行足す価値あり |
| Quist, Laarman, *Trade-offs between classical and quantum space using spooky pebbling*, LMCS 21(4:29) 2025, arXiv:2401.10579 | 全文 | parallel **11**・depth 2・pebbl 561 | spooky ペブリングの SAT/BMC 符号化。「**the above encoding implements parallel pebbling semantics** so multiple pebbles and ghosts can be added or removed at the same timestep」。並列意味論は BMC の展開数を減らす**ソルバ上の工夫**で、解は逐次化して報告 | **§1（符号化は既発表）に足すべき 2 本目の先例**。並列時間を目的にはしていない。厳密値の表なし |
| de Rezende, Meir, Nordström, Robere, *Nullstellensatz Size-Degree Trade-offs from Reversible Pebbling*, Comput. Complexity 30(1), 2021, DOI 10.1007/s00037-020-00201-y, arXiv:2001.02481 | 全文 | parallel 3・depth 12・simultaneous 11（「同時に小さい次数と大きさ」） | 可逆ペブリングの（時間, 空間）＝ NS 反駁の（大きさ−1, 次数）の**厳密な対応**。逐次のトレードオフ | 逐次。時間最適点の空間は問わない。「時間–空間の対を厳密に扱う」系列として関連研究に入れる候補 |
| Torán, Wörz, *Reversible Pebble Games and the Relation Between Tree-Like and General Resolution Space*, STACS 2020 / Comput. Complexity 30(1), 2021, DOI 10.1007/s00037-021-00206-1 | 全文（STACS 版） | parallel 1・depth 3 | 可逆ペブリングと木状導出の節空間 | 空間側。問いは現れない |
| Jaser, Torán, *Pebble Games and Algebraic Proof Systems Meet Again*, LMCS 22(2:12) 2026, arXiv:2506.21149 | 全文 | parallel 3（「対応関係」の意味）・simultaneous 12 | 黒ペブリング ↔ Monomial Calculus の対応 | 無関係 |
| Parent, Roetteler, Mosca, *Improved reversible and quantum circuits for Karatsuba-based integer multiplication*, TQC 2017, arXiv:1706.03419 | 全文 | parallel 6・depth 21・pebbl 51 | 完全三分木のペブルゲームで Karatsuba の空間を $O(n^{1.427})$ に。「parallel」は再帰呼び出しの並べ方 | 木の上の空間–演算数。時間最適点の厳密値は無い |
| Zhang, Li, Ying, *A Divide-And-Conquer Pebbling Strategy for Oracle Synthesis…*, IEEE TCAD 44(12), 2025, pp. 4601–4614, DOI 10.1109/TCAD.2025.3570608 | **要旨のみ** | 10 語 0・pebbl あり | 分割統治のヒューリスティック。qubit 90% 減・演算 3–4 倍 | 応用側（Meuli+ と同じ位置） |
| Lancellotti+, *Optimizing Quantum Circuit Synthesis with Dominator Analysis*, ICCD 2024 | **要旨のみ** | depth 1（T-depth） | 支配関係でペブリングを改善 | 応用側 |
| Li+, *From Leaves to Clusters: Depth-Efficient SAT-Oracle Synthesis…*, arXiv:2607.11401（2026） | 全文 | parallel 50・depth 119・schedule 25・pebbl 3（文献題のみ） | ancilla 予算下で節レベルの並列度を上げて**回路深さ**を削る。グループ化問題の NP 完全性 | ペブルゲームではない。「予算つきで深さを問う」点だけ隣接 |
| Li+, *Modeling and Resource Optimization for Quantum Oracles*, arXiv:2605.21380（2026） | 全文 | depth 88・slack 1（「予算に余裕なし」）・pebbl 12 | 複数関数の合成層の木構成を最適化 | 無関係 |
| Fisher, Bobda, *Earliest Failure Localization in Pipelines Via Quantum Search*, IEEE DCAS 2026 | **要旨のみ** | earliest 3・schedule 2 | 「earliest」は最初に違反する段。ancilla 予算つきの compute/uncompute 順序を再計算コストで最適化 | 逐次のコスト。深さ・窓は無い |
| SQUARE（ISCA 2020, arXiv:2004.08539）／ Reqomp（Quantum 2024, arXiv:2212.10395）／ IPDR（arXiv:2308.12162） | 全文 | earliest 各 1（ゲートを置く最早時刻／最初の頂点）。IPDR は pebbl 68・parallel 9（並列プログラムの検証） | ヒューリスティックな ancilla 再利用／時間無制約での最小ペブル数を PDR で | 問いは現れない |
| Banegas, Bernstein, *Low-Communication Parallel Quantum Multi-Target Preimage Search*, SAC 2017（LNCS, pp. 325–335）, ePrint 2017/789 | 全文 | parallel 52・pebbl **1**（Knill の文献題） | 量子プロセッサの並列化。ペブリングは扱わない | 無関係 |
| BHL 2025（ePrint 2024/334。34_survey で既読） | 全文（再計数） | parallel 80・depth 121・pebbl 708 | **Thm 1（逐語確認）**: $\Pi_{cc}^{\leftrightarrow,\parallel}(L_N) = \Omega\!\big(N^{1+\frac{\sqrt2-o(1)}{\sqrt{\log N}}}\big)$ | 下の §3.2。34_survey は「漸近のみ」で片付けているが、**$n^*(p)$ の漸近上界を含意する** |

### 3.1 ⭐ KRV 2025 と R-Q2-01/03 の差分（投稿時に必ず書く）

**模型（Def. 2.1–2.3, 2.8。逐語）**

> the state of the game will be a vector state ∈ {pebble, ghost, empty}$^{\ell+1}$ … (The first entry of the state is a dummy variable which will always be pebble.)
> … the target end state will be (pebble, empty, …, empty).

> In the first phase of a parallel pebbling game, we can make an arbitrary number of parallel calls to Pebble, Unpebble, provided that their active sets are pairwise disjoint.
> In the second phase, we can make an arbitrary number of parallel calls to Ghost.

> we define the space usage $s_t$ of time step $t$ as the number of indices $i \in [1, \ell]$ such that at least one of state$[t-1]_i$, state$[t]_i$ is pebble.

**R-Q2-02 に当たる 1 行（Remark 2.7。逐語）**

> It is straightforward to see that a parallel pebbling game of length $\ell$ must necessarily have depth $\ge 2\ell$. This is because the position of the rightmost
> pebble/ghost changes by at most ±1 in each time step.

**R-Q2-01 と同じ形の問い（§2.4 と Fig. 2 の説明。逐語）**

> One may desire to hold the number of pebbles $s$ constant, and find the optimal-depth solution under that constraint (which may be greater than $2\ell$)

> In the left figure, we plot the minimum number of pebbles $s$ with which it is possible to achieve the absolute optimal depth $2\ell$ … In the right figure, we plot
> the depth as a function of $\ell$, for different constant values of the number of pebbles $s$.

**R-Q2-03 と同方向の記述（付録 B。逐語）**

> as we discuss in Section 2, an optimal pebbling provably always begins with an initial “blast” phase where we pebble directly across to position $\ell$

本文にこれを述べた補題は無い（番号つきの言明を全数見た: Def. 2.1–2.4, 2.8, 2.13, 2.17、Rem. 2.5–2.7、Thm 2.9, 2.10, 2.12、Cor. 2.11、Prop. 2.14、Lem. 2.15–2.19）。根拠は Remark 2.7 の 3 行だけ。

| | KRV 2025 | 我々（R-Q2-01 / R-Q2-03） |
|---|---|---|
| 模型 | 並列 **spooky**（Ghost 手あり。ゴーストは後で置き直して消す） | 並列**純可逆**（BHL 2022 Def. 1） |
| 終状態 | 全部空（計算して全部戻す）→ 最適深さ $2\ell$ | sink に 1 個 → $T = 2n-1$ |
| 空間の数え方 | **遷移の前後どちらかでペブルがある位置の数**の最大（Def. 2.8） | 各時刻のペブル数の最大 |
| 問い | 鎖で最適深さを達成できる最小 $s$（$\ell$ の関数）／ $s$ 固定での最小深さ | 鎖で $T=2n-1$ を保てる最大 $n$（$p$ の関数）＝**逆関数の形で同じ問い** |
| 答え | $s = \Theta(\log\ell)$（上界 $\lceil 2.47\log\ell - 2.77\rceil$・下界は KSS Thm 4.13 から Cor. 2.11）。具体値は**図のみ**（数表なし） | $7, 11, 17, 25, 35, 47, 62, 81, 104$（閉じた式なし） |
| 手段 | A\* 探索（Julia。Zenodo 10.5281/zenodo.17298960）。**公開コード v0.1 に Ghost を禁じるオプションは無い**（README と `find_pebblings.jl` の引数を確認: `-l`, `-s`, `--touch-and-go`, `--save-dir`） | SAT ＋ UNSAT 証明 |
| 構造の主張 | 鎖のみ。右端の位置が毎手 ±1 しか動かない、という 3 行の議論。最適なら最初の $\ell$ 手は一直線、は付録で “provably” と言うだけ | 任意の DAG・**全頂点**を窓 $[j+1,\,T-j-1]$ に閉じ込め**両端で必ず存在**。Lean 4 |
| 対象 | 鎖のみ（Regev の因数分解の冪乗算） | 鎖・ピラミッド・完全二分木・層状 |

**判断**: 値と定理は重ならない。**重なるのは問いの立て方**で、「同じ問いを並列模型で問うと…」という 34_survey 結論 2 の売り方は、
「spooky では $\Theta(\log\ell)$ 個で足りる（KRV 2025）。純可逆ではそうならず、厳密値は $7, 11, 17, \dots$」という**三者比較**（逐次 $p$ ／ 並列純可逆 ／ 並列 spooky）に
組み替えたほうが強く、かつ正直。**言及なしに出してはならない**（EUROCRYPT 2026 なので査読者が知っている可能性が高い）。

### 3.2 BHL 2025 Thm 1 が $n^*(p)$ に含意すること（⚠ 紙の導出・未検算）

時間 $T = 2n-1$・ピーク $p$ のペブリングの累積コストは高々 $p(2n-1)$。Thm 1 から
$p(2n-1) \ge c\,n\,2^{(\sqrt2-o(1))\sqrt{\log n}}$、よって $p = \Omega\big(2^{(\sqrt2-o(1))\sqrt{\log n}}\big)$、すなわち

$$ \log_2 n^*(p) \;\le\; \big(\tfrac12 + o(1)\big)\log_2^2 p \qquad\text{（準多項式の上界）} $$

* **層**: 私の紙の導出で、機械検証も独立の検算もしていない。BHL の模型が我々のもの（34_survey §10 で一致を確認した Def. 1）と同じであることが前提。
* 実測との突き合わせ: $p = 12$ で $2^{\log_2^2 12 / 2} \approx 86$ に対し実測 $n^*(12) = 104$。$o(1)$ と定数を無視した値なので桁が合う程度の意味しかない。
* **意味**: $n^*(p)$ の**厳密値**は新しいが、「$n^*(p)$ は多項式より速く指数より遅い」という漸近の枠は BHL 2025 から従う。
  KRV 2025 の Table 1 も同じ対比（並列のみ $O(4^{\sqrt{\log\ell}})$ 個 対 並列＋spooky $\approx 2.47\log\ell$ 個）を載せている。
  ただし BHL 2022 Lemma 8 の上界は深さ $O(\ell)$ であって**ちょうど** $2\ell-1$ ではないので、$n^*(p)$ の下界は BHL からは出ない。

---

## 4. 34_survey §4 の差し替え文案

既存の書き方（打ち消し線 → 結果）に合わせた。§4 の最後の 2 項目をこれで置き換える。

```markdown
* ~~OpenAlex の全文検索は自然文クエリに弱く、「窓」「最早配置」のような概念での
  網羅的探索は**できていない**。DBLP の会議単位の目視か、Královič/Meuli の被引用の
  全数追跡が要る~~ → **2026-09-18 に被引用の全数追跡を実施**（§13）。
  Královič 2004 は S2 28 件・OpenAlex 24 件（会議版レコード 16 ＋ 雑誌版レコード 9）・和集合 32 レコード、
  Meuli+ 2019 は S2 46 件・OpenAlex 2 件。核文献 12 本の引用元 610 レコードを、先に固定した 10 語
  （parallel, depth, makespan, simultaneous, window, earliest, slack, schedule, time-optimal, minimum time）で
  ふるい（ヒット 92 件。`pebbl` との和で 118 件を目視、要旨なし 205 件は題名を全件目視）、16 本は全文で語を計数した。
  **結果: 新顔 1 本**（Kahanamoku-Meyer–Ragavan–Van Kirk, EUROCRYPT 2026 ＝ 並列 *spooky* ペブリング。
  鎖で最適深さ $2\ell$ を達成できる最小ペブル数を A\* で厳密に求めており、**R-Q2-01 と問いの形が同じ**。模型が違い、値は重ならない）。
  それ以外に R-Q2-01/03 の問いに触れるものは見つからなかった。
  ⚠ **§11 の「前方引用 16 件を全数」は OpenAlex の会議版レコードだけの数だった**（雑誌版レコードの 9 件と S2 のみの 8 件を見ていなかった）。
  ⚠ DBLP の会議単位の目視は**未実施**（API が bot 判定で取得不可）。S2 のブール検索
  `reversible + (pebble | pebbling | …)`（62 件）と OpenAlex の同式（88 件）で代替し、どちらも新顔 0 件
* ~~Semantic Scholar は 429 で使えなかった（`~/.env` に鍵はあるので、次回は鍵つきで叩く）~~
  → **2026-09-18 に鍵つきで実施**。1.2 秒間隔＋再試行で全リクエスト成功。
  S2 は OpenAlex より被引用の取りこぼしが少ない（Meuli+ 2019 で 46 対 2、BHL 続編で 1 対 0）。
  **OpenAlex は参照リスト未取り込みの論文を被引用に数えない**ので、前方引用の「全数」を OpenAlex だけで言わないこと。
  逆に S2 は版を併合して書誌を混ぜる（Královič が year=2001 になる）ので、書誌の裏取りには使わない
```

あわせて直すべき箇所（§4 の外）:

* **§3**「BHL 続編（2025・`W4409846353`）**被引用 0 件。** 前方引用の追跡はここで打ち止め」
  → 「OpenAlex では 0 件だが **S2 では 1 件**（KRV 2025）。BHL 2022 も S2 ∪ OpenAlex で 6 件（KRV 2025 が S2 のみ）」。表に KRV 2025 の行を足す。
* **§11** 冒頭「Královič 2004 の前方引用 16 件を全数見て見つけた」→「OpenAlex の会議版レコードの 16 件を見て」。
* **§12「残る未確認」** の 3 項目はいずれも消し込める（概念語の探索＝本調査、量子回路合成系＝要旨で確認、Komarath+ の前方引用＝S2 で 9 件全件）。
  DBLP の目視だけが残る。
* **§1** の末尾に「並列意味論の SAT 符号化は Quist–Laarman 2024（LMCS 2025）§4 にもある（spooky 版。ソルバ高速化のための工夫）」を 1 行。
* **§2** の差分表に KRV 2025 Remark 2.7／付録 B の列（鎖・3 行・非形式）と、KSS Def. 4.4 “sweep-first”（逐次 spooky・空間固定）の言及を足す。
* **§6 の対比表**に「並列 spooky（KRV 2025）: 時間最適 $2\ell$ を保てる最大 $\ell$ は $2^{\Omega(p)}$（$s \le 2.47\log\ell$ の逆）」の列を足すと三者比較になる。
* 新しい節（§13）として本ファイルの §1–§3 を移す。

---

## 5. §5（台帳への反映）は今も正しいか

| 項目 | 現在の §5 の記述 | 判定 | 直すなら |
|---|---|---|---|
| **R-Q2-01**（$n^*(p)$） | 「Meuli+ 2019 の符号化を引用すること。**問い自体は依然として見当たらない**」 | **後半が正しくなくなった** | 「Meuli+ 2019（と Quist–Laarman 2024）の符号化を引用すること。**問いの形には先例がある**: KRV 2025（EUROCRYPT 2026）§2.4・Fig. 2 が並列 *spooky* 模型で『最適深さを達成できる最小ペブル数』を A\* で厳密に求めている。**純可逆の並列模型での値 $7, 11, 17, \dots$ は見当たらない**（範囲: 核文献 12 本の引用元 610 レコード＋ S2/OpenAlex のブール検索。DBLP の目視は未実施）。漸近の枠は BHL 2025 Thm 1 が含意する（準多項式の上界。⚠ 紙の導出・未検算）。KRV 2025 と BHL 2025 を引用必須」 |
| **R-Q2-02**（$T_\parallel = 2\,\mathrm{depth}-1$） | 「初等的な補題なので新規性は主張しない方針を維持」 | **正しい。補強された** | 「鎖の下界は KRV 2025 Remark 2.7 が “straightforward” として 3 行で述べている」を根拠に足す |
| **R-Q2-03**（窓・余裕ゼロ） | 「Královič 2004 Lemma 3.2 との差分を明記した上で主張する」 | **正しいが不足** | 「Královič 2004 Lemma 3.2 **と KRV 2025 Remark 2.7／付録 B**（鎖・並列 spooky・非形式: 右端が毎手 ±1 しか動かないので、最適なら最初の $\ell$ 手は一直線）との差分を明記。**鎖の場合の最早配置は右端の議論からほぼ直ちに従う**ので、寄与は『任意の DAG・全頂点・両端で必ず存在・機械証明』の側に置く」 |
| R-Q2-04（`alt`）— §5 に行が無い | — | 本調査の範囲では変化なし | KRV 2025 の Thm 2.12 は「時間最適を保ったまま空間を減らす」再帰構成（Fibonacci 様の $A$-数列）で、**狙いが `alt` と同じ**（ゴーストを使う点が違う）。§7 の Bennett との対比に並べて言及する価値がある。⚠ 構成の中身の比較はしていない |

**台帳（`topic-mining/registry/`）について**: 本調査では触っていない。R-Q2-01 の新規性の根拠欄が「問いが見当たらない」に依っているなら、
その文言は上の表のとおり弱めるのが正確。層（R-Q2-01 層 2・R-Q2-02/03 層 1）は機械証明の有無で決まっているので、**本調査の結果では動かない**。

---

## 6. 限界（正直に）

* ふるいは題名＋要旨にしか効かない。**610 件中 205 件は要旨が取れず題名だけ**で判定した。本文のどこかで 1 段落だけ並列可逆ペブリングの時間最適点に触れる論文は、この方法では拾えない。
* 被引用追跡は「核文献を引用している論文」しか見ない。**核文献を 1 本も引かずに同じ問いを扱う論文は原理的に見えない**。その穴は S2/OpenAlex のブール検索（§1.1・§1.3）で塞いだつもりだが、検索も題名＋要旨が対象。
* Gidney の spooky pebble game の原典（2019 のブログ記事）は S2 に無く、その被引用は追えていない。KSS・Quist–Laarman・KRV の 3 本の被引用で代替した。
* DBLP の会議単位の目視は未実施（§1.4）。
* KRV 2025 は §1・§2・付録 B を通読したが、§3–§4（因数分解への応用）と付録 A, C–G は語の検索だけ。Fig. 2 の具体値は図からは読んでいない（数表が無い）。
* §3.2 の準多項式上界は紙の導出で未検算。
* `⚠ 検査していません`: 本ファイルに対する独立の検算（`saikensha` 等）は走らせていない。

---

## 7. 台帳の `novelty_check` 欄に**追記**する文（2026-09-18・親セッションが起草。⚠ 未反映）

`topic-mining` で別セッションが作業中だったため、台帳にはまだ入れていない。既存の欄の末尾に足す。

**`R-Q2-01`**

> ／2026-09-18 追加（exact-rev-complexity/docs/34a_survey_addendum_2026-09-18.md）: **問いの形には先例あり** — Kahanamoku-Meyer–Ragavan–Van Kirk（EUROCRYPT 2026, arXiv:2510.08432, 全文確認）§2.4・Fig.2 が並列 spooky 模型で「最適深さ 2ℓ を達成できる最小ペブル数」を A* で厳密に求めている（n*(p) の逆関数の形。模型・終状態・空間の数え方が違い値は重ならない。純可逆の 7,11,17,… は論文にも公開コード v0.1 にも無い）。**引用必須**。Semantic Scholar 鍵つきで核文献 12 本の引用元 610 レコードを全数ふるい（10 語を事前固定）、他に該当なし。⚠ DBLP の会議単位の目視は未実施・205 件は題名のみ。

**`R-Q2-03`**

> ／2026-09-18 追加（docs/34a_survey_addendum_2026-09-18.md）: 被引用の全数追跡を実施（Královič 32 レコード・Meuli 46 件ほか計 610 レコード、S2 鍵つき）。**Kahanamoku-Meyer–Ragavan–Van Kirk（EUROCRYPT 2026, arXiv:2510.08432）Remark 2.7／付録 B が同方向**（鎖・並列 spooky・非形式:「最適なら必ず一直線の blast で始まる」。補題は無い）。差分: 我々は任意の DAG・全頂点・両端で必ず存在・Lean。**言及必須。** ⚠ 以前の「続編の前方引用 0 件」は OpenAlex の数で、S2 では 1 件（＝この論文）だった。
