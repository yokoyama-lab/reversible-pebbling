# v15 と既存 4 原稿の重なり（2026-11-16）

対象: `overleaf/2026_erasure_pebbling`（英文 IEICE A・main.tex）、`2026_spooky_pebbling`（spooky_en/ja/qp）、
`2026_exact_reversible_pebbling`（増大率の原稿群）、`2026_exact_reversible_pebbling-autoresearch`（.tex なし・lean/ と notes/ の作業場）。
探し方: 各プロジェクトの `*.tex` を `rg --no-ignore` で、数（584・2916・472・`14^{k`）、語（半順序被覆・poset cover・線形拡張・
linear extension・全順序・実消去・actual erasure）、題の語で検索した。Lean は `rg --no-ignore -g '*.lean' -g '!.lake/**'` と
`find -L … -name '*.lean' | xargs grep` の 2 通りで、v15 系の識別子（`LocalCertificate`・`CommonExtension`・`pairTrace`・`LayerSpec`・
`IsExactCover`・`SignatureClass`）を 4 プロジェクトと `yokoyama-lab/reversible-pebbling-lean`・`spooky-pebbling-lean` から探した（0 件）。
数で当たったのは、無関係な 3 件（増大率の定数の桁の `584`、「$\le$ は全順序」の 2 件）だけだった。

| v15 の主張 | 既存 4 原稿 | どこに |
|---|---|---|
| モデル（鎖・容量・前駆不在の除去を実消去と数える） | 一部ある | erasure_pebbling の Def. erasure budget（l.134〜。前駆が使えない頂点からの除去を irreversible removal と数える）。量 $M^*(n,p,e)$ も同じ。両者とも LTV 1998 を引くが、v15 は erasure_pebbling を引いていない |
| 予算 $k$・容量 5 の最短値 $16k+9$（$n=5+6k$） | 無い（量だけ一部） | erasure_pebbling は $M^*$ の一般の床 $2n-1$ と $\mathrm{reach}(p,e)$、$p_{\min}$ での表（$n\le20$）。$16k+9$ の族は無い。v15 は Thumann–Soloveichik の漸化式から導く |
| 配置回数と実消去位置の固定・全順序の区間直積 | 無い | — |
| 語数 $400\cdot584^{k-1}$・最小被覆 $6\cdot14^{k-1}$ | 無い | — |
| 局所証明書 $I$・$M$（200／584 語・6／14・不合法共通拡張 15／91） | 無い | — |
| 隣接交換成分 $2^{k-1}$・成分の語数と被覆数 | 無い | — |
| 最小 DFA $40k+6$・順位付け・一様生成 | 無い | — |
| ガードを残す表現 472／2,916 → 200／584 | 無い | — |
| 一般の署名被覆定理（11-15・v16 で追加） | 無い | — |
| 交換連結性（線形拡張） | 無い（文献では既知） | Chan–Pak arXiv:2311.02743v2 Prop. 12.2（folklore）、Naatz 2000 |
| 累積石数（各時点の石数の和）という費用の尺度・可逆な鎖での累積費用の下界 | 無い（文献では既知） | さくらいの `NOVELTY_BOUNDARY.md`（showa、sha 83bedd18…）。Blocki–Zhou arXiv:1609.04449v2、Blocki–Holman–Lee ePrint 2024/334（書誌は arXiv API と ePrint のページで確認。v16 で引用） |
| 一般の poset cover 問題 | 無い（文献では既知） | Yuan–Wang arXiv:2505.04013v2（v15 で引用済み） |
| 最大費用層の全語が単独の全順序（I 6・M 14） | 無い | さくらいの `MaximalAlternation.lean`（showa、未コンパイル。`LocalCounts` に依存し、手元の 2G 上限では依存先が通らない） |
| spooky pebbling（ゴースト） | 対象外 | spooky_* は別モデル。重なりなし |
| 消去なしの鎖の増大率 | 対象外 | exact_reversible_pebbling。v15 は yokoyama2026 として引用済みで、問題設定が違うと明記 |

Lean の所在: erasure_pebbling → `yokoyama-lab/reversible-pebbling-lean`（と計算の `exact-rev-complexity`）、
spooky → `yokoyama-lab/spooky-pebbling-lean`、exact_reversible → `yokoyama-lab/reversible-pebbling-exact-rate`、
autoresearch → その `lean/`。v15 系の Lean（11-12〜15 のさくらいの単位）は、どれにも入っていない。

## 結論: v15 は独立の原稿として扱う

- 4 本のどれにも v15 の結論（全順序の分類・被覆数・オートマトン・局所証明書）は無い。重なるのはモデルの定義（erasure_pebbling）と引用関係だけ。
- erasure_pebbling は英文 IEICE A で「消去がどれだけ時間を買うか」（$M^*$ の最適値と reach）。v15 は和文 IPSJ PRO で「最適値を達成する固定族の全順序をいくつの半順序で書けるか」。
  問いも結論も投稿先も違う。v13 の README も「英文 Exact Time–Space–Erasure とは別原稿」と書いている。
  合流させると、どちらの原稿でも中心でない節が大きくなる（v15 は 11 頁）。
- ただし v15 の関連研究に erasure_pebbling（同じモデルでの最適値と reach）を 1 文で引くのが自然（人の判断。v16 には入れていない）。
- このため v16 は `audits/sakurai-2026-11-15/v16/` に作った（git 外）。
