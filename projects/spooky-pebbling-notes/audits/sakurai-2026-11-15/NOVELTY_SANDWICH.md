# Sandwich（R-Q35-28）の新規性の確認（2026-11-16）

ユーザーの決定（2026-11-16「する」）を受けて実施。手順は novelty-check スキル（核の語を本文を読む前に決め、全文で数える）。
台帳は触っていない（提案は末尾）。

## 0. 判定（要約）

| 部分 | 判定 | 層 |
|---|---|---|
| **下界** W ≤ 3n・s = s_H ⇒ D ≥ H⌊log₂H⌋/16（H ≥ 16384）と一般形 `LogLower.paper_explicit_log_lower`・`SumArea.paper_finite_lower` | **新しい見込み**（下記の範囲で既出なし。LLJ 自身が「固定空間での work–depth のトレードオフ全体は未解決」と書いている） | 証明は層 1（Lean 緑・手元で再ビルド）。新規性は「確認した範囲で」 |
| 上下が Θ(H log H) で一致すること（W を固定したときの深さの次数の決定） | **新しい見込み**（同上）。LLJ の式 (38) からは W ≤ 3n で D = Ω(H·λ(H)²) しか出ない | 同上 |
| 上界の構成（block/boundary、1 段の block cleanup） | **既知の技法**（LLJ §3.4 の block cleanup・Lemma 3.6・3.7）。ただし「W ≤ 3n かつ深さ O(H log H)」という**明示的な点**は LLJ に書かれていない（LLJ の Algorithm 5 は s = Θ(n/H) で W = O(nλ(H))） | 層 1（`SkeletonUnfill.height_upper`） |
| W ≥ 3n − s − 1（全戦略） | **既知の型**（逐次の T ≥ 4n−2p−1 と R-Q35-05 の仕事量の恒等式からの並列版。新規性の主張にしない） | 不等式 3n+B ≤ W+2p+1 は Lean（Exceptions）、W の下界の形への書き換えは紙 |
| 解析の技法（入れ子の区間・累積の占有 Σ|P_t∪P'_t| ≤ sd） | **既知の系統**（LLJ の Lemma 4.2・Theorem 5.1 の区間と cumulative storage の論法と同族。累積量 A ≤ sD は LLJ 式 (27)）。新しいのは「最後の根の計算での切断」と W ≤ 3n から良い頂点（計算 1 回・除去 1 回）を大量に残す課金 | — |

**一言で**: 「W を固定（≤ 3n）したときの depth・space・work の三者で深さ Θ(H log H)」を述べた先行研究は、確認した範囲（下表）に無い。
最も近いのは LLJ で、同じ模型・同じ空間 Θ(n/H) で「最小 work Θ(n)」「最小 depth Θ(Hλ(H))」「最小 depth には Ω(nλ(H)) の work が要る（Thm 5.2）」まで。
Sandwich はその逆向き（work をほぼ最小に固定したときの深さ）で、LLJ が §7 に未解決として挙げた問いの 1 点を決める。

## 1. 核の語（本文を読む前に固定）

`/work/tmp/.../scratchpad/nov/TERMS.txt` に先に書いた（下に転記）。

- T1 `log log`（D = Θ(H log H) = Θ(log n · log log n) を n で書けば必ず出る）
- T2 `H log H` / `h log h` / `log n log log n`
- T3 `3n`（仕事量の係数 3 の固定）
- 補助: `work … depth` の同一行の共起、`trade-off`

## 2. 全文での出現（pdftotext -layout）

| 文献 | 範囲 | 総語数 | T1 log log | T2 H log H | T3 3n | 文脈（0 でないもの） | 判定 |
|---|---|---|---|---|---|---|---|
| LLJ: Lee–Lee–Jeong, arXiv:2610.09434v1（手元 `tree-gap/universal-lb/llj/`） | 全文 | 10,080 | 6 | 0 | 0 | log log はすべて s = h+1 の W = Θ(n log n/log log n)・D = Θ(n/log log n)（Thm 1.1 式 (6)、§3.4）と Thm 5.1 の証明内の補助不等式 (32)(33)。**固定 work での深さは無い**。§5.3 式 (38) W ≥ cnL − sD/L（L = λ(n) は**固定**で自由な引数ではない）、Thm 5.2、§7「the full work–depth tradeoff at a fixed space budget also remains open」 | 含まない（最近接） |
| KMRV: Kahanamoku-Meyer–Ragavan–Van Kirk, arXiv:2510.08432v3 | 全文 | 23,662 | 2 | 0 | 0 | 2 件とも線（line）の空間 1.3(2n+…) log log D の qubit 数 | 含まない（対象は線） |
| KSS: Kornerup–Sadun–Soloveichik, arXiv:2110.08973v3 | 全文 | 14,097 | 0 | 0 | 1 | 3n は漸化式 T(n)=n²+3n−2 | 含まない（逐次） |
| QL: Quist–Laarman, arXiv:2401.10579v7 | 全文 | 11,779 | 1 | 1 | 2 | log log・H log H は参考文献（Cook–Mertz の題名）。3n は QBF 帰着の pebbling cost P = 3n+4（空間であって work ではない） | 含まない |
| BHL22: Blocki–Holman–Lee, TCC 2022（Paperpile 版） | 全文 | 15,863 | 19 | 0 | 0 | すべて iMHF（Argon2i・DRSample）の cumulative/space-time cost O(N² log log N/log N) | 含まない（一般 DAG・MHF） |
| Blocki ほか EC 2025（eprint 2024/334、"The Impact of Reversibility on Parallel Pebbling"） | 全文 | 26,103 | 2 | 0 | 0 | 一般 DAG の reversible/classical の比較 | 含まない |
| Blocki2022（手元 `novelty/pdf/Blocki2022.pdf`、BHL22 の別版） | 全文 | 15,597 | 20 | 0 | 0 | 同上 | 含まない |
| Alwen–Serbinenko STOC 2015（cumulative complexity、Paperpile） | 全文 | 21,502 | 7 | 0 | 1 | 一般 DAG の cumulative complexity。3n は構成の区間 n/2〜3n/4 | 含まない |
| Alwen–Blocki–Pietrzak "Sustained Space Complexity"（arXiv:1705.05313、depth-robust 系） | 全文 | 22,171 | 10 | 0 | 3 | depth-robust DAG の CC O(n² log log n/log n) 等。3n は 3n/4 | 含まない |
| Alwen–Blocki CRYPTO 2016 "Efficiently Computing Data-Independent MHFs"（doi:10.1007/978-3-662-53008-5_9） | **未取得**（eprint 2016/115 は Cloudflare で拒否、OA 版なし） | — | — | — | — | — | **要確認** |
| Alwen–Blocki–Pietrzak EUROCRYPT 2017 "Depth-Robust Graphs and Their Cumulative Memory Complexity"（eprint 2016/875） | **未取得**（同上） | — | — | — | — | — | **要確認** |

一般 DAG・MHF 系（BHL22・AS15・ABP・AB16）は、対象が木でない・work（操作回数）を固定しない・累積量（CC）の下界であって深さの下界ではない、という点で Sandwich と主張の型が違う。
AB16・ABP17 の 2 本は全文未取得なので、この系統について「無い」は**要旨と被引用側からの推定**にとどまる。

## 3. 前方引用（2 つ以上の源で突き合わせ）

| 源 | 対象 | 結果 |
|---|---|---|
| OpenAlex（mailto=claude-research@example.com） | LLJ（W7220928765）を引く文献 | **0 件**（2026-11-16）。0 件は LLJ が 6 週間前の preprint であることによる可能性が高く、「無い」とは読まない |
| OpenAlex | KSS を引く 2026-06 以降 9 件、KMRV を引く 3 件 | 題名で見て、木の並列 work–depth を扱うものは無い（Erasynth・MBUndo・ECDSA.Fail・Streaming Regev・cat qubits 等、応用寄り）。MBUndo（arXiv:2611.02345）は全文で spooky 4・log log 0。**題名だけで除外したものは本文未読** |
| arXiv の全文検索（"spooky pebbling"、新しい順） | — | 4 件のみ（LLJ・KMRV・QL・KSS）。"pebble game"・"pebbling" の 2026 年分も題名で確認し、関連しそうな 2610.27249・2610.08929 は全文で spooky 0・log log 由来の一致なし |
| OpenAlex の題名検索 "spooky pebbling"（2026-09 以降） | — | 6 件。新しいのは Thumann–Soloveichik arXiv:2610.24435（全文で spooky 2、LLJ を引かない）と MBUndo |
| Semantic Scholar | LLJ・KMRV の被引用 | **未確認**（無認証で 429 を 5 回。`S2_API_KEY` は使っていない） |
| DBLP | "spooky pebbling" | **未確認**（Anubis の bot 拒否） |

→ 依頼の「2 つ以上で突き合わせ」は **OpenAlex と arXiv 全文検索の 2 源**で満たした。S2・DBLP は未確認。

## 4. 「W を固定したときの depth と space の三者トレードオフで Θ(H log H)」

- LLJ: 固定空間での work と depth は**別々に**最適化（「Work and depth are minimized separately」）。work と depth の結合は Thm 5.2（最小深さ側の work）と式 (38) だけで、§7 で全体を未解決と明記。
  式 (38) に W ≤ 3n を入れると sD ≥ L(cnL − 3n) = Ω(nL²)、すなわち D = Ω(Hλ(H)²)（L = λ(n) は固定値なので L を log H まで動かすことはできない）。**Θ(H log H) は出ない。**
- KMRV・KSS・QL: 線または逐次。木の work 固定の深さは無い。
- MHF 系: CC・space-time の下界で、work 固定の深さの次数は無い。
- **結論: 確認した範囲には無い。**

## 5. 層

- Sandwich の数学: **層 1**（Lean 4.35.0 で手元再ビルド、閉包 39 モジュール・定理 1111 本が標準 3 公理、変異 2/2 検出。INDEX.md §2）。
  ただし模型と LLJ 本文の対応は読み合わせ（Lean の定理ではない）。
- 新規性: 「確認した範囲（上表の全文 9 本＋前方引用 2 源）で既出なし」。AB16・ABP17 の全文と S2・DBLP の前方引用は未確認。

## 6. 論文化

- **置き場: 別の短い論文**（`<local>/dev/notes/spooky-pebbling/paper-sandwich/sandwich_ieice.tex`、IEICE Trans. A LETTER、ieice.cls）。
  既存の `overleaf/2026_spooky_pebbling` は「線（鎖）の逐次の厳密値」の PAPER（8 頁の目安）で、木・並列・work 固定の結果は対象も模型も違い、節として入れると主題がぶれて頁も超える。
  木の論文 `tree-gap/paper-ieice/tree_ieice.tex`（Trans. A PAPER）も逐次の木で模型が違う。
- 投稿先: POLICY.md P1（国内誌優先）に従い **IEICE Trans. A LETTER**［第 2 候補: IPSJ JIP］。⚠ P9（1 誌 1 編）で Trans. A は行列が長い（spooky-pebbling・urtm2state・erasure-pebbling・letter 4 本）。順番は人の判断。
- 現状: 3 頁、`latexmk sandwich_ieice` rc=0、.log にエラー・Overfull・Underfull なし（和文の太字斜体の font warning 1 件のみ）、PDF はソースより新しい（10:48）。著者・所属・謝辞・Lean の公開リンクは TODO。bib 7 件は Crossref で DOI を確認（LLJ は arXiv の PDF の表記で確認）。
- 原稿での主張の書き方: 「the lower bound is new」は §1 に 1 回だけ。比較は §6 で「we found no statement … in these works」と範囲つき。

## 7. 台帳 R-Q35-28 の novelty_check 欄への提案（台帳は未変更）

> 2026-11-16 novelty-check: 核の語 log log / H log H / 3n を LLJ・KMRV・KSS・QL・BHL22・Blocki EC25・Alwen–Serbinenko・ABP sustained space の全文で数え、W 固定の深さの下界は既出なし。LLJ §7 が固定空間の work–depth トレードオフ全体を未解決と明記、式 (38) からは D = Ω(Hλ²) のみ。上界の構成は LLJ §3.4 の block cleanup、W ≥ 3n−s−1 は既知の型。前方引用は OpenAlex（LLJ 被引用 0）と arXiv 全文検索で確認、S2・DBLP は 429/bot 拒否で未確認、AB16・ABP17 は全文未取得。判定: 新規の見込み（範囲つき）。記録 notes/spooky-pebbling/audits/sakurai-2026-11-15/NOVELTY_SANDWICH.md
