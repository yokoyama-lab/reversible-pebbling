# 95 — 占有度チェック: `R-CBT-01`（$M^*(T_5)=155$）（2026-09-18）

台帳 `R-CBT-01` の `novelty_check` 欄が空だったので実施した。数は `bib-auditor` エージェントに
取らせ、最も近い 1 本（Komarath+）の逐語と `155` の 0 件は親セッションが現物で再確認した。
現物（PDF・txt・前方引用の JSON）は作業時のスクラッチにあり、リポジトリには入れていない。

## 0. 核となる語（⚠ 本文を開く前に固定した）

| # | 語 | 意図 |
|---|---|---|
| D1 | `complete binary`・`binary tree` | 対象を扱っているか |
| D2 | `\b155\b` | 値そのもの |
| D3 | `exact`・`optimal`・`minimum` | 厳密な手数の主張か（**文脈を読む**） |
| D4 | `trade-?off`・`time.space` | ペブル数制約の下での手数を論じているか |
| 対照 | `pebbl` | 抽出の健全性 |

## 1. 結果（すべて**全文**。回数は該当行数）

| 文献 | 語数 | complete binary | binary tree | `155` | exact | optimal | minimum | trade-off | time.space | pebbl |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| Komarath–Sarma–Sawlani, JCSS 2018, DOI 10.1016/j.jcss.2017.07.009（arXiv:1604.05510） | 6,126 | 17 | 16 | **0** | 5 | 47 | 8 | 4 | 4 | 253 |
| Královič 2004（⚠ 取得できたのは同著者の**学位論文**。RAIRO 版 DOI 10.1051/ita:2004008 の本文そのものではない） | 14,810 | 18 | 57 | **0** | 7 | 29 | 3 | 1 | 13 | 284 |
| Meuli+ DATE 2019, DOI 10.23919/date.2019.8715092 | 3,922 | 0 | 0 | **0** | 2 | 1 | 3 | 5 | 2 | 63 |
| Bhattacharjee+ ISMVL 2019, DOI 10.1109/ismvl.2019.00026 | 5,765 | 0 | 0 | **0** | 2 | 2 | 1 | 4 | 1 | 41 |
| Torán–Wörz, comput. complex. 2021, DOI 10.1007/s00037-021-00206-1（ECCC TR19-097 rev.1） | 13,294 | 0 | 0 | **0** | 9 | 22 | 11 | 4 | 2 | 233 |
| de Rezende+ CCC 2019, DOI 10.1007/s00037-020-00201-y | 12,736 | 0 | 2（無関係） | **0** | 11 | 2 | 0 | 68 | 13 | 293 |
| Quist–Laarman arXiv:2401.10579 | 11,520 | 0 | 0 | **0** | 6 | 14 | 0 | 30 | 2 | 561 |

前方引用（Semantic Scholar・全数）: Komarath+ **9 件**、Meuli+ **46 件**。題名を `tree` ×
(`exact|optimal|minimum|steps|moves|time`) でふるって**候補 0 件**（`tree` を含む題名は 1 件で無関係）。
⚠ 前方引用は**題名（一部要旨）のみ**の確認。OpenAlex はこの分野では被引用を過少に返す（Komarath で 0 件）。

## 2. 最も近い先行研究 — Komarath–Sarma–Sawlani 2018 §4–5

**木の手数を論じる唯一の文献。** 逐語:

> We give an optimal pebbling of complete binary trees that takes at most $n^{O(\log\log(n))}$ steps,
> where $n$ is the number of nodes in the tree. Our pebbling is essentially the same as in [7].

> **Theorem 17** There exists an optimal pebbling of $Bt_h$ that takes at most $n^{O(\log\log(n))}$ steps.

> In light of Theorem 17, the natural question to ask is whether there are polynomial time optimal
> pebblings for complete binary trees.（§5 冒頭）

ここで "optimal" は**ペブル数が最小**の意。つまり彼らが上から抑えている量は
「最小ペブル数での手数」で、**`R-CBT-01` が $h=5$ で厳密に決めた量と同じ種類**である。
ただし与えているのは漸近上界だけで、具体的な $h$ の数値・表は無い（`155` 0 件）。
Královič は木については**空間**（$h+\Theta(\lg^* h)$）のみで、time-space の節は鎖専用。

⚠ 添字の対応に注意: 本リポの「$T_h$ free-leaves」は既存実装と**レベルが 1 ずれる**（`docs/20` §3）。
Komarath の $Bt_h$ と並べて書くときは、$R^\bullet(Bt_3)=5$ と $p_{\min}=5$ の一致で対応を確かめること。

## 3. 判定

**占有なし（探索範囲内）。** 「完全二分木・ペブル数固定での最小手数の具体値」を載せた文献は、
全文 7 本＋前方引用 55 件（題名）の範囲で見つからなかった。⚠ 不在の証明ではない。

書き方:
* **Komarath+ 2018 Theorem 17 を必ず引く**（同じ量の漸近上界。§5 の「多項式時間の最適ペブリングは
  あるか」という問いに対し、こちらは小さい $h$ の厳密値という別の角度のデータを与える）。
* 有界事例 1 点（$h=5$）であることは変わらない（層 2 のまま。`STATUS.md` の規則）。

## 4. 台帳の `novelty_check` 欄に書く文

> 実施済み（2026-09-18、`docs/95_novelty_R-CBT-01.md`）。核となる語は本文閲覧前に固定
> （complete binary・binary tree / 155 / exact・optimal・minimum / trade-off・time-space、対照 pebbl）。
> **全文 7 本**（Komarath+ JCSS 2018・Královič 2004 学位論文・Meuli+ DATE 2019・Bhattacharjee+ ISMVL 2019・
> Torán–Wörz 2021・de Rezende+ CCC 2019・Quist–Laarman arXiv:2401.10579）で `155` は 0 件。
> 木の手数を論じるのは Komarath+ のみで、Theorem 17「最小ペブル数のペブリングで $n^{O(\log\log n)}$ 手」
> という**漸近上界だけ**（具体的な $h$ の値・表なし）。Královič は木については空間のみ。
> 前方引用 55 件（S2 全数・題名のみ）に候補 0。⇒ 占有なし（探索範囲内。不在の証明ではない）。
> ⚠ Komarath+ Thm 17 は同じ種類の量の上界なので**必ず引用する**。⚠ Královič は RAIRO 版でなく
> 学位論文で確認した。
