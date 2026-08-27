# 45 — R-Q2-05（層 0＋層 1 の共存下界）の新規性判定【決着】

2026-08-20。台帳 `results.tsv` R-Q2-05 の novelty_check に残っていた宿題
（「投稿前に DBLP で TCC/STOC/FOCS/CCC の可逆ペブリング関連を目視すること」）の決着。

**判定: 「時間最適 ⇒ 最も浅い 2 層が共存する」という断面のピーク下界は、掃いた範囲では未出。
ただし機構の一段目は BHL に既出なので、引用と差分の明示が必須。**

---

## 1. 一番効く証拠（負の証拠）— Nordström のサーベイ

> J. Nordström, "New wine into old wineskins: a survey of some pebbling classics with
> supplemental results," 2015-03-25, **139 ページ**.
> ⚠ KTH の URL は **404**（"Denna sida är inte längre i bruk"）。現物は
> <https://jakobnordstrom.se/docs/publications/PebblingSurveyTMP.pdf>

全文の語数（**独立に再計数して一致**）:

| 語 | 出現 |
|---|---|
| `reversible` | **0** |
| `Bennett` | **0** |
| `time-optimal` | **0** |
| `Layered Graph` | 26 |

そして **§4 のタイトルが "Layered Graphs"（14–37 ページ、23 ページ分）で、仮定が我々と同一**:

> "For the layered DAGs $G$ that we will study in this paper, we will assume that **all sources
> are on level 0**, that all non-sources have indegree 2, and that there is a **unique sink** $z$.
> This means that the **height will be equal to the depth**..." （§4.1、逐語）

模型は逐次（Def 2.1: "$P_t$ follows from $P_{t-1}$ by **one** of the rules"）。
`parallel` の 4 件はすべて別義。§13「このサーベイで扱わなかった結果」にも可逆は現れない。

> ⭐ **論旨**: 層状 DAG は古典ペブリングの正典で 23 ページ分やり尽くされているのに、
> **可逆ゲームも並列模型も時間最適性も、この正典に一度も現れない。**
> 「初等的すぎて誰も書いていないだけ」説に対する、いま手に入る最も強い反証。
> **関連研究の節でそのまま使う。**

---

## 2. 該当しなかったもの

- **Chan–Lauria–Nordström–Vinyals, FOCS 2015**（arXiv:2305.19104）: 可逆ペブリングを扱うが
  **空間（価格）だけ**。PSPACE 完全性と加法定数近似の困難性。規則は逐語で 1 頂点ずつ。
  `time-optimal` 0 回・`number of steps` 0 回。**並列模型も時間最適性も無い。**
- **Alwen–Serbinenko STOC 2015 §4.1 / ABP17**: 古典の上界側のみ
  （"greedily pebble $G$ in topological order in time depth($G$)"）。
  ⭐ **古典は削除が自由なので、時間最適のピークは $\max_i n_i$ にしかならず、
  $n_0+n_1$ の共存は出ない。ここが可逆性の効きどころで、差分は鮮明。**
- **DBLP 全ダンプの census**（2026-08-18、8,692,534 レコード）: タイトルに `pebbl` を含む
  全数のうち、可逆／並列／量子ペブリングは **22 本のみ**で全部確認済み。
  OpenAlex の "time-optimal pebbling" / "depth-optimal pebbling" / "pebbling"+"layered DAG"
  はいずれも **0 件**。

---

## 3. ⚠ 必ず引き、差分を明示しなければならない 2 本

### (A) BHL の続編 — **機構の一段目は既出**

> J. Blocki, B. Holman, S. Lee, EUROCRYPT 2025（ePrint 2024/334）, **Theorem 9 の証明**:
> "we are not allowed to **simultaneously remove the pebble from node $v_{d-1}$ while we are
> placing a pebble on node $v_d$**"（逐語）

**我々の下界の核心機構がここにある。** ただし彼らは:
- **1 本の path 上**で使い、$2d-1$ ラウンドの時間窓から**累積コスト** $\Pi_{cc}\ge e(2d-1)$ を出す
- **断面のピーク下界は無い**（$\max_t |P_t|$ を下から押さえていない）
- **時間最適性の仮定も無い**

→ 原稿では「the one-step non-simultaneity observation goes back to [BHL25, Thm 9]; our
contribution is to turn it into a **cross-section peak bound under time-optimality**, which
they do not state」と書く。**この 1 文を落とすと査読で刺される。**

### (B) EUROCRYPT 2026 の新しい隣接論文 — **台帳に無かった**

> G. D. Kahanamoku-Meyer, S. Ragavan, K. Van Kirk,
> **"Parallel Spooky Pebbling Makes Regev Factoring More Practical," EUROCRYPT 2026**,
> arXiv:2510.08432（v1 2025-10-09 / v3 2026-07-03）。

**abstract を独立に確認した（逐語）**:
> "we show by construction that a line graph of length $\ell$ can be pebbled in
> **depth $2\ell$ (exactly optimal)** using **space $\le 2.47\log\ell$**"
> "we use a highly optimized A\* search implemented in Julia to find the lowest-depth
> parallel spooky pebbling possible for a range of concrete line graph lengths $\ell$
> given a constant number of pebbles $s$"

**彼らは「深さをちょうど最適に固定して空間を最小化する」を明示的にやっている。問いの形が同じ。**

差分（すべて我々に有利）:

| | KRV EUROCRYPT 2026 | 我々 |
|---|---|---|
| 模型 | **spooky**（測定＝ghost 手あり） | **clean な可逆**（測定なし） |
| グラフ | **線グラフのみ** | 一般の層状 DAG・木・ピラミッド |
| 手法 | 構成 ＋ **A\* 探索**（Julia） | 厳密全数 ＋ SAT/**DRAT** ＋ **Lean** |
| 結論の向き | 鎖では**深さ最適が安い**（$2.47\log\ell$） | 木では**深さ最適が指数的に高い**（$3\cdot2^{D-1}+1$） |

⭐ **矛盾しない。むしろ同じ軸の両端である。** 鎖は源が 1 個、完全二分木は源が $2^{D-1}$ 個。
**「深さ最適性の代価は源の数で決まる」**という我々の R-Q2-05 の主張が、
彼らの安い側と我々の高い側の両方を説明する。**物語としてはこれ以上ない。**
（鎖では我々の下界は $p\ge 1+1+1=3$ で自明なので、値の衝突も無い。）

---

## 4. 掃いた範囲と、掃いていない範囲

**掃いた**: DBLP 全ダンプ census（8,692,534 レコード、タイトルの `pebbl` 全数）、
arXiv API 20 クエリ・619 本、OpenAlex 概念クエリ 14 本、
本文確認: Nordström サーベイ全 139 ページ、CLNV FOCS 2015 全文、BHL 本体と続編、
Alwen–Serbinenko / ABP17 / ABP18、KSS、Meuli+、Královič、Knill、Chan、Bhattacharjee+。

**掃いていない（原稿に書く留保）**:
1. **全文検索はしていない**（タイトル＋アブストラクト＋読んだ本文まで）。
2. **Abe & Sung, "Parallelizing with Limited Number of Ancillae," UMC 2000 — 全文は依然入手できず。**
   ⚠ 題目が近い。ただし **2026-08-20 に所在を確定した**ので、あとは取り寄せるだけ:

   | 経路 | 現況 |
   |---|---|
   | DBLP | レコードあり（Hideaki Abe, Shao Chin Sung / UMC 2000）。**`ee` リンク無し**＝オンライン版が登録されていない |
   | CiNii Research | **2 件ヒット**。CRID `1571417126743280128` / `2120589364333558400` |
   | ⭐ **JAIST テクニカルレポート版** | **`IS-RR-2000-019`**、2000-07-04、**pp. 1–11**、ISSN 0918-7553。<https://hdl.handle.net/10119/14617> ⚠ **リポジトリに書誌はあるがファイルが添付されていない** |
   | Springer の巻 | *Unconventional Models of Computation, UMC'2K*（Antoniou, Calude, Dinneen 編、Springer、DMTCS 叢書、ISBN 1-85233-415-0、DOI 10.1007/978-1-4471-0313-4）。⚠ 南山大の Springer 契約は**要確認**（ACM DL・IEEE Xplore・ScienceDirect は可） |

   **現実的な最短経路（推奨順）**:
   1. **JAIST 図書館へ `IS-RR-2000-019` の複写依頼**（レポート番号が確定しているので確実）。南山大の ILL 経由
   2. **著者に直接連絡** — Shao-Chin Sung は国内の研究者（DBLP pid 119/3059 と 88/7022 の 2 レコード）。可逆計算の分野なのでメール 1 通が最短かもしれない
   3. Springer の巻（契約次第）

   **⚠ これが未入手のままでも投稿は止めない。** 原稿の留保としてその旨を書けばよい
   （2000 年の技術報告で、並列可逆ペブリングゲームの定式化（BHL 2022）より前）。

---

## 5. ⚠ 高さの規約（抄録で必ず揃える）

Královič の $Bt(h)$ は逐語で
「A complete binary tree of **height 1** ... containing **one vertex**」＝**レベル数の規約**
（頂点 $2^h-1$・葉 $2^{h-1}$）。この $h$ では $n_0+n_1+1 = 3\cdot2^{h-2}+1$
（`results.tsv` の書き方）。深さ $D=h-1$ では $3\cdot2^{D-1}+1$。

**抄録で $\Theta(D)$ と $\Theta(2^D)$ を 1 文に並べるときは、どちらの規約かを明示すること。**
図（`data/figs/fig_time_vs_space.pdf`）は横軸 $h$・注記 $D=h-1$ で統一済み。
