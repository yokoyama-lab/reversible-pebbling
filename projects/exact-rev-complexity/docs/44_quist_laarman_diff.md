# 44 — Quist–Laarman (RC 2023) との差分【決着】

2026-08-20。**本文 PDF を逐語で確認して決着**（RC 2023 の巻は Paperpile の
`All Papers/Other/RC 2023 2023 - RC 2023.pdf`。著者名では引っかからない）。
対象章は pp. 134–150。

> A.-J. Quist, A. Laarman, "Optimizing Quantum Space Using Spooky Pebble Games,"
> *Reversible Computation* (RC 2023), LNCS 13960, pp. 134–150.

---

## 0. 結論（1 行）

**「spooky pebbling を SAT で解く」という着想そのものは彼らが先。だが厳密性の担保
（証明ログ）・閉形式・機械証明は彼らに無く、対象グラフも違う。差分は明確に立つ。**

---

## 1. 差分表（すべて逐語確認）

| | **Quist–Laarman (RC 2023)** | **KSS (Quantum 2025)** | **我々** |
|---|---|---|---|
| 対象グラフ | **一般 DAG**。「we are the ﬁrst that study the spooky pebble game on general DAGs instead of line graphs as in [12]」（p. 136） | 線グラフ（鎖） | **鎖（線グラフ）** |
| ベンチマーク | **ISCAS85 の実回路**（c5315 は 1089 ノード等） | なし（紙） | 鎖の族 |
| 手法 | **SAT/BMC ソルバ**。「To our knowledge this is the ﬁrst solver for the spooky pebble game」（p. 136）。Z3 を使用 | 紙の証明・漸化式 | SAT/BMC ＋ **DRAT** ＋ Lean 4 |
| 厳密性 | ⚠ **打ち切ったら T を `Tskip` 進める**（Alg. 1）。`Twait`=60 s・`Tmax`=8 min。**最適性を確定しない探索** | 厳密（Cor 4.7/4.12） | **厳密**（n≤21・s≤6 を確定） |
| 下界の証明ログ | **無し**（章内の出現回数: `DRAT` 0・`proof log` 0・`certificate` 0） | 該当なし | **DRAT を `drat-trim` で検証**（最大 12 GB が `s VERIFIED`） |
| 閉形式 | **無し**（`closed form` 0・`theta` 0） | 漸化式 2 本 | θ(s)=s(s+1)/2、T_UG=4n−2s、T(n,3)=n²−n−3 ほか |
| 「下界」という語 | **章内 0 回** | あり（±1 評価） | 主題 |
| 定理証明支援系 | **無し**（`Coq` 0・`Isabelle` 0。`Lean` の 1 件は **`boolean` の部分一致**＝偽陽性） | 無し | **Lean 4**（`sorry` 0・標準 3 公理・変異注入 48 種） |
| 独自の定理 | §3「Spooky Pebble Cost Equals Irreversible [Pebble Cost]」（古典空間が使えるときの上限） | 多数 | 多数 |

---

## 2. 線引き

### ❌ 主張してはいけない

1. **「spooky pebbling を SAT で解く最初の道具」** — Quist–Laarman が先（RC 2023、Z3）。
   我々の R-Q7-04 は**この着想の先取りではない**。
2. **「BMC で spooky pebbling の厳密値を出す」** という枠組み自体の新規性。
3. **一般 DAG への拡張** — 彼らが先（KSS は線グラフのみ、と彼ら自身が書いている）。

### ✅ 主張してよい

1. **下界を検証可能な証明書として出すこと。** 彼らのソルバは打ち切ると `T` を `Tskip` 進めるだけで、
   **「その T では不可能」を確定しない**。我々は DRAT を出して `drat-trim` に通している。
   ⭐**これが最大の差分。**
2. **閉形式と、それを Lean の無条件定理へ上げること。** 彼らには閉形式も機械証明も無い。
3. **鎖（線グラフ）の厳密値の体系。** 彼らは一般 DAG の実回路がベンチマークで、
   族ごとの厳密値の表は作っていない。**KSS の体系が T_UP について閉じていない穴を埋める**
   という我々の位置は、彼らの仕事と直交する。
4. **T_UG ≠ T_UP のパリティによる分離。** 両者ともこの問いを立てていない。

---

## 3. 原稿での位置づけ（草案）

> Quist and Laarman [QL23] gave the first SAT-based solver for the spooky pebble game and
> were the first to study it on general DAGs, evaluating it on ISCAS85 circuits. Their solver
> searches for a strategy and, on timeout, simply advances the time bound; it therefore
> establishes upper bounds but does not certify optimality. We work in the opposite
> direction: on line graphs, where closed forms are within reach, we certify every lower bound
> with a DRAT proof and lift the resulting formulas to unconditional theorems in Lean 4.

---

## 4. 副産物 — 書誌が確定したもの（彼らの参考文献欄より）

- ⭐ **spooky pebble game の出典は Gidney の 2019 年のブログ記事**:
  C. Gidney, "Spooky pebble games and irreversible uncomputation" (2019),
  <https://algassert.com/post/1905>。
  ⚠ **"Halving the cost of quantum addition" (Quantum 2, 74, 2018) ではない。**
  2026-08-20 に一度そちらを引きかけたので注意。
  Quist–Laarman は「introduced recently by Gidney [8] and more extensive worked out by
  Kornerup et al [12]」と書き、§2.1 の見出しを "Measurement-Based Uncomputation" にしている。
- G. Meuli, M. Soeken, M. Roetteler, N. Bjorner, G. De Micheli,
  "Reversible pebbling game for quantum memory management," **DATE 2019, pp. 288–291**, IEEE.
- B. Komarath, J. Sarma, S. Sawlani, "Reversible pebble game on trees,"
  **COCOON 2015, LNCS 9198, pp. 83–94**（我々のノートが JCSS 2017 / arXiv 1604.05510 で
  引いていたものの会議版）。
- S. M. Chan, "Just a pebble game," **CCC 2013, pp. 133–143**。
- ⭐ S. M. Chan, M. Lauria, J. Nordström, M. Vinyals, "Hardness of approximation in PSPACE
  and separation results for pebble games," **FOCS 2015, pp. 466–485**。
  → **R-Q2-05 の folklore 判定でこれと Nordström のサーベイを必ず見ること。**
- J. Nordström, "New wine into old wineskins: a survey of some pebbling classics with
  supplemental results" (2015),
  <https://www.csc.kth.se/~jakobn/research/PebblingSurveyTMP.pdf>
  → **ペブリングの folklore を確かめるならまずこのサーベイ。**

---

## 5. 検証の手順（再現できる形で）

```sh
rclone copyto "gdrive:Paperpile/All Papers/Other/RC 2023 2023 - RC 2023.pdf" /tmp/RC2023.pdf
pdftotext /tmp/RC2023.pdf /tmp/rc2023.txt
sed -n '7283,8100p' /tmp/rc2023.txt > /tmp/ql_chapter.txt   # 該当章
grep -oic "DRAT\|certificate\|closed form\|lower bound" /tmp/ql_chapter.txt
```

⚠ **`Lean` の grep は `boolean` に当たる。** 語境界を付けて数え直すこと
（この章では真の出現は 0）。
