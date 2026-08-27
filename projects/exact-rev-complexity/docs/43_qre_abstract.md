# 43 — 量子リソース見積り（QRE）向けの翻訳と abstract

2026-08-20 起草。**目的は新規研究ではなく、既に層1で存在する結果を量子側の語彙へ移すこと。**
一次の材料は `registry/results.tsv` の **R-Q2-05 / R-Q2-08 / R-Q2-09** と
**R-Q7-03 / R-Q7-05 / R-Q7-07**、証明は `lean/Revgarbage/ParPebbleWindow.lean` と
`yokoyama-lab/spooky-pebbling-lean/SpookyPebbling/*.lean`。

---

## 0. なぜ今か（2026-08-20 に一次確認した外部状況）

- **QRE（Quantum Resource Estimation）という専用会議が立っている**（quantumresource.org）。
  見積りの支配項が「物理量子ビット数」から**コンパイル・ルーティング・スケジューリング**へ
  移った、という認識が業界側にある。
- **アンコンピュテーションの順序付けは量子コンパイラの実装課題になっている。**
  Unqomp (PLDI 2021)、Reqomp (Quantum 2024)、SQUARE (ISCA 2020)、
  Reichental ら (arXiv:2503.00822, 2025) が実装を持つ。
  ⚠ **訂正（2026-08-20）**: 当初「arXiv 2503.00822 が reversible pebbling game を直接使用」と
  書いたが**誤り**。本文で "pebbl" は**参考文献欄に 1 回のみ**（Meuli+ 2019 を引くところ）で、
  解法は位相ソートの探索＝ヒューリスティック。
  **可逆ペブリングを量子メモリ管理に持ち込んだのは Meuli+ 2019 (arXiv:1904.02121) のほう。**
  → 我々の位置づけはむしろ強くなる: **産業側の実装は厳密解も下界も持たない。**
- **spooky pebble game の本流は Quantum 誌に載った**:
  Kornerup–Sadun–Soloveichik, *Tight Bounds on the Spooky Pebble Game: Recycling Qubits
  with Measurements*, **Quantum, 2025-02-18**（arXiv:2110.08973）。
  我々のノートの「KSS」はこれ。**Cor 4.7 / Cor 4.12 / Thm 4.11 の番号がどの版のものかを
  投稿前に必ず固定すること**（arXiv v1 と Quantum 版で番号がずれうる）。

**要点**: 中身は既にある。足りないのは**語彙**と**出荷**だけ。

---

## 1. English abstract（arXiv 投稿用ドラフト）

> **Exact Costs of Uncomputation:**
> **Machine-Checked Space–Time Trade-offs for Reversible and Spooky Pebbling**

Resource estimates for fault-tolerant quantum computation are increasingly dominated by
compilation, and in particular by how a circuit's ancilla qubits are recycled. Two
combinatorial models capture this: the *reversible pebble game* (Bennett), which schedules
uncomputation, and the *spooky pebble game* (Kornerup–Sadun–Soloveichik), which trades
ancillas for measurement-based phase corrections. Both are studied almost exclusively in
the asymptotic regime — the wrong granularity for an estimator that must report an integer.

We determine exact values, and prove them in Lean 4.

**(i)** For *time-optimal* parallel reversible pebbling we give a closed form for the
minimum peak on complete binary trees, `p_min = 3·2^(D-1) + 1` for depth `D ≥ 2`, with
**both** the upper and the lower bound machine-checked for general `D`. Space-optimal
pebbling of the same trees needs only `Θ(D)` pebbles (Kralovic 2004), so **insisting on
depth-optimal uncomputation costs exponentially many ancillas.**

**(ii)** We generalize this to layered DAGs. Writing `n_k` for the number of vertices at
depth `k`, if `Σ_{k≥2} n_k ≤ n_0 + 1` then `p_min = n_0 + n_1 + 1` *exactly*; the two
shallowest layers must coexist, and nothing else is forced. The hypothesis predicts
tightness on 14 of the 14 families we tested, including the exact boundary case.

**(iii)** For the spooky game on chains we prove `θ(s) = s(s+1)/2` and
`T_UG(n,s) = 4n − 2s` on `s ≤ n ≤ θ(s)`, together with the sign reversal of
`δ = T_UG − T_UP` at `n = θ(s)`; and we **separate** `T_UG` from `T_UP` by a parity
invariant — a separation that the `±1` bound of KSS leaves open.

Every general theorem is `sorry`-free and uses only Lean's three standard axioms; every
bounded exhaustive claim carries a DRAT certificate verified by `drat-trim`.

*(≈240 words. quant-ph primary, cs.CC / cs.LO cross-list.)*

### QRE 読者に刺さる 1 文（要旨の冒頭とトークの表紙に置くもの）

> **Depth-optimal uncomputation is exponentially expensive in qubits — and we now know
> exactly when, with a machine-checked closed form.**

---

## 2. 語彙の対応表（これが翻訳の本体）

| ペブリング側（現在の書き方） | 量子側（QRE の読者の語彙） |
|---|---|
| ペブル / pebble | **ancilla qubit** |
| ピーク `p` / peak | **qubit count（幅）** |
| 時間 `T` / step | **circuit depth**（並列模型なので depth がそのまま対応する） |
| unpebble | **uncompute** |
| 時間最適 `T = 2·depth(G) − 1` | **depth-optimal uncomputation schedule** |
| 空間最適 | **qubit-minimal schedule** |
| ghost（spooky） | **measured-and-deferred qubit**（測定して古典ビットへ落とし、位相補正を後回しにした状態） |
| 依存 DAG の層 `n_k` | **オラクル回路の依存グラフの深さ `k` の演算数** |
| 鎖 `L_n` | 逐次合成されたオラクル（`n` 段のパイプライン） |
| 完全二分木 | **並列合成の極（分割統治型オラクル）** |

**⚠ 翻訳で落としてはいけない留保**: 我々の並列模型は BHL（Blocki–Holman–Lee, TCC 2022）
Definition 1 と一致することを本文照合で確認済み。**実機の並列度制約（接続性・同時実行可能な
ゲート数）は入っていない。** abstract では "in the standard parallel reversible pebbling
model" と明示する。

---

## 3. 主張してはいけないもの（台帳の novelty_check から）

投稿原稿でこれらを寄与として書くと、査読で確実に落ちる。**すべて確認済みの既知事実**。

1. **「鎖の最小量子空間は 3」は新しくない** — KSS Cor 3.4 で既知。
2. **SAT 符号化は Meuli+ 2019 (DATE) §III と実質同一** — 寄与として主張しない
   （逐語確認は `docs/34`）。
3. **`T = 2N − 1` の naive 構成は BHL §1.2 で既知**（彼ら自身が naive reversible
   pebbling と呼んでいる）。
4. **`n*(p)` の閉形式は未確定。少数項からの外挿は 4 回連続で反証されている。**
   `results.tsv` R-Q2-01 の警告を原稿に持ち込むこと。
5. ✅ **R-Q2-05 の folklore 判定は決着**（`docs/45_q205_novelty_verdict.md`）。
   掃いた範囲では**未出**。⭐ 最強の証拠は **Nordström のペブリングのサーベイ（139 ページ）で
   `reversible` 0・`Bennett` 0・`time-optimal` 0** なのに **§4 が 23 ページの "Layered Graphs"
   で仮定が我々と同一**であること。**関連研究にそのまま書く。**
   ⚠ ただし **機構の一段目は BHL 続編（EUROCRYPT 2025, Thm 9 の証明）に逐語で既出**。
   **「one-step non-simultaneity は [BHL25] に遡る。我々の寄与はそれを時間最適性のもとでの
   断面のピーク下界に変えた点」と 1 文で書くこと。落とすと刺される。**
6. ✅ **Quist & Laarman, RC 2023 との差分は決着**（`docs/44_quist_laarman_diff.md`、本文逐語）。
   **彼らが先なので主張してはいけないもの**: 「spooky pebbling を SAT で解く最初の道具」
   「BMC で厳密値を出す枠組み」「一般 DAG への拡張」。
   **我々が主張してよいもの**: 下界を **DRAT で証明書化**すること（彼らは打ち切ると T を
   進めるだけで最適性を確定しない。章内 `DRAT`/`certificate`/`closed form`/`lower bound` は
   すべて 0 回）、閉形式、Lean の無条件定理、T_UG ≠ T_UP のパリティ分離。
7. ⚠ **spooky pebble game の出典は Gidney の 2019 年のブログ記事**
   （"Spooky pebble games and irreversible uncomputation", <https://algassert.com/post/1905>）。
   **"Halving the cost of quantum addition" (Quantum 2, 74, 2018) ではない。**一度引きかけた。

---

## 3.5 必ず引く 2 本（2026-08-20 に発見。差分は `docs/45`）

1. **BHL の続編（EUROCRYPT 2025 / ePrint 2024/334）Theorem 9** — 我々の下界の機構の一段目が
   逐語である。ただし 1 本の path 上・累積コスト向けで、**断面のピーク下界も時間最適性の仮定も無い**。
2. ⭐ **G. D. Kahanamoku-Meyer, S. Ragavan, K. Van Kirk, "Parallel Spooky Pebbling Makes Regev
   Factoring More Practical," EUROCRYPT 2026**（arXiv:2510.08432）。
   **「深さをちょうど最適に固定して空間を最小化する」を明示的にやっている**（線グラフを深さ
   $2\ell$ ちょうどで空間 $\le 2.47\log\ell$、および A\* 探索）。**問いの形が同じ。**

   ⭐ **だが矛盾せず、むしろ物語が完成する。** 彼らは **spooky 模型・線グラフ**で
   「深さ最適は安い」($2.47\log\ell$)、我々は **clean 可逆・木**で「深さ最適は指数的に高い」
   ($3\cdot2^{D-1}+1$)。**源が 1 個か $2^{D-1}$ 個かの違いであり、
   R-Q2-05 の「代価は源の数で決まる」がその両端を説明する。**
   → **abstract の (ii) はこの対比を 1 文で入れると格段に強くなる。**

## 3.6 ⚠ 高さの規約

Královič の $h$ は**レベル数**（"height 1 ... one vertex"、頂点 $2^h-1$）。
その $h$ で $3\cdot2^{h-2}+1$、深さ $D=h-1$ で $3\cdot2^{D-1}+1$。
**abstract で $\Theta(D)$ と $\Theta(2^D)$ を並べるとき、どちらの規約かを明示すること。**

---

## 4. 出荷計画（科研費の締切 2026-09-17 と整合させる）

| 期限 | やること | 目的 |
|---|---|---|
| **8月下旬** | 上の §3-5, §3-6 の 2 件の novelty を潰す（DBLP 目視＋Quist–Laarman 精読） | 嘘を書かない |
| **9月上旬** | arXiv プレプリント投稿（本 abstract ＋ 既存の定理と表） | **科研費の「研究遂行能力」欄に書ける業績**にする |
| 9月中旬 | 科研費 基盤(B) 提出（`~/dev/uni/kakenhi/2027_kiban_b/骨子.md`） | 本命 |
| 10月以降 | QRE / IEEE QCE / RC 2027 / TQC へ本投稿 | 露出 |

**arXiv を先に出す理由**: 締切まで 28 日で査読誌は間に合わないが、プレプリントなら間に合う。
科研費の調書は「関連する研究成果」を書く欄があり、**arXiv 番号があるかないかで
「この計画は既に動いている」の説得力が変わる**。中身は既に層1 で存在するので、
書くのは導入と関連研究だけで済む。

---

## 5. 図（作成済み・2026-08-20）

**`data/figs/fig_time_vs_space.{pdf,png,svg}`**。生成は `scripts/gen_qre_figure.py`
（`.venv/bin/python` から実行）、系列の回帰テストは `tests/test_gen_qre_figure.py`（10/10 緑）。

横軸は完全二分木の高さ `h`（深さ `D = h-1`）、縦軸は ancilla 数（対数）。
実線 = **depth-optimal `3·2^(D-1)+1`**（両側とも Lean で機械証明）、
破線 = **qubit-minimal `Θ(D)`** の傾向（Královič 2004 の `h+Θ(lg* h)`）、
四角 = 我々が SAT で厳密に測った点（h=3,4,5）、白丸 = 近似値（h=9）。
**h=9 で 385 対 12、約 32 倍。** これが abstract の (i) の全部。

⚠ **h=2（D=1）は式の適用範囲外**（実測 3・式は 4）なので図から外してある。
この境界 `D≥2` は変異注入が発見したもの。キャプションで必ず断ること。

**検査の記録**: 系列テストに変異を 4 種入れて 4/4 検出
（指数を D にずらす／定理の境界を h≥2 に緩める／h=9 の近似値を厳密と偽る／傾向線を h+3 にする）。
⚠ 変異注入のたびに `__pycache__` を消すこと（消さないと検出率が嘘になる）。
