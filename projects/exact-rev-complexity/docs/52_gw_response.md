# 52 — Grochow–Wolpert のモデル批判への応答（論文 §3 に入れる段落）

`docs/51_paper_plan_candidate3.md` §4 の穴 3。**これが書けないと落ちる**と判定していた項目。

**2026-07-28: 本文を入手・精読した**（先生が Paperpile に所蔵。Paperpile の Google Drive 同期
`gdrive:Paperpile/All Papers/G/` から取得）。以下は**本文の表現に基づく**。

| 文献 | 状態 |
|---|---|
| **Grochow & Wolpert**, *Beyond number of bit erasures: New complexity questions raised by recently discovered thermodynamic costs of computation*, SIGACT News **49(2):33–56**, June 2018, doi:`10.1145/3232679.3232689` | ✅ **精読済み** |
| **Wolpert & Kolchinsky**, *Thermodynamics of computing with circuits*, `arXiv:1806.04103v6` | ✅ 精読済み（mismatch cost の技術的定義） |

---

## 1. GW が実際に述べている批判（本文から）

### 1.1 abstract の位置づけ

> "we now understand that while **logically reversible computing can have some thermodynamic
> benefits, it is far from the end of the story**"

つまり「可逆計算に利点が無い」ではなく「**それで話は終わらない**」という主張である。

### 1.2 核心は「会計」の議論（§2、本文 p.38 付近）

これが我々に最も関係する箇所である。$f$ を可逆関数 $f_r$ に埋め込んで
出力 $(x, f(x))$ を得る場合について:

> "since $f_r$ is logically reversible, there is no Landauer cost incurred when it produces the
> output $(x, f(x))$. … **This is misleading though.** In the case of embedding $f$ in a
> reversible function $f_r$, in addition to the sunk cost of erasing $f(x)$, we face an
> **additional cost of erasing the other component of the output, $x$**. … It is
> straight-forward to show that the cost of doing this is **precisely the Landauer cost of
> simply using the conventional computer to implement $f$ directly** … Ultimately, whether or
> not $f_r$ is considered to have lower Landauer cost than $f$ **depends on how we do the
> accounting**."

**要するに「可逆化して残した $x$ を最後に誰が消すのか」という会計の問題である。**

### 1.3 GW が提起している問いは我々の設定を含まない

> "In light of this, here we **focus almost entirely on implementing circuits with AND, OR, NOT**"

Question 3.2（普遍ゲート集合の下での最悪ケース熱力学コストの最小化。NP 困難か、MCSP に帰着するか）、
3.6（不正な prior に由来するコスト）、3.11、5.1（物理乱数とのトレードオフ）、
6.1–6.3（誤り訂正符号・ノイズのある素子・近似計算）は**すべて不可逆回路についての問い**であり、
**消去予算つき可逆ペブリングの時間計算量は含まれていない**。

→ **我々は GW の問いのいずれにも答えていない。** 論文でもそう明記する（下記 §3）。

## 2. 応答（GW の会計問題は、本稿のモデルがまさに固定するもの）

**GW の 1.2 の指摘は、本稿のモデルでは定義によって解決されている。**

- 本稿は**clean 到達**を要求する。すなわち終端では**目標以外に何も残さない**。
  GW が問題にする「残った $x$ を誰が消すのか」は、本稿では
  **「可逆な `take` の列で uncompute する」** と定めており、**消去しない**。
- 可逆な `take` は論理的に可逆なので Landauer コストを負わない
  （GW も 1.2 で「$f_r$ が出力を produce する分には Landauer コストが無い」と認めている）。
- **その代わりに払うのが手数（時間）である。** 本稿の $M^*(n,p,e)$ はまさにその値である。
- そして**可逆に片付けられない `take`** だけが不可逆消去であり、その回数が $e$ である。

> **したがって本稿は GW の「会計」問題に対して、
> 一つの明示的な会計方式（clean 終端を要求し、片付けの代価を手数で数え、
> 可逆に片付けられない回数だけを $e$ として別建てにする）を与え、
> その方式の下での厳密な値を決めている。**

さらに Wolpert 自身の技術論文（`arXiv:1806.04103v6` §III）は、我々の可逆操作が
**現代の枠組みでも**無料であることを支持する:

> 「$P$ が $Z$ 上で論理的に可逆で $\mathrm{supp}\,p\subseteq Z$ ならば、
> **mismatch cost と Landauer cost はどちらも 0** でなければならない」
> 「逆に $P$ が論理的に可逆でないならば、$\mathrm{supp}\,p\subseteq Z$ なる
> **すべての初期分布 $p$ に対して mismatch cost を 0 にはできない**」

→ **$e$ は「熱の量」ではなく、避けられないエントロピー生成が生じうる箇所の個数である。**
量は入力分布と実装に依存するが、**どの箇所で生じうるかは論理構造だけで決まる**。

## 3. 論文に入れる最終形（草案・約 210 語）

> Grochow and Wolpert [SIGACT News 49(2), 2018] argue that counting bit erasures does not
> capture the thermodynamic cost of a computation, and in particular that the apparent
> Landauer saving of embedding $f$ in a reversible $f_r$ "depends on how we do the accounting":
> the retained copy of the input must eventually be erased, at precisely the Landauer cost of
> computing $f$ irreversibly in the first place.
>
> Our model fixes that accounting explicitly. We require a *clean* terminal configuration, so
> the retained material is **uncomputed by reversible removals rather than erased**; what we pay
> for cleaning is *time*, and $M^*(n,p,e)$ is exactly that price. The budget $e$ counts only
> those removals that cannot be performed reversibly. Under this accounting the reversible moves
> are free even in the modern framework: for a map that is logically reversible on the relevant
> support, both mismatch cost and Landauer cost vanish, while for a logically irreversible map no
> single process makes the mismatch cost vanish for all input distributions
> [Wolpert–Kolchinsky, arXiv:1806.04103].
>
> We therefore read $e$ not as an amount of heat but as **the number of occasions at which
> unavoidable entropy production can arise** — its magnitude depends on the input distribution
> and on implementation details, but its *placement* is fixed by the logical structure. We make
> no claim about magnitude, and we do not address the open questions of [GW], which concern
> irreversible circuits built from AND/OR/NOT gates.

## 4. 実測が援護材料になる（副次的な論拠）

`data/exp52_cutrod_findings.md` の実測で、既存の可逆メモ化実装が実際に払っている資源は
**空間**（メモ表 7〜20）・**スタック**（`topDownCutRod` でピーク 75,802）・**時間**
（総歩数 959〜27,157）の 3 つで、**熱（不可逆消去）は一度も使っていない**。

> 実装者は熱を使わない 2 つの設計点の間で選択させられている。
> 本稿の $e$ は**第 3 の軸を明示的に与える**ものであり、
> 「その軸の目盛りが EP の量か機会の数か」という問い（GW の批判）は、
> **軸を導入することの価値とは独立である**。軸が無ければ設計者はそこを選べない。

**批判を否定せず、主張の射程を限定して受け止める**書き方であり、
査読で「反論に耳を貸さない」と取られるリスクが小さい。

## 5. 記録: この節を書くまでに踏んだ手順

1. 当初は abstract と二次情報から「消去ビット数は粗い」という批判だと**推測**していた。
2. ACM DL 有料・SFI Press 版は本論なし → **一度は「本文未読」と明記して草案を書いた**。
3. 先生が Paperpile 所蔵を教示 → **Paperpile の Google Drive 同期から現物を取得**
   （`gdrive:Paperpile/All Papers/G/`。`rclone copy` で読み取りのみ）。
4. 精読の結果、**批判の核心は「粗い」ではなく「会計」だった**ことが判明し、
   応答の骨格を書き換えた（§2）。**推測で書いた版とは論点が違っていた。**

→ 教訓（`docs/60_novelty_audit.md` §7 に同じことを書いた）: **本文を読むまで論点は分からない。**
abstract からの再構成は、方向は当たっても**論点を外す**。
