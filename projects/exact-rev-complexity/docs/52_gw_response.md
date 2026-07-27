# 52 — Grochow–Wolpert のモデル批判への応答（論文 §3 に入れる段落）

`docs/51_paper_plan_candidate3.md` §4 の穴 3。**これが書けないと落ちる**と判定していた項目。

---

## 0. 文献の入手状況（正直に）

| 文献 | 入手 | 状態 |
|---|---|---|
| **Grochow & Wolpert**, *Beyond Number of Bit Erasures*, SIGACT News 49(2):33–56, 2018, doi:`10.1145/3232679.3232689` | ❌ **本文未読** | ACM DL 有料。SFI Press 版（`sfipress.org/energetics/beyond-number-of-bit-erasures`）は**導入と文献一覧のみ**で本論が無い |
| **Wolpert & Kolchinsky**, *Thermodynamics of computing with circuits*, `arXiv:1806.04103v6` | ✅ **本文精読** | 無料公開。**著者の一方（Wolpert）が同じ**で、mismatch cost の技術的定義と定理を含む |

**⚠️ 投稿前に GW の本文を入手すること**（南山大の ACM DL 契約で取れるはず）。
下の応答は **Wolpert 自身の accessible な技術論文に基づく**もので、
GW の具体的な主張文には当たっていない。**この点は査読で不利になりうるので必ず埋める。**

---

## 1. 批判の要旨（我々の理解。GW 本文未読なので abstract と背景から再構成）

> Landauer 以来、計算の熱力学的コストは「消去したビット数」で測られてきた。
> しかし非平衡統計力学の進展により、実際の熱力学的コストは
> **入力分布と物理実装に依存**し、消去ビット数だけでは決まらないことが分かった。

したがって「$e$ 回の不可逆消去」を資源として数える本稿のモデルは、
**時代遅れの粗い近似ではないか**という批判が想定される。

## 2. 応答（Wolpert 自身の枠組みが我々を支持する）

Wolpert–Kolchinsky（`arXiv:1806.04103v6`, §III）は、エントロピー生成 (EP) を
**mismatch cost** と **residual EP** に分解し、次の 2 つを示している（本文 p.7 付近）:

> **(i)** 「$P$ が状態集合 $Z$ 上で**論理的に可逆**で $\mathrm{supp}\,p \subseteq Z$ ならば、
> **mismatch cost と Landauer cost はどちらも 0 でなければならない**」
>
> **(ii)** 「逆に $P$ が $Z$ 上で論理的に可逆でないならば、
> **$\mathrm{supp}\,p\subseteq Z$ なるすべての初期分布 $p$ に対して mismatch cost を 0 にはできない**。
> …したがって論理的に不可逆な写像を実装するどの固定過程にも、
> **避けられない EP を生む初期分布が存在する**」

この 2 つを我々のモデルに読み替えると:

- 本稿の**可逆な `put`/`take`** は論理的に可逆な操作なので、(i) より
  **mismatch cost も Landauer cost も 0**。つまり**現代の枠組みでも「無料」である**
  （Landauer 近似に頼った主張ではない）。
- 本稿の**不可逆消去**は論理的に不可逆な操作なので、(ii) より
  **避けられない EP が生じうる箇所そのもの**である。

> **したがって $e$ は「熱の量」ではなく、
> 避けられないエントロピー生成が生じうる箇所の個数を数える組合せ量である。**
> 現代の非平衡熱力学は「その箇所でいくら出るか」が入力分布と実装に依存すると言うが、
> **「どの箇所で出うるか」は論理構造だけで決まり、それを数えるのが $e$ である。**
> $e$ を最小化することは、**実装や入力分布に依存せずに、
> 避けられない散逸の機会の数を最小化すること**に対応する。

### 2.1 この応答の強みと限界

**強み**: 批判の出典の著者自身の枠組みで、我々の量が意味を持つことを示せる。
「Landauer は粗い」に対して「粗い Landauer に依存していない」と答えられる。

**限界（論文にも書く）**:
1. $e$ は **EP の量を与えない**。$e$ が小さくても、その少数回で大量の EP が出る実装はありうる。
   本稿の主張は「機会の数」の最小化に限る。
2. 逆に $e$ が下界になるとも主張しない（residual EP は可逆操作でも 0 でないことがありうる。
   W–K は「適切な準静的過程なら 0 にできる」と述べているが、これは実装への条件である）。
3. GW が提起している「計算量理論への具体的な問い」との関係は**未確認**（本文未読）。
   入手後、我々の $M^*(G,p,e)$ が彼らの問いのどれかに答えていないか照合する。

## 3. 今日の実測が援護材料になる（副次的な論拠）

`data/exp52_cutrod_findings.md` の実測で、既存の可逆メモ化実装が実際に払っている資源は

- **空間**（メモ表 7〜20 スロット）
- **スタック**（`topDownCutRod` でピーク **75,802** スロット）
- **時間**（総歩数 959〜27,157）

の 3 つで、**熱（不可逆消去）は一度も使っていない**ことが分かった。

> つまり実装者は、熱を使わない 2 つの設計点の間で選択させられている。
> 本稿の $e$ は**第 3 の軸を明示的に与える**ものであり、
> その軸の目盛りが「EP の量」なのか「EP の機会の数」なのかという問い（GW の批判）は、
> **軸を導入することの価値とは独立**である。
> 軸が無ければ設計者はそこを選べない。

この段落は「モデルが粗いかどうか」の議論を「設計空間に軸を足す価値」の議論にずらす。
**批判を否定せず、主張の射程を限定して受け止める**書き方であり、
査読で「反論に耳を貸さない」と取られるリスクが小さい。

---

## 4. 論文に入れる最終形（草案・約 200 語相当）

> Recent work in nonequilibrium statistical mechanics shows that the thermodynamic cost of
> a computation is not determined by its number of bit erasures alone: the entropy production
> depends on the input distribution and on implementation details [Grochow–Wolpert 2018].
> Our erasure budget $e$ is therefore **not** a measure of dissipated heat. What it measures is
> the number of *occasions* at which unavoidable entropy production can arise.
> This reading is supported by the decomposition of entropy production into mismatch cost and
> residual EP [Wolpert–Kolchinsky, arXiv:1806.04103]: for a map that is logically reversible on
> the relevant support, both mismatch cost and Landauer cost vanish, whereas for a logically
> irreversible map no single process can make the mismatch cost vanish for all input
> distributions. Hence the reversible moves of our game are free even in the modern framework,
> and the irreversible removals are exactly the steps that can incur unavoidable dissipation.
> Minimizing $e$ minimizes the number of such steps, independently of the input distribution and
> of implementation details — while making no claim about the magnitude of the dissipation.
> We regard this as the appropriate combinatorial abstraction: the *placement* of unavoidable
> dissipation is fixed by the logical structure, even though its *magnitude* is not.

**投稿前の必須作業**: GW 本文を入手し、この段落が彼らの主張を正しく要約しているか確認する。
（現状は abstract と Wolpert の別論文からの再構成。**引用の正確さに責任を持てる状態ではない。**）
