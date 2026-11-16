# 並列可逆ペブリング（Q2）の新規性調査 — 2026-08-14

対象は次の 3 つの主張。

* **A**: 鎖で時間最適 $T=2n-1$ を保てる上限 $n^*(p)$ の厳密値（R-Q2-01・層2）
* **B**: $T_\parallel(G) = 2\cdot\mathrm{depth}(G) - 1$ の両側機械証明（R-Q2-02・層1）
* **C**: 時間窓定理と余裕ゼロ定理（R-Q2-03・層1）
* **D**: 交互構成・持ち上げ定理（R-Q2-04・層1）

## 結論を先に（3 点とも投稿前に効く）

1. **符号化は既発表**。SAT による並列可逆ペブリングの定式化は **Meuli+ 2019（DATE）§III**
   と実質同一。**我々の寄与として主張してはならない**（§1）。
2. **A の「逐次版」は Knill 1995 に明示的にある。** Observation 2.2(i)
   $F(n,S) = 2n-1$ for $S \ge n$、すなわち逐次では $n^*_{\text{seq}}(p) = p$（§6）。
   **寄与は「同じ問いを並列模型で問うと答えが $7,11,17,25,\dots$ に変わる」こと。**
   「30 年間問われなかった」ではなく「**逐次では自明だったので問う価値が無かった**」が正確。
3. **C は Královič 2004 Lemma 3.2 と同じ方向**（時間最適なら構造が固まる）。
   独立発見でも**言及なしに出してはならない**。差分は §2 の表。

4. **D は Bennett 1989 の 1 段の再帰と同じ仕事量（3/2）**だが、Bennett が時間を
   $T^{1.585}$ に延ばして払うのに対し、`alt` は**並列性で払って時間最適を保つ**（§7）。
   **総トグル数が $T$ を超えるので逐次では実現できない。** Bennett の戦略そのものではないが
   言及必須。

B は初等的なので新規性を主張しない（BHL Def.1 から直ちに従い、逐次版は Knill Obs 2.2(i)）。

---

## 1. Meuli, Soeken, De Micheli 2019（DATE）— **符号化は同じ**

*Reversible Pebbling Game for Quantum Memory Management*, DATE 2019, pp. 288–291.
現物: `gdrive:Paperpile/All Papers/M/Meuli et al. 2019 - ...pdf`

### §III の符号化（逐語）

> Problem 2 is encoded in terms of the pebble state variables $p_{v,i}$. For $v \in V$ and
> $0 \le i \le K$, those are Boolean variables that evaluate to true if the node $v$ is
> pebbled at time $i$.

> **Initial and final clauses** At time 0 all the nodes are unpebbled and at time $K$ all the
> outputs need to be pebbled and all the intermediate results unpebbled

> **Move clauses** If a node is pebbled or unpebbled at time $i+1$, then all its children are
> pebbled at time $i$ and time $i+1$:
> $\bigwedge_{i=1}^{K} \bigwedge_{(v,w)\in E} \big((p_{v,i} \oplus p_{v,i+1}) \to (p_{w,i} \wedge p_{w,i+1})\big)$

> **Cardinality clauses** At each step, at most $P$ pebbles are used:
> $\bigwedge_{i=0}^{K} \big(\sum_{v\in V} p_{v,i} \le P\big)$

**これは `scripts/q2_cnf.py` の `build()` と 1 対 1 に対応する。**
（我々の `par[v]` が彼らの $C(v)$、`x[v][t]` が $p_{v,t}$、`c.atmost(..., p)` が
cardinality clauses。move clauses の形も同一。）
XOR の形なので**1 ステップで複数頂点が変化してよい＝並列モデル**である点も同じ。

⚠ **したがって「並列可逆ペブリングを SAT で厳密に解く」こと自体に新規性は無い。**
`q2_cnf.py` のヘッダと論文の関連研究にこの引用を必ず入れること。

### 彼らが**していない**こと

* 深さへの言及が本文に**一度も無い**（`grep -i depth` で 0 件）
* 時間の下界を論じない。$K$ を 1 ずつ増やして最初に SAT になる点を探すだけ
* 扱う DAG は暗号の straight-line program と ISCAS ベンチマーク（`c432`, `c880` 等）。
  **鎖・ピラミッドのような構造族の厳密値の表は無い**
* 「時間最適を保てる最大サイズ」という問い（$n^*(p)$）は現れない
* Bennett 戦略との比較（Table I）はピーク $P$ と手数 $K$ の実測比較で、最適性の証明はしない

**位置づけ**: 応用側の道具論文。我々の A・B・C とは問いが違う。

---

## 2. Královič 2004 — **⚠ C と同じ方向を向いた補題がある**

*Time and space complexity of reversible pebbling*, RAIRO-ITA 38(2), 121–145.
現物: `gdrive:Paperpile/All Papers/K/Královič 2004 - Time and space complexity of reversible pebbling.pdf`

### Theorem 3.1（逐語）

> It holds that $S^{-1}(p) = 2^p - 1$. Therefore for minimal space function of the chain
> topology $S_{\min}(n)$ it holds $S_{\min}(n) = \Theta(\lg n)$.

これは**時間無制約**での「$p$ 個で到達できる最長の鎖」＝ half-reach $2^p-1$。
我々の $n^*(p)$（**時間最適 $T=2n-1$ を課したときの上限**）とは別の量である。
$n^*(4)=7 < 2^4-1=15$ のように、時間の制約が入ると激しく落ちる。

### ⚠ Lemma 3.2（逐語）— 我々の C と同じ方向

> An important fact is that **any time optimal computation must be symmetric.** The time of
> its subcomputation to the point where the vertex with the maximal number is pebbled is
> half of the time of the whole computation.
>
> **Lemma 3.2.** Let $K$ be a complete computation of length $l$ on $Ch_n$,
> $S(K) = S_{\min}(n)$, $T(K) = T(n, S_{\min}(n))$. Let
> $i = \min\{i \mid i \in \{1..l\} \wedge K(i)(n) = 1\}$. Then it holds that
> $T(\mathrm{Rst}(K,1,i)) = T(\mathrm{Rst}(K,i,l)) = T(K)/2$.

**差分（投稿時に必ず書く）**:

| | Královič Lemma 3.2 | 我々の `no_slack` |
|---|---|---|
| 決めるもの | **sink 1 個**の配置時刻が全体の中点 | **すべての頂点**の初出・最終存在時刻 |
| regime | **空間最適** $S = S_{\min}(n)$ での時間最適 | **時間最適** $T = 2\cdot\mathrm{depth}-1$（空間は無制約） |
| 主張の強さ | 前後半の長さが等しい | 窓 $[j+1,\ T-j-1]$ に閉じ込め、**両端で必ず存在** |
| 形式 | 紙の証明（Appendix B） | Lean 4・`sorry` 0・公理 `[propext, Quot.sound]` |

**同じ「時間最適なら構造が固まる」という直観**を扱っているので、独立発見であっても
**言及なしに出してはならない**。我々の主張は「Královič の対称性補題を全頂点に拡張し、
別の regime（時間最適・空間無制約）で厳密化したもの」と位置づけるのが正直。

### 個々の頂点の配置時刻

`grep` で `vertex j is pebbled at` / `first pebbled at` / `each vertex ... time` を探したが
**該当なし**。Lemma 3.3 は「各配置での最初にペブルされた頂点の位置の最大値」で、
時刻ではなく**位置**についての主張。

### この論文が解く問題

> given the minimal number of pebbles needed to perform the complete computation,
> what is the minimal time needed to perform it? This minimal time for space optimal
> reversible computation is described by the function $T(n, S_{\min}(n))$.

**トレードオフ曲線の反対の隅**である。彼ら: 空間を最小に固定して時間を問う。
我々: **時間を最小に固定して空間を問う**。この対比は論文の導入で使える。

---

## 3. BHL 系列の前方引用（2026-08-14 時点で全数確認）

### BHL 2022（TCC）

*The Parallel Reversible Pebbling Game: Analyzing the Post-quantum Security of iMHFs*
（arXiv 2110.04191v3）。OpenAlex `W4312698707`・**被引用 5 件**。全件:

| 年 | 題 | 我々への影響 |
|---|---|---|
| 2025 | Tight Bounds on the Spooky Pebble Game: Recycling Qubits with Measurements | 別モデル（測定つき）。既知 |
| 2025 | Red-Blue Pebbling with Multiple Processors: Time, Communication and Memory Trade-Offs | 別モデル（red-blue） |
| 2025 | **The Impact of Reversibility on Parallel Pebbling**（= ePrint 2024/334） | BHL 続編。本文確認済み・**漸近のみ** |
| 2025 | Dataflow-Specific Algorithms for Resource-Constrained Scheduling and Memory Design | 別分野 |
| 2026 | On the Need for (Quantum) Memory with Short Outputs | 空間下界と query complexity。無関係 |

要旨（逐語・最後のもの）:
> we establish the first separation between computation with bounded and unbounded space,
> for problems with short outputs … we introduce a problem called nested collision finding,
> and show that optimal query complexity can not be achieved without exponential memory.

### BHL 続編（2025・`W4409846353`）

**被引用 0 件。** 前方引用の追跡はここで打ち止め。**保留タスク「BHL 2024 続編の前方引用」は完了。**

> ⚠ **2026-09-18 訂正**: 0 件は **OpenAlex の数**。Semantic Scholar では **1 件**ある
> （Kahanamoku-Meyer–Ragavan–Van Kirk, EUROCRYPT 2026, arXiv:2510.08432。以下 KRV）。
> BHL 2022 も S2 ∪ OpenAlex で 6 件。OpenAlex は参照リスト未取り込みの論文を被引用に数えない。
> → `34a_survey_addendum_2026-09-18.md` §2–§3

---

## 4. まだ確認していないこと（正直に）

* ~~**Bennett 1989**~~ → **§7 で読了**（Table 2 を逐語確認。`alt` は Bennett の 1 段の
  再帰と同じ 3/2 の仕事量を、時間の延長でなく**並列性**で吸収したものと判明）
* ~~**Levine and Sherman 1990**~~ → **§8 で読了**（Bennett の定数因子の是正。別の隅）
* ~~**Knill 1995**~~ → **§6 で読了**（逐次モデルであることを確認。これが鍵だった）
* ~~**Bhattacharjee+ 2019**~~ → **§8 で読了**（Meuli と同じ研究室の応用論文。問いは現れない）
* ~~OpenAlex の全文検索は自然文クエリに弱く、「窓」「最早配置」のような概念での
  網羅的探索は**できていない**。DBLP の会議単位の目視か、Královič/Meuli の被引用の
  全数追跡が要る~~ → **2026-09-18 に被引用の全数追跡を実施**（`34a_survey_addendum_2026-09-18.md`）。
  Královič 2004 は S2 28 件・OpenAlex 24 件（会議版レコード 16 ＋ 雑誌版レコード 9）・和集合 32 レコード、
  Meuli+ 2019 は S2 46 件・OpenAlex 2 件。核文献 12 本の引用元 610 レコードを、先に固定した 10 語
  （parallel, depth, makespan, simultaneous, window, earliest, slack, schedule, time-optimal, minimum time）で
  ふるい（ヒット 92 件。`pebbl` との和で 118 件を目視、要旨なし 205 件は題名を全件目視）、16 本は全文で語を計数した。
  **結果: 新顔 1 本**（KRV ＝ 並列 *spooky* ペブリング。鎖で最適深さ $2\ell$ を達成できる最小ペブル数を
  A\* で厳密に求めており、**R-Q2-01 と問いの形が同じ**。模型が違い、値は重ならない。逐語は親セッションが全文で再確認）。
  それ以外に R-Q2-01/03 の問いに触れるものは見つからなかった。
  ⚠ **§11 の「前方引用 16 件を全数」は OpenAlex の会議版レコードだけの数だった**（雑誌版レコードの 9 件と S2 のみの 8 件を見ていなかった）。
  ⚠ DBLP の会議単位の目視は**未実施**（API が bot 判定で取得不可）。S2 のブール検索
  `reversible + (pebble | pebbling | …)`（62 件）と OpenAlex の同式（88 件）で代替し、どちらも新顔 0 件
* ~~Semantic Scholar は 429 で使えなかった（`~/.env` に鍵はあるので、次回は鍵つきで叩く）~~
  → **2026-09-18 に鍵つきで実施**（`scripts/survey34/s2.py`。1.2 秒間隔＋再試行で全リクエスト成功）。
  S2 は OpenAlex より被引用の取りこぼしが少ない（Meuli+ 2019 で 46 対 2、BHL 続編で 1 対 0）。
  **前方引用の「全数」を OpenAlex だけで言わないこと。** 逆に S2 は版を併合して書誌を混ぜる
  （Královič が year=2001 になる）ので、書誌の裏取りには使わない

---

## 5. 台帳への反映

* **R-Q2-01**（$n^*(p)$）: Meuli+ 2019 の符号化を引用すること。~~問い自体は依然として見当たらない~~
  → ⚠ **2026-09-18 訂正: 問いの形には先例がある。** KRV §2.4・Fig. 2 が並列 *spooky* 模型で
  「最適深さ $2\ell$ を達成できる最小ペブル数」を A\* で厳密に求めている（$n^*(p)$ の逆関数の形）。
  **純可逆の並列模型での値 $7, 11, 17, \dots$ は見当たらない**（範囲: 核文献 12 本の引用元 610 レコード＋
  S2/OpenAlex のブール検索。DBLP の目視は未実施）。**KRV と BHL 2025 を引用必須。** 売り方は
  「逐次／並列純可逆／並列 spooky」の三者比較に組み替える（`34a` §3.1）。
  漸近の枠（準多項式の上界）は BHL 2025 Thm 1 から従う見込みだが、⚠ 紙の導出・未検算（`34a` §3.2）
* **R-Q2-02**（$T_\parallel = 2\,\mathrm{depth}-1$）: 初等的な補題なので新規性は主張しない方針を維持
  （2026-09-18 補強: 鎖の下界は KRV Remark 2.7 が "straightforward" として 3 行で述べている）
* **R-Q2-03**（窓・余裕ゼロ）: **Královič 2004 Lemma 3.2 との差分を明記**した上で主張する。
  2026-09-18 追加: **KRV Remark 2.7／付録 B**（鎖・並列 spooky・非形式:「最適なら必ず一直線の blast で始まる」）
  との差分も明記する。鎖の場合の最早配置は右端の議論からほぼ直ちに従うので、寄与は
  「任意の DAG・全頂点・両端で必ず存在・機械証明」の側に置く

---

## 6. ⭐ なぜ古典文献に現れないのか — **逐次モデルでは自明だから**（2026-08-14 確定）

### Knill 1995 の設定（逐語）

> In Bennett's pebble game, we have a board of $n$ squares … **A move in the game consists of
> adding or removing a pebble.** A pebble can be added to or removed from square $s_i$ if
> $i = 1$ or if there is a pebble on square $s_{i-1}$.

> The pebble game is trivial without resource constraints. At the $i$'th step for
> $1 \le i \le n$ we can place a pebble on square $s_i$. At the $n+i$'th step for
> $1 \le i \le n-1$ we can remove the pebble on square $s_{n-i}$.
> **This solves the game in $2n-1$ steps using $n$ pebbles.**

> $F(n,S) = \min(T(\mathcal{S}) \mid S(\mathcal{S}) \le S)$

**1 手 1 ペブル＝逐次モデル**である。そして $T=2n-1$・$p=n$ の解は
**Knill が「自明」と呼んでいるもの**（我々が機械証明した `naive` / `layered` と同じ）。

### 紙の議論: 逐次では $n^*(p) = p$

逐次で $T = 2n-1$ を達成するとき、**総トグル数はちょうど $2n-1$**。
一方、各頂点は最低 1 回置かれ、sink 以外は最低 1 回消えるので下限も $n + (n-1) = 2n-1$。
**等号なので再計算の余地がゼロ**。すると

* 各頂点は「1 回置いて 1 回消す」だけ（sink は置くだけ）
* $v$ を消すには $v-1$ が要るので**除去の順は $n-2, n-3, \dots, 0$ に固定**
* 最初の除去（$n-2$）より前に sink の配置が済んでいなければならない
  （$n-2$ が消えたら二度と戻せず sink を置けない）
* よって**全配置が全除去より前**に起き、sink を置いた瞬間に $n$ 個すべてが盤上にある

したがって $p \ge n$ が必要、すなわち $\boxed{n^*_{\text{seq}}(p) = p}$。

### 機械での裏づけ（`tests/test_sequential_trivial.py`・CP-SAT・14 点全通過）

| $p$ | $n$ | 逐次 | 並列 |
|---|---|---|---|
| 4 | 4 | SAT | SAT |
| 4 | 5 | **UNSAT** | SAT |
| 4 | **7**（$=n^*(4)$） | **UNSAT** | SAT |
| 6 | 6 | SAT | SAT |
| 6 | 7 | **UNSAT** | SAT |
| 6 | **17**（$=n^*(6)$） | **UNSAT** | SAT |

並列解が実際に同時手を使っていることも確認した（`scripts/q2_profile.py`）:

| | 総トグル | 逐次の下限 | 同時 2 手のステップ |
|---|---:|---:|---:|
| $n=7, p=4, T=13$ | **19** | 13 | 6 |
| $n=11, p=5, T=21$ | **33** | 21 | 12 |
| $n=12, p=6, T=23$ | **35** | 23 | 12 |

**並列性が再計算の予算を生む。** 鎖では隣接しない 2 頂点が同時に動けるので、
1 ステップあたり最大 2 手まで使え、その余剰が再計算（＝空間の節約）に回る。

### 結論（論文の導入に使える）

> Bennett 1989 / Knill 1995 / Královič 2004 はいずれも**逐次**モデルであり、
> そこでは「時間最適を保てる最大サイズ」は $p$ に等しく自明である。
> 並列可逆ペブリング（Blocki–Holman–Lee 2022）で初めてこの量は非自明になり、
> $7, 11, 17, 25, 35, 47, 62, 81, 104$ という**閉じた式を持たない数列**になる。

**これが「なぜ 30 年以上この問いが現れなかったか」の説明である。**
⚠ ただし Knill の $F(n,S)$ の再帰は逐次での**時間最小化**を厳密に解いており、
**問いの形（時間を固定して空間を問う／空間を固定して時間を問う）が我々と対**である点は
必ず言及すること。

### ⚠ 逐次の答えは Knill 1995 に**明示的に書いてある**

> **Observation 2.2** (i) $F(n,S) = 2n-1$ for $S \ge n$.
> (ii) For $S \le S'$, $F(n,S) \ge F(n,S')$.
> (iii) For $n \le n'$, $F(n,S) \le F(n',S)$.

> **Theorem 2.3** $F(n,S) < \infty$ iff $n \le 2^{S-1}$.

**Observation 2.2(i) が逐次版の $n^*(p) = p$ そのもの**である（(ii) の単調性と合わせると
$F(n,S) = 2n-1 \iff S \ge n$）。**上の §6 の紙の議論は Knill の再発見**なので、
**自分の補題として書いてはならない**。書くなら「Knill Obs 2.2(i) の並列版」として書く。

また **Theorem 2.3 の $2^{S-1}$ は我々が「clean reach」と呼んでいる量**と一致する
（`data/q2_parallel_findings.md` の校正表の $2^{p-1}$）。Královič Thm 3.1 の $2^p-1$ は
relaxed（half-reach）側なので**別の量**。両方が既知値として校正に使われている。

### したがって、我々の寄与の正しい述べ方

| | 逐次（Bennett / Knill / Královič） | **並列（BHL 2022 の模型）** |
|---|---|---|
| 時間最適 $2n-1$ を保てる最大 $n$ | $p$（**Knill Obs 2.2(i)・既知**） | **$7, 11, 17, 25, 35, 47, 62, 81, 104$**（我々・閉じた式なし） |
| 時間無制約で到達できる最大 $n$（clean） | $2^{p-1}$（**Knill Thm 2.3・既知**） | 同じ（校正に使用） |
| 時間無制約（relaxed） | $2^p - 1$（**Královič Thm 3.1・既知**） | 同じ |

**同じ問いを並列模型で問うと答えが全く変わる**、というのが寄与の核。
「30 年間問われなかった」のではなく、**逐次では答えが `p` で自明だったから
問う価値がなく、並列模型（2021–2022）が現れて初めて非自明になった**が正確。

---

## 7. Bennett 1989 との関係 — **同じ仕事量を、時間でなく並列性で払う**（2026-08-14）

### Bennett 1989 Table 2（逐語）

> …then doing and undoing these segments in a hierarchical manner as shown in Table 2.
> This table shows that by **hierarchically iterating the simulation of 2 segments of
> original computation by 3 stages reversible computation**, $2^n$ segments of the original
> computation can be simulated in $3^n$ stages of reversible computation. More generally,
> for any fixed $k > 1$, $k^n$ segments of irreversible computation can be simulated by
> $(2k-1)^n$ stages of reversible computation.

> the number of intermediate checkpoints in storage at any one time is at most $n(k-1)$,
> which for fixed $k$ is $O(\log T)$ … the space requirement is $O(S \cdot \log T)$,
> while the time requirement is $O(T^{1 + 1/\log k})$.

**Bennett は時間を $T^{\log 3/\log 2} \approx T^{1.585}$ に延ばして空間を $O(S\log T)$ に落とす。**
モデルは**逐次**（1 ステージ = 1 チェックポイントの作成/破棄）。

### 我々の `alt` との対応

`alt` の**総トグル数**を測ると（`tests/test_alt_construction.py` の構成をそのまま使用）:

| 対象 | $T$ | 総トグル | 最小 $2\|V\|-1$ | 比 | 逐次で足りるか |
|---|---:|---:|---:|---:|---|
| 鎖 $n=8$ | 15 | 21 | 15 | 1.40 | **不可** |
| 鎖 $n=12$ | 23 | 33 | 23 | 1.43 | **不可** |
| 鎖 $n=20$ | 39 | 57 | 39 | **1.46** | **不可** |
| ピラミッド $h=6$ | 11 | 61 | 41 | 1.49 | **不可** |
| ピラミッド $h=10$ | 19 | 165 | 109 | 1.51 | **不可** |
| ピラミッド $h=14$ | 27 | 317 | 209 | **1.52** | **不可** |

**比は $3/2$ に収束する。これは Bennett の「2 セグメントを 3 ステージ」とちょうど同じ仕事量**
（$k=2$ の 1 段）。しかも**総トグル数が $T$ を超えている**ので、
**逐次モデルではこのスケジュールは実現できない**。

### 結論（R-Q2-04 の新規性の答え）

> `alt` は **Bennett の 1 段の再帰と同じ仕事量（係数 3/2）を行うが、
> それを時間の延長ではなく並列性で吸収する。**
> Bennett は $T \to T^{1.585}$ と時間を犠牲にして空間を得る。
> `alt` は**時間を $2\cdot\mathrm{depth}-1$ ちょうどに保ったまま**空間を約半分にする。
> これは逐次モデルでは不可能（総トグル数が時間を超える）。

したがって **`alt` は Bennett の戦略ではない**が、**Bennett の再帰を並列模型へ移したもの**
として位置づけるのが正確。論文では Bennett 1989 Table 2 を引き、
「同じ 3/2 の仕事量を時間でなく並列度で払う」と書く。

⚠ 多段（$k > 2$、すなわち $\alt$ より深い再帰）が並列模型でどこまで許されるかは未解析。
ピラミッドの $h \ge 9$ で実測が `alt` を下回るのは、まさにその多段が効いているため。

---

## 8. 残りの 2 本を読了（2026-08-14）

### Levine & Sherman 1990（SIAM J. Comput. 19(4), 673–677）

Knill が $F(n,S)$ の再帰の出典として引く論文。要旨（逐語）:

> Given any irreversible program with running time $T$ and space complexity $S$, and given
> any $\epsilon > 0$, Bennett shows how to construct an equivalent reversible program with
> running time $O(T^{1+\epsilon})$ and space complexity $O(S \ln T)$. Although these loose
> upper bounds are formally correct, **they are misleading due to a hidden constant factor
> in the space bound.** It is shown that this constant factor is approximately $e2^{1/\epsilon}$,
> which **diverges exponentially as $\epsilon$ approaches 0.** Bennett's analysis is simplified
> using recurrence equations and it is proven that the reversible program actually runs in
> time $O(T^{1+\epsilon}/S^\epsilon)$ and space $O(S(1 + \ln(T/S)))$.

**Bennett の定数因子を正した論文**であって、厳密値や時間最適のピークは扱わない。
regime は $T^{1+\epsilon}$ 対 $S\ln T$（＝時間を犠牲にする側）。**我々とは別の隅。**

### Bhattacharjee, Soeken, Dutta, Chattopadhyay, De Micheli 2019

*Reversible Pebble Games For Reducing Qubits in Hierarchical Quantum Circuit Synthesis*。
**Meuli+ 2019 と同じ研究室（Soeken, De Micheli）の応用側の論文。**

> we demonstrate and establish how reversible pebble games can be used to reduce the number
> of stored temporary results, thereby reducing the qubit count. … the qubit count can be
> signiﬁcantly reduced (by up to 63.2%) compared to the state-of-the-art algorithms,
> at the cost of additional gate count.

深さの下界も厳密値の表も無い（`grep -i depth` は T-depth の話のみ）。
**Meuli+ 2019 と同じ位置づけ**（応用の道具）。我々の問いは現れない。

### 文献側の結論（この時点で読了したもの）

| 文献 | モデル | 扱う量 | 我々との関係 |
|---|---|---|---|
| Bennett 1989 | 逐次 | $T^{1.585}$・$O(S\log T)$ の構成 | `alt` は同じ 3/2 の仕事量を**並列性**で払う（§7） |
| Levine–Sherman 1990 | 逐次 | Bennett の定数因子の是正 | 別の隅（漸近・時間を犠牲） |
| Knill 1995 | 逐次 | $F(n,S)$ の厳密な再帰 | **Obs 2.2(i) が逐次版の $n^*(p)=p$**（§6） |
| Královič 2004 | 逐次 | $T(n, S_{\min}(n))$・$S^{-1}(p)=2^p-1$ | **Lemma 3.2 が窓定理と同方向**（§2） |
| Meuli+ 2019 | **並列** | SAT による最小手数（応用） | **符号化が同一**（§1） |
| Bhattacharjee+ 2019 | 並列 | qubit 数削減（応用） | 同上の系統 |
| BHL 2022 / 2025 | **並列** | 漸近の space-time 積 | 模型の出典。厳密値は無い |

**残る未確認は「概念語による網羅探索」のみ**（OpenAlex の全文検索は自然文に弱い）。
DBLP の会議単位の目視か、Královič・Meuli の被引用の全数追跡が要る。

---

## 9. ⭐⭐ 完全二分木で**指数的な隔たり**が出た（2026-08-14）

### Královič 2004 Theorem 4.9（逐語）

> **Theorem 4.9.** For the minimal space function of the complete binary tree topology
> $S_{\min}(h)$ it holds that $S_{\min}(h) = h + \Theta(\lg^*(h))$, where the function
> $\lg^*$ … is defined as follows: $\lg^*(x) = 0$ for $x \le 0$,
> $\lg^*(x) = 1 + \lg^*(\lg(x))$ otherwise.

要旨にも「we show a tight optimal space bound for the binary tree of height $h$ of the
form $h + \Theta(\lg^* h)$」とある。**時間無制約での空間最適値**である。

### 我々の値（時間最適 $T = 2h-1$）

$$ p_{\min}(\text{完全二分木 } h) = 3 \cdot 2^{h-2} + 1 $$

（下界 `peak_lower_right`・上界 `alt_par_time_exact` の両方が機械証明済みで一致。
$h = 2..9$ の 8 点で SAT の実測とも一致。）

### 対比

| $h$ | $\|V\| = 2^h-1$ | **空間最適**（Královič・時間無制約） | **時間最適**（我々） | 比 |
|---|---|---|---|---|
| 5 | 31 | $\approx 5{+}2 = 7$ | **25** | 3.6 |
| 7 | 127 | $\approx 7{+}3 = 10$ | **97** | 9.7 |
| 9 | 511 | $\approx 9{+}3 = 12$ | **385** | 32 |
| $h$ | $2^h-1$ | $h + \Theta(\lg^* h)$ | $3\cdot 2^{h-2}+1$ | **指数的** |

$$ \boxed{\;\text{完全二分木では、時間最適性を課すと必要な空間が } \Theta(h) \text{ から } \Theta(2^h) \text{ へ指数的に増える}\;} $$

**これが論文の核になりうる。** 「時間最適性の空間コスト」を、
古典的に調べつくされた族について**厳密な閉じた式**で答えている。
Královič は同じ族の反対の隅（空間最適）を厳密に決めており、**対になる。**

⚠ 一般の $h$ に対する Lean の証明はまだ（`alt` のピークが $n_0+n_1+1$ であることを
一般に示すには奇数層の等比和の評価が要る）。各 $h$ では計算で確認している。
⚠ **この対比自体が既知でないかは未確認**（Královič は時間最適側を扱っていないが、
BHL 系列や他の並列模型の論文にないかを見る必要がある）。

---

## 10. 一般の下界「最も浅い 2 層は同時に居る」の新規性（2026-08-14）

主張（`peak_lower_levels01`・層1・任意の DAG）:
$$ p \;\ge\; \#\{v : \mathrm{dep}\,v = 0\} + \#\{v : \mathrm{dep}\,v = 1\} + 1 $$

### BHL 2022（arXiv 2110.04191v3）本文を確認した

* **Definition 1** の条件 (1)–(5) が我々の使っている並列可逆ペブリングの定義（一致を再確認）
* **Lemma 1** は長さ $2N$ の構成（前半で積み上げ、後半で対称に崩す）＝我々の `naive` / `layered`
  と同じもの。**BHL 自身が「naïve reversible pebbling strategy」と呼んでいる**
* **下界はすべて漸近**: `Ω̃(N^1.75)`（Argon2i-B）など iMHF の space-time コストについてのもの。
  `grep` で `lower bound` / `Ω(` を全数見たが、**構造的な下界（どの頂点が同時に必要か）は無い**
* 「すべての源が同時に必要」型の主張は**現れない**
  （`all sources` / `source nodes` / `inputs must ... simultaneously` などで 0 件）

### 現時点の判断

**BHL・Královič・Knill・Meuli・Bennett・Levine–Sherman のいずれにも見当たらない。**
ただし証明が 10 行と初等的なので、**folklore の可能性は残る**。
`docs/22_known_facts_ledger.md` の方針どおり、投稿前に
「初等的すぎて誰も書いていないだけ」の可能性を潰す必要がある
（`STATUS.md` に同種の注記の前例あり: 「1 回組 ≤ min(p,N)」は約 10 行なので folklore の可能性が高い）。

⚠ **概念語での網羅探索は依然できていない**（OpenAlex の全文検索は自然文に弱い）。
DBLP で TCC / STOC / FOCS / CCC の可逆ペブリング関連を目視するのが次の手。

---

## 11. ⭐⭐⭐ Komarath–Sarma–Sawlani 2016 は**逆の隅**を研究している（2026-08-14）

*Pebbling meets coloring: Reversible pebble game on trees*（arXiv 1604.05510 / JCSS 2017）。
Královič 2004 の前方引用 16 件を全数見て見つけた（⚠ 2026-09-18 訂正: 16 件は OpenAlex の**会議版レコードだけ**の数。
S2 ∪ OpenAlex では 32 レコード。残りも `34a` で全件見て、結論は変わらない）。**木を扱う唯一の系列**。

### 彼らの結果（逐語）

> We show that the **reversible pebbling number of any tree is exactly one more than the
> edge rank coloring number** of the underlying undirected tree. … Our result implies that
> the reversible pebble game number of trees can be computed in polynomial time.

> Besides the reversible pebbling number, another interesting parameter … is **the number of
> steps required to optimally pebble the given DAG**. For example, it is known that **paths can
> be optimally pebbled in $O(n \log n)$ steps**. We show … that **complete binary trees have
> optimal pebblings that take at most $n^{O(\log\log n)}$ steps**. This is a significant
> improvement over the previous upper bound of $n^{O(\log n)}$ steps.
> **It remains open whether complete binary trees can be pebbled in polynomial number of steps.**

> We also generalize a time-space trade-off result given for paths by Královič to families of
> bounded degree trees showing that for any constant $\epsilon > 0$, such families can be
> pebbled using $O(n^\epsilon)$ pebbles in $O(n)$ steps.

### 我々との関係——**同じトレードオフ曲線の反対の隅**

| | 固定するもの | 問うもの | 完全二分木での答え |
|---|---|---|---|
| Královič 2004 / **Komarath+ 2016** | **空間を最小に** | **時間** | $n^{O(\log\log n)}$ ステップ。**多項式かは未解決** |
| **我々** | **時間を最小に**（$T = 2h-1$） | **空間** | $3 \cdot 2^{h-2} + 1$（**厳密**） |

**同じ族（完全二分木）について、文献は「空間最適側の時間」を長く追いかけていて
（$n^{O(\log n)} \to n^{O(\log\log n)}$、多項式かは未解決）、
「時間最適側の空間」は問われていない。** 我々はそちらを厳密に答えている。

しかも彼らの空間最適値には**厳密な組合せ的特徴づけ**がある（辺ランク彩色数 + 1）。
**対比が非常に鮮明**:

| | 空間最適 | 時間最適 |
|---|---|---|
| 値 | 辺ランク彩色数 $+1$（$= h + \Theta(\lg^* h)$） | $3\cdot2^{h-2}+1$ |
| 計算量 | **多項式時間で計算できる**（Lam–Yue の線形時間アルゴリズム経由） | — |
| 反対側の資源 | ステップ数は $n^{O(\log\log n)}$、**多項式かは未解決** | ステップ数は $2h-1$（定義） |

### 判断

**我々の問い（時間最適側の空間）は、この系列にも現れない。**
彼らのモデルは逐次（Bennett のゲーム）だが、空間最小値は並列でも一致するので
（§9 で確認）、**値の比較は妥当**。

⚠ **引用必須**。論文では「Komarath+ が空間最適側の時間を追っているのに対し、
我々は時間最適側の空間を決める」と位置づける。
⚠ Siu Man Chan 2013（可逆ペブリング数 = Dymond–Tompa 数 = Raz–McKenzie 数）も
Paperpile にある（`Siu Man 2013 - Just a Pebble Game.pdf`）。**未読。**

---

## 12. 文献の全体像（2026-08-14 時点・読了分）

### Chan 2013（*Just a Pebble Game*）も空間側

> the Dymond–Tompa pebble game, the Raz–McKenzie pebble game, and the reversible pebble
> game of Bennett have the same **pebble cost**.

**「ペブル数（空間）」の等価性**であって、時間は扱わない。
（この論文の主眼は Dymond–Tompa ゲームが L vs NL・NC vs P の技法の障壁になること。）

### まとめ

| 文献 | モデル | 固定 | 問う | 対象 |
|---|---|---|---|---|
| Bennett 1989 | 逐次 | — | $T^{1+\epsilon}$ と $S\log T$ の構成 | 一般 |
| Levine–Sherman 1990 | 逐次 | — | Bennett の定数因子の是正 | 一般 |
| Knill 1995 | 逐次 | **空間** | **時間** $F(n,S)$ の厳密な再帰 | 鎖 |
| Královič 2004 | 逐次 | **空間** | **時間** $T(n,S_{\min})=\Omega(n\lg n)$ ／ $S_{\min}$ の値 | 鎖・木・バタフライ |
| Chan 2013 | 逐次 | — | **ペブル数**の等価性（Dymond–Tompa） | 一般 |
| **Komarath+ 2016** | 逐次 | **空間** | **時間** $n^{O(\lg\lg n)}$（**多項式かは未解決**）／ $S_{\min}$ = 辺ランク彩色数+1 | **木** |
| Meuli+ 2019 / Bhattacharjee+ 2019 | **並列** | 空間 | 時間（SAT で実用的に最小化） | 回路 |
| BHL 2022 / 2025 | **並列** | — | 漸近の space-time 積（iMHF 攻撃） | iMHF の DAG |
| **我々** | **並列** | **時間**（$T = 2\,\mathrm{depth}-1$） | **空間** | 鎖・ピラミッド・木・層状 |

**文献は一貫して「空間を固定して時間を問う」側。我々は反対側。**
唯一の並列模型の先行研究（Meuli+, BHL）も、前者は応用の道具・後者は漸近であり、
**時間最適点での厳密な空間を問うものは無い。**

### 残る未確認

* 概念語での網羅探索（OpenAlex の全文検索は自然文に弱い）。
  **DBLP で TCC / STOC / FOCS / CCC / MFCS の可逆ペブリング関連を目視するのが次の手**
* Královič の前方引用 16 件のうち、量子回路合成系（LUT-Based Hierarchical Reversible Logic
  Synthesis 2018、Quantum Multiplier 系 2023–2024 など）は応用側なので未読
* Komarath+ の前方引用（9 件）
