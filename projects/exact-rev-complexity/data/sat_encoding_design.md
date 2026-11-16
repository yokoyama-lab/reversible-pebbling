# $M^*(G,p,e)\le k$ の SAT 符号化設計（実装前仕様）

作成日: 2026-08-10

この文書は `scripts/sat_pebble.py` を書く**前**に、決定問題の意味と CNF の
正当性を固定するための仕様である。対象は `landauer.py` の `mode="ops"`、すなわち
1 手で 1 頂点だけを put/take し、先行点が揃っていない take を不可逆消去 1 回と
数える clean $e$-消去可逆ペブリングである。一括消去を許す `mode="bits"` は対象外。

## 1. 決定問題

DAG $G=(V,E)$、常時利用可能でペブル数に数えない頂点集合 $F$、目標 $q$、
ピーク上限 $p$、不可逆消去予算 $e$、手数上限 $k$ を入力とする。
$V'=V\setminus F$ と書く。問うのは、次を満たす長さ $L\le k$ の手順が存在するかである。

- 初期配置は空、終端配置は $\{q\}$（clean 終端）。
- 1 手は $V'$ の 1 頂点の put または take。
- put$(v)$ では直前に $v$ の全先行点が配置中または $F$ にある。
- take$(v)$ で同じ条件が成立しなければ、不可逆消去を 1 回使う。
- どの配置でも $V'$ 上のペブル数は $p$ 以下。
- 不可逆消去は合計 $e$ 回以下。

`target in free` は既存 BFS の規約に従って最適値 0 とする。それ以外では
$0\le q<|V|$, $p,e,k\ge0$ を要求する。

## 2. 時間展開変数

時刻 $t=0,\ldots,k$ とステップ $t=0,\ldots,k-1$ を置く。

| 変数 | 意味 |
|---|---|
| $x_{t,v}$ | 時刻 $t$ に $v\in V'$ がペブル済み |
| $P_{t,v}$ | ステップ $t$ が put$(v)$ |
| $R_{t,v}$ | ステップ $t$ が take$(v)$ |
| $I_t$ | ステップ $t$ は idle |
| $A_{t,v}$ | 時刻 $t$ に $v$ の全非 free 先行点がペブル済み |
| $Z_{t,v}$ | take$(v)$ が不可逆消去 |

各ステップで

$$I_t,\quad \{P_{t,v}:v\in V'\},\quad \{R_{t,v}:v\in V'\}$$

の**ちょうど一つ**を真にする。さらに

$$I_t\Rightarrow I_{t+1}$$

を加え、実手を先頭 $L$ ステップ、idle を末尾 $k-L$ ステップに正規化する。
これは意味を変える対称性除去ではない。任意の $L\le k$ 手の合法手順の末尾に
$k-L$ 個の identity（idle）を足せる。逆に充足割当てから idle 接尾辞を除けば
$L\le k$ 手の手順になる。途中の idle も状態を変えないため末尾へ移せる。

## 3. CNF 節

以下で $N(v)=\operatorname{pred}(v)\setminus F$ とする。

### 境界条件

各 $v\in V'$ について $\lnot x_{0,v}$。時刻 $k$ では $x_{k,q}$、および
$v\ne q$ に対する $\lnot x_{k,v}$ を加える。

### 可用性

$A_{t,v}\leftrightarrow\bigwedge_{u\in N(v)}x_{t,u}$ を Tseitin 符号化する。

- 各 $u\in N(v)$ について $(\lnot A_{t,v}\lor x_{t,u})$。
- $(A_{t,v}\lor\bigvee_{u\in N(v)}\lnot x_{t,u})$。
- $N(v)=\varnothing$ なら単位節 $(A_{t,v})$。

### 状態遷移

各 $t,v$ に次を加える。

- $P_{t,v}\Rightarrow\lnot x_{t,v}$、$P_{t,v}\Rightarrow x_{t+1,v}$。
- $R_{t,v}\Rightarrow x_{t,v}$、$R_{t,v}\Rightarrow\lnot x_{t+1,v}$。
- $\lnot P_{t,v}\land\lnot R_{t,v}$ なら
  $x_{t+1,v}\leftrightarrow x_{t,v}$。

最後の同値は次の 2 節で表す。

$$
(P_{t,v}\lor R_{t,v}\lor\lnot x_{t,v}\lor x_{t+1,v}),\qquad
(P_{t,v}\lor R_{t,v}\lor x_{t,v}\lor\lnot x_{t+1,v}).
$$

### 手の合法性と不可逆消去

put の合法性として $P_{t,v}\Rightarrow A_{t,v}$ を加える。take 自体は常に可能だが、

$$Z_{t,v}\leftrightarrow(R_{t,v}\land\lnot A_{t,v})$$

を 3 節で表す。

$$
(\lnot Z_{t,v}\lor R_{t,v}),\quad
(\lnot Z_{t,v}\lor\lnot A_{t,v}),\quad
(\lnot R_{t,v}\lor A_{t,v}\lor Z_{t,v}).
$$

### 濃度制約

Sinz 型の逐次カウンタで以下を CNF 化する。

- 各ステップの action 集合に exactly-one。
- 各時刻 $t$ で $\sum_{v\in V'}x_{t,v}\le p$。
- 全ステップで $\sum_{t,v}Z_{t,v}\le e$。

逐次カウンタは補助変数 $s_{i,j}$（先頭 $i+1$ リテラル中に少なくとも
$j+1$ 個が真なら真）への単調な含意を置き、$k+1$ 個目の真を禁止する。
入力数を $n$、上限を $b$ とすると補助変数・節は $O(nb)$。
$b=0$ は全入力を偽にする単位節、$b\ge n$ は無制約、$b<0$ は空節とする。

## 4. 正当性

### 健全性（SAT $\Rightarrow M^*\le k$）

exactly-one により各非 idle ステップは一つの頂点だけを操作する。遷移節により
`x` はその操作どおりに変わり、他の頂点は保存される。$P\Rightarrow A$ と $A$ の
定義により全 put は合法である。$Z\leftrightarrow(R\land\lnot A)$ と
$\sum Z\le e$ により不正な可用性での take は漏れなく高々 $e$ 回である。
境界節とピーク制約も直接ゲームの条件を表す。idle 接尾辞を捨てれば、長さ
$L\le k$ の合法な clean 手順を得る。

### 完全性（$M^*\le k\Rightarrow$ SAT）

長さ $L\le k$ の合法手順から、最初の $L$ ステップの $P/R$、各時刻の配置 $x$、
可用性 $A$、不可逆 take $Z$ を定義し、末尾を idle にする。ゲームの条件から
全ての節と濃度制約を満たす。したがって CNF は決定問題と同値である。

### 非 free 目標では $M^*$ が奇数である理由

目標 $q\notin F$ とする。実手の put 数を $a$、take 数を $r$ とすると、
空配置から 1 個だけの終端へ行くので
$a-r=1$。よって実手数は $a+r=2r+1$ で必ず奇数。このため既知値 $M^*$ の
下界確認は $k=M^*-2$ を使う。ただし実装する決定問題自体は偶数の $k$ も受理し、
idle によって「$k$ 以下」を正しく表す。

## 5. 証明と検証のパイプライン

1. 上の節だけを DIMACS CNF として保存する。
2. CaDiCaL 3.0.1 を `--binary=false` で実行し、UNSAT 時の ASCII DRAT を保存する。
3. **CaDiCaL の終了状態だけでは下界確定としない。** 同じ CNF と DRAT を
   PATH 上の `drat-trim` に渡し、終了コード 0 かつ `s VERIFIED` を確認する。
4. 検証器が無い、時間切れ、非 0 終了、または `s VERIFIED` が無ければ、結果は
   「CaDiCaL は UNSAT と報告したが証明は未検証」と記録する。
5. SAT 側はモデルから手順を復号し、CNF とは別の手続き型検証器で初期・終端・
   put/take 規則・ピーク・消去数・手数を再検査する。

グラフの自己同型などを仮定する対称性除去は入れない。idle 接尾辞の正規化は §2 の
明示的な全単射的変換で正当化し、全て通常の CNF 入力節として与える。このため証明形式は
DRAT、検証器は `drat-trim` とし、DPR/SR 用の `dpr-trim` は使わない。

## 6. 事前に固定する回帰条件

`landauer_bfs` の既知値について、各ケースで $k=M^*$ が SAT かつ復号手順が有効、
$k=M^*-2$ が UNSAT かつ DRAT VERIFIED であることを要求する。

| case | $p$ | $e$ | $M^*$ |
|---|---:|---:|---:|
| chain(4) | 3 | 0 | 9 |
| chain(4) | 3 | 1 | 7 |
| chain(6) | 4 | 0 | 15 |
| chain(6) | 4 | 1 | 11 |
| chain(8) | 4 | 0 | 25 |
| chain(8) | 4 | 1 | 17 |
| chain(12) | 5 | 0 | 39 |
| chain(12) | 5 | 1 | 29 |

加えて小さい DAG と全小手数を BFS に照合し、逐次カウンタ単体も全割当てで検査する。
