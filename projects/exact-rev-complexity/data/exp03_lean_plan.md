# exp03 — 定理 A の Lean 形式化プラン（2026-07-27）

> **状態: 未着手（形式化していない）。** 本ファイルは「形式化できる形まで落とした証明」であり、
> Lean のコードは書いていない。理由: 担当範囲のファイル許可リストに `.lean` が含まれておらず、
> 新規 Lean プロジェクトの作成は権限外。**ここに書いた命題をそのまま Lean に落とせる状態**にある。
> 既存の Lean 資産は `~/dev/github.com/tetsuo-jp/gen_janus/260612/formal/`（`leanprover/lean4:v4.31.0`,
> `native_decide` による表検証の前例あり）なので、そこに `Landauer/` を足すのが最短。

## 1. 二層の切り分け（`docs/00_overview.md` C4 / `idea03` §6 に対応）

| 層 | 内容 | 手段 |
|---|---|---|
| **L1** | 定理 A（$e^*_{\text{ops}}(n,p)=\lceil (n-1)/(p-1)\rceil-1$）を**無条件**に証明 | 通常の証明。$n,p$ は任意 |
| **L2** | 曲面の表（$n\le20$, $e\le6$ の $M^*$）を有界全数検査 | `native_decide`。信頼境界が広がるので L1 と明確に区別する |

L1 が本命。**定理 A の証明は純粋な有限組合せに落ちており、実数・解析を一切使わない**ので
Lean 化の難易度は低い（難所は「ゲームの意味論の定義」であって、証明の中身ではない）。

## 2. 形式化する定義

```lean
/-- 鎖 chain n 上の状態: ペブルの載った頂点集合（頂点 0 は常時可用な源で、集合には入れない）。 -/
abbrev St (n : ℕ) := Finset (Fin n)   -- 頂点 1..n を Fin n で 0..n-1 に読み替える

/-- 頂点 v の取り除き／置きが可逆か（先行点 v-1 がペブル済み、または v が先頭）。 -/
def ready (s : St n) (v : Fin n) : Prop :=
  v.val = 0 ∨ (∃ u : Fin n, u.val + 1 = v.val ∧ u ∈ s)

/-- 1 手。`erase` は不可逆消去（`ready` が偽のときの取り除き）。 -/
inductive Step (p : ℕ) : St n → ℕ → St n → ℕ → Prop
  | put   (s v) : ready s v → v ∉ s → (insert v s).card ≤ p → Step p s k (insert v s) k
  | take  (s v) : ready s v → v ∈ s → Step p s k (s.erase v) k
  | erasr (s v) : ¬ ready s v → v ∈ s → Step p s k (s.erase v) (k+1)

/-- `Reaches p e s k s' k' m` : 予算 e 以内で m 手で移る。 -/
-- 反射推移閉包に手数を載せたもの（略）

/-- M*(n,p,e) : ∅ から {n-1} へ、消去 ≤ e で到達する最小手数。 -/
noncomputable def mstar (n p e : ℕ) : Option ℕ := ...
```

**注意**: `mode="bits"`（一括消去）はここでは形式化しない。L1 の主張は `ops` のみ。

## 3. L1 の証明構造（`data/exp03_results.md` 定理 A と同じ）

### 3.1 上界（構成）— `theorem esat_le`

```lean
theorem esat_le (n p : ℕ) (hp : 2 ≤ p) :
    mstar n p (⌈(n-1)/(p-1)⌉ - 1) = some (2*n - 1)
```

証明は**明示的なスケジュールを構成して `Step` の列を組み立てる**。
Python 側で既に機械検証済み（`tests/test_exp03_proof.py::test_upper_bound_construction`、
$n\le21$, $p\le7$ で規則・ピーク・消去回数・clean 終端をすべて検査、943 assertion 緑）。
構成は「取り除かれる点の集合 $[1,n-1]$ を長さ $\le p-1$ のブロックに分割し、
ブロック $[a,b]$ ごとに $b+1$ まで置いて $b$ から $a$ へ降順に外す」。
Lean では `List` の連結として定義し、`Step` を各要素について機械的に確認する形になる。

### 3.2 下界 — 4 つの補題

**すべて Python 側で最適スケジュール上に実測検証済み**
（`test_exp03_proof.py::test_structural_lemmas`、$n\le14$, $p\le7$）。

```lean
/-- L1 剛性: 2n-1 手なら各点はちょうど 1 回 put され、1..n-1 はちょうど 1 回外される。 -/
lemma rigid (h : 手数 = 2*n - 1) :
    (∀ v, putCount v = 1) ∧ (∀ v < n-1, removeCount v = 1) ∧ removeCount (n-1) = 0
```
証明: 下界 $n + (n-1)$ は「各点は少なくとも 1 回置かれ、目標点以外は少なくとも 1 回外れる」
から出る。等号なので各カウントは 1 に固定される。

```lean
/-- L2 順序: put は 1,2,…,n の順に起きる。 -/
lemma puts_ordered : ∀ i < n, π i < π (i+1)
```
証明: `put (i+1)` は `ready` より $i$ がペブル済みを要求し、$i$ は 1 回しか置かれないので
$\pi(i) < \pi(i+1)$。

```lean
/-- L3 消去数 = τ の上昇数。 -/
lemma erasures_eq_ascents :
    消去回数 = (Finset.filter (fun i => τ (i-1) < τ i) (Finset.Icc 2 (n-1))).card
```
証明: $i\ge2$ の取り除きが可逆 $\iff$ $i-1$ がその時点でペブル済み $\iff$ $\tau(i)<\tau(i-1)$
（$i-1$ は 1 回だけ置かれ 1 回だけ外れるので、ペブル済みの区間は $(\pi(i-1),\tau(i-1))$ で、
$\pi(i-1)<\pi(i)<\tau(i)$ は常に成立）。$i=1$ は源 0 のおかげで常に可逆。

```lean
/-- L4 連長: τ の極大下降連の長さは p-1 以下。**ここが証明の核**。 -/
lemma run_le (B : 極大下降連 [a,b]) : b - a + 1 ≤ p - 1
```
証明: 連 $[a,b]$ 内では $\tau$ が減少するので、連の中で**最初に外れるのは $b$**。
時刻 $\tau(b)$ の直前には
- $a,\dots,b$ が全てペブル済み（$\pi(i)<\pi(b)<\tau(b)$ かつ $\tau(i)>\tau(b)$）、
- さらに **$b+1$ もペブル済み**。
  - $b<n-1$ のとき: `put (b+1)` は $b$ のペブル済みを要求するので $\pi(b+1)<\tau(b)$。
    かつ $b$ が連の終端なので上昇があり $\tau(b+1)>\tau(b)$。
  - $b=n-1$ のとき: `put n` は $n-1$ のペブル済みを要求するので $\pi(n)<\tau(n-1)$、
    かつ $n$ は外れない。
よって同時ペブル数 $\ge (b-a+1)+1$。ピーク制約より $b-a+1 \le p-1$。∎

```lean
/-- 結論。 -/
theorem esat_ge (n p : ℕ) (hp : 2 ≤ p) (h : mstar n p e = some (2*n-1)) :
    ⌈(n-1)/(p-1)⌉ - 1 ≤ e
```
証明: L1–L3 で 消去数 = 連数 $-1$。L4 と鳩の巣で 連数 $\ge \lceil (n-1)/(p-1)\rceil$。∎

### 3.3 Lean 化の難所の見積り

| 部分 | 難易度 | 備考 |
|---|---|---|
| ゲームの意味論（`Step` と手数付き閉包） | **中** | ここが分量の大半。`Finset.card` の扱いが煩雑 |
| L1 剛性 | 中 | 「各点が少なくとも1回」の帰納が要る |
| L2 順序 | 易 | |
| L3 消去数 = 上昇数 | 易〜中 | 「1 回だけ置かれ1回だけ外れる」から区間が一意に決まる |
| **L4 連長** | **易** | 上の証明はそのまま形式化できる。時刻の比較だけ |
| 鳩の巣 | 易 | `Nat.ceil_div` 系の補題 |
| 上界の構成 | 中 | `List` 構成と `Step` の逐次確認。`decide` で潰せる部分が多い |

**L4 が易しいのが重要**: 直感的に一番難しそうな部分が、実は時刻の不等式 4 本で終わる。

## 4. L2（表の全数検査）

`gen_janus` の `Hard18.lean` の `mstar_table` / `pmin_table` と同じ形で:

```lean
def mstarTable : List (ℕ × ℕ × ℕ × ℕ) :=  -- (n, p, e, M*)
  [(16,5,0,71), (16,5,1,45), (16,5,2,37), (16,5,3,31), ...]

theorem mstarTable_correct : ∀ r ∈ mstarTable, mstarBFS r.1 r.2.1 r.2.2.1 = r.2.2.2 := by
  native_decide
```

生成元は `data/exp03_surface_ops.csv`。**`native_decide` は信頼境界を広げるので、
manifest に「L1 は無条件、L2 は `native_decide` 依存」と明記すること**
（`docs/00_overview.md` C4 / `CLAUDE.md` 証明・計算の方針）。

## 5. 定理 B1 の Lean 化（余力があれば）

$\mathrm{reach}(p,e) \ge (e+2)2^{p-2}$ は `scripts/exp03_reach.py` の `bennett` の再帰と
`construction` をそのまま Lean の再帰関数にすれば、帰納法で
「ピーク $p$・消去 $e$ 回・終端 clean」が示せる。
Python 側は $p\le8, e\le6$ で機械検証済み（`--verify-construction`、不合格 0 件）。
**逆向き（等号・予想 B2）は未証明なので Lean に持ち込まない。**
