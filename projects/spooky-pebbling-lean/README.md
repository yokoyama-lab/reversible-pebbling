# spooky-pebbling-lean

鎖（線グラフ）上の **spooky pebble game** の厳密値に関する結果を Lean 4 で形式化する。

紙の証明と数値実験の正本は別リポジトリ（`notes/spooky-pebbling`）にあり、ここは
**そのうち機械証明まで上げたもの**を置く場所である。何が Lean で証明済みで、何がまだ
紙のままなのかを混同しないよう、下の「層」の表を常に最新にすること。

## 定義の出典

| もの | 出典 |
|---|---|
| spooky pebble game の遷移規則 | Quist–Laarman, *Trade-offs between classical and quantum space using spooky pebbling*, LMCS 21:4 (2025), arXiv:2401.10579, **Definition 2.2** |
| $T_P$ / $T_{UP}$ / $T_{UG}$ の名前と役割 | Kornerup–Sadun–Soloveichik, *Tight Bounds on the Spooky Pebble Game*, Quantum 9:1636 (2025), arXiv:2110.08973v3, §3–4 |

頂点は `0, …, n-1`、辺は `i → i+1`。配置は `ℕ → Cell`（`Cell = empty | pebble | ghost`）で、
鎖の長さ `n` は述語の側に持たせている。`ghost` だけが前提条件を持たない（測定）。

## 層（何が機械証明されているか）

| 主張 | 層 | 置き場 |
|---|---|---|
| **定理B**: $T_{UG}(n,s)=4n-2s$（$s\le n\le\theta(s)$、$\theta(s)=s(s+1)/2$） | **1（Lean）** | `SpookyPebbling/Theta.lean` |
| **定理C**: $T_{UP}(n,s)=4n-2s-1$（$s\le n\le\theta(s)-1$）と系 $\delta=T_{UG}-T_{UP}=+1$ | **1（Lean）** | `SpookyPebbling/Delta.lean` |
| **定理D**: $T_{UG}(n,s)\ge 6n-s(s+3)$（$s\ge2$・無条件） | **1（Lean）** | `SpookyPebbling/Slope6.lean` |
| **KSS Lemma 4.10**: $T_{UG}(n,s)\le T_{UP}(n,s)+1$ | **1（Lean）** | `SpookyPebbling/UGvsUP.lean` |
| **補題3**: $T_{UG}(n,s)=2n$（$n\le s$）、**補題4**: $T_{UP}(k,s)=2k-1$（$k\le s$） | **1（Lean）** | `SpookyPebbling/Closed.lean` |
| **定理A**: $T_{UG}(n,s)\ge 4n-2s$（$s\ge2$・無条件） | **1（Lean）** | `SpookyPebbling/Slope4.lean` |
| **KSS Cor 4.12**: $T_{UG}(n,s)=\min_k[2k-1+T_{UP}(k,s)+T_{UG}(n-k,s-1)]$ | **1（Lean）** | `SpookyPebbling/Unghost.lean` |
| $T_{UP}(k,s)\ge 2k-1$、$T_{UG}(n,s)\ge 2n$（無条件） | **1（Lean）** | `SpookyPebbling/Small.lean` |
| **$T_{UP}$ 分解が厳密**（$\ge$ と $\le$ の両方向。$s\ge3$） | **1（Lean）** | `Decomp.lean` / `Upper.lean` |
| **$\ge$ 方向**（KSS の交換論法は不要） | **1（Lean）** | `SpookyPebbling/Decomp.lean` |
| **$\le$ 方向**（掃き＋尻尾の持ち上げ＋ゴースト回収） | **1（Lean）** | `Sweep.lean` / `Lift.lean` / `Reghost.lean` / `Upper.lean` |
| **$T_{UG}(n,s) \ne T_{UP}(n,s)$**（パリティ不変量） | **1（Lean）** | `SpookyPebbling/Parity.lean` |
| unpebbling は奇数手・unghosting は偶数手・pebbling は奇数手 | **1（Lean）** | `SpookyPebbling/Parity.lean` |
| **補題G**: 始状態に余分なゴーストが在っても手数は減らない | **1（Lean）** | `SpookyPebbling/Ghost.lean` |
| 段(i): 頭の手は `2k-1` 手以上 | **1（Lean）** | `SpookyPebbling/Count.lean` |
| 頭・尻尾への射影が部分鎖の妥当な手順になること | **1（Lean）** | `SpookyPebbling/Project.lean` |
| **到達可能性**: `s ≥ 2` ならどんな長さの鎖も片付く（`sInf ∅ = 0` を回避） | **1（Lean）** | `SpookyPebbling/Reach.lean` |
| 意味論が `< n` の値にしか依存しない（射影の土台） | **1（Lean）** | `SpookyPebbling/Defs.lean` |
| 傾き 6 の**厳密値**（定理E/F）、$T(n,3)=n^2-n-3$、KSS Cor 4.7 | 2（紙＋機械検査） | `notes/spooky-pebbling`（未移植） |

**$T_{UG}\ne T_{UP}$ は KSS が持っていない。** KSS Thm 4.11 の $\pm1$ は Lemma 4.9/4.10 の
両側不等式から出るもので、$0$ の可能性を排除していない。パリティが排除する。

**分解の $\ge$ 方向は KSS の交換論法を使わない。** KSS Lemma 4.1 は
「すべての最適算法のうち $k$ を最大にするものを取る」WLOG から $P^\bot$ を構成するが、
$k$ を*与えられた 1 本の手順の内側*で

$$s^\dagger := \max_t |P_t|,\quad F := \{t : |P_t| = s^\dagger\},\quad
  u := \max_{t\in F}\ \min\{i : v_i\in P_t\},\quad k := u+1$$

と取れば、必要な「尻尾のペブルは常に $\le s^\dagger-1$」が**定義から**出る。
手順を作り変えないので、最適性の仮定も sweep-first 正規化も要らず、
**任意の妥当な手順について**主張が立つ（`decomp_ge` の仮定は `Run` だけ）。

**⚠ $\le$ 方向で紙の証明が飛ばしていた点（形式化で判明）**: 「$v_{k-1}$ まで掃いて
ペブル 1 個を残す `2k-1` 手」は **`unpebble` では書けない**。`unpebble v_i` は
$v_{i-1}\in P$ を要求するが、掃きでは $v_{i-1}$ を既に外しているからである
（$v_0$ だけは前提が無いので外せる）。手数がちょうど `2k-1` である以上、余分な手を
入れる余地は無い。したがって

> **掃きは `ghost` を使い、$v_0..v_{k-2}$ にゴーストを残す。**

残ったゴーストは頭の手順が回収する: 頭の手順はどのみち各頂点を 1 回は置くので
（`head_places`）、その `pebble` を `unghost` に読み替えればよく、**手数は変わらない**
（`Run_reghost` = `Ghost.lean` の補題G のちょうど逆向き）。この読み替えが要ることは
紙の証明にも `closed2.py` の数値検証にも現れていなかった。変異G（掃きを `unpebble` に
戻す）でビルドが落ちることが、この点が本質であることの機械的な証拠である。

## 検査（テストファースト）

`SpookyPebbling/Tests.lean` は 2 種類を置く。

1. **陽性**: `notes/spooky-pebbling` の BFS（Knill の既知値 5 点と独立 2 実装 40 点で
   校正済み）が返した**最適手順そのもの**を転記し、`by decide` で妥当性を検査する。
   同時に `T… ≤ 値` の上界が得られる（$T_{UP}(n,2)=n^2+n-3$、$T_{UG}(n,2)=n^2+n-4$、
   $T_P(n,3)=n^2-n-3$、$k\le s$ で $T_{UP}=2k-1$、$n\le s$ で $T_{UG}=2n$ の各点）
2. **陰性（変異注入）**: 前提条件・上限・終状態・範囲を 1 つずつ壊した手順が
   **`Run` にならない**ことを `by decide` で検査する。陽性だけでは
   「何でも `Run` になる」定義でも通ってしまうため

**定義が正しいことは証明できない。**できるのは、独立に得た値と突き合わせて
「間違っていたら落ちる」ようにしておくことだけ。

## ビルド

```sh
lake build SpookyPebbling
```

Lean `v4.31.0` ＋ mathlib `v4.31.0`。`sorry` は入れない方針（入れる場合は本 README の
層の表に必ず書く）。緑が本物かは変異注入で確かめること（`lake build` の沈黙は
成功と OOM を区別しない）。

## 検査ゲート（2026-08-14 実施）

| 点 | 結果 |
|---|---|
| ビルド | `lake build SpookyPebbling` rc=0 |
| 成果物の実在 | olean 18 本を確認 |
| `sorry` / `native_decide` / 追加 `axiom` | **0 件**（18 ファイルすべて） |
| 公理検査 | `decomp_ge` を含む主要定理すべて `[propext, Classical.choice, Quot.sound]` のみ（`sorryAx` 無し） |
| 変異A（偽の補題 `probe : False`） | **検出**（ビルドが落ちる） |
| 変異B（`ghost` に前提条件を付ける） | **検出**。うち `Tests.lean` だけで 14 か所（`by decide` が定義の変異を捕まえる） |
| 変異C（$\ge$ 方向の `2k-1` を `2k` に強める） | **検出** |
| 変異D（尻尾の上限を `s†-1` でなく `s` にする） | **検出**（`k` の取り方が効いている証拠） |
| 変異E（構成の手数を `2j+1` でなく `2j` と主張） | **検出** |
| 変異F（`s ≥ 3` を `s ≥ 2` に緩める） | **検出**（掃きの 3 個が入らなくなる） |
| 変異G（掃きの `ghost` を `unpebble` にする＝紙の証明どおりの書き方） | **検出**（ゴーストが本質である証拠） |
| 変異H（到達可能性の上限を 2 でなく 1 と主張） | **検出** |
| 変異I（到達可能性の構成から最初の `ghost v_{n-1}` を消す） | **検出**（枠を空けないと掃きに 3 個要る） |
| 変異J（Cor 4.12 の `2k-1` を `2k` に強める） | **検出** |
| 変異K（Cor 4.12 の $\le$ 方向を `s ≥ 1` に緩める） | **検出**（掃きに 2 個要る） |
| 変異L（定理A の傾きを 4 でなく 5 にする） | **検出** |
| 変異M（`T_UP` の下界を `2k-1` でなく `2k` にする） | **検出** |
| 変異N（傾き 4 の領域を $\theta(s)+1$ まで広げる） | **検出**（真の値は 2 大きい） |
| 変異O（定理B の傾きを 4 でなく 3 にする） | **検出** |
| 変異P（Lemma 4.10 の `+1` を落として `T_UG ≤ T_UP` にする） | **検出**（`unpebble` 枝で `unghost` を挿む分が入らない） |
| 変異Q（定理D を $s(s+2)$ に強める） | **検出** |
| 変異R（定理C の範囲に $n=\theta(s)$ を含める） | **検出**（$\delta$ が反転する点そのもの） |
| 変異S（$T_{UP}\ge 4n-2s-1$ の `-1` を落とす） | **検出** |
| **定理B と BFS の突き合わせ** | `TUG 3 2 = 8`・`TUG 3 3 = 6`・`TUG 5 3 = 14` が**転記した最適手順の長さと一致**（片方は定理・片方は全数探索） |
| **定理C と BFS の突き合わせ** | `TUP 2 2 = 3`・`TUP 3 3 = 5`・`TUP 5 3 = 13` が一致。`(5,3)` は $n=\theta(s)-1$＝**範囲の右端そのもの** |
| **$\delta=+1$ と BFS の突き合わせ** | `TUG 3 3 = TUP 3 3 + 1`・`TUG 5 3 = TUP 5 3 + 1` が転記した手順の長さでも成立 |
| **定理D の緊密性** | `(n,s)=(3,2)` で $6n-s(s+3)=8$ が BFS の最適手数 8 と**一致（等号）** |
| 主定理の非空虚性 | `Tests.lean` で具体的な `Run` に `decomp_ge` / `decomp_le_run` を適用して結論を得ている |

再現:

```sh
lake build SpookyPebbling                       # rc=0
grep -cE '\bsorry\b|\bnative_decide\b|^axiom ' SpookyPebbling/*.lean   # すべて 0
echo 'import SpookyPebbling
#print axioms Spooky.TUG_ne_TUP' > /tmp/ax.lean && lake env lean /tmp/ax.lean
```

## ファイル

| ファイル | 内容 |
|---|---|
| `Defs.lean` | 遷移規則（Quist–Laarman Def 2.2 の逐語）、`Run`、`TP`/`TUP`/`TUG`、`< n` 依存性 |
| `Parity.lean` | パリティ不変量 → `TUG_ne_TUP` |
| `Ghost.lean` | 補題G（余分なゴーストは損にならない） |
| `Project.lean` | 軌跡・`valid`/上限の分離・添字ずらし・頭/尻尾への射影 |
| `Count.lean` | 段(i)（`2k-1` の数え上げ） |
| `Split.lean` | ペブル数の分割・最下位ペブル・最大元の存在 |
| `Decomp.lean` | `s†≥2`、尻尾の上限、**`decomp_ge` / `TUP_ge_decomp`**（$\ge$ 方向） |
| `Lift.lean` | 持ち上げ（射影の逆）・連結・`valid_mono`・`traj_above` |
| `Sweep.lean` | 掃き `sweep k`（`2k-1` 手、ゴーストを残す）とその仕様 |
| `Reghost.lean` | `head_places` と再ゴースト `Run_reghost`（補題G の逆向き） |
| `Reach.lean` | 到達可能性（上限 2 の構成と上限の単調性） |
| `Upper.lean` | **`decomp_le_run_gen` / `decomp_le` / `decomp_exact`**（$\le$ 方向と等号） |
| `Unghost.lean` | **KSS Cor 4.12**（`decomp_ug_ge` / `decomp_ug_le` / `decomp_ug_exact`） |
| `Small.lean` | 数え上げの下界（`T_UP ≥ 2k-1`・`T_UG ≥ 2n`） |
| `Slope4.lean` | **定理A**（`T_UG ≥ 4n-2s`。Cor 4.12 の望遠鏡） |
| `Closed.lean` | 補題3・補題4（`n ≤ s` / `k ≤ s` での厳密値。上界＝構成） |
| `Theta.lean` | `θ(s)=s(s+1)/2` と **定理B**（傾き 4 の領域の厳密値） |
| `UGvsUP.lean` | **KSS Lemma 4.10**（`T_UG ≤ T_UP+1`。終端の 1 マスだけの外科手術） |
| `Slope6.lean` | **定理D**（`T_UG ≥ 6n-s(s+3)`。望遠鏡をもう一段） |
| `Delta.lean` | **定理C**（`T_UP = 4n-2s-1` と `δ = +1`） |
| `Tests.lean` | 陽性 13 点・陰性 6 点・両方向の非空虚性・定理B/C/D と BFS の突き合わせ |

## 未移植（次にやること）

1. **KSS Cor 4.7** — `T_P` 版。$\theta$ には**不要**で、$T(n,3)=n^2-n-3$ に要る。
   頭が `T_{UP}(k,s-1)`（上限が 1 小さい）なので、そこだけ別扱いが要る
2. **傾き 6 の厳密値**（定理E/F）と $T(n,3)=n^2-n-3$。定理D は**下界**だけで、
   上界（Cor 4.12 の構成側で $k$ を選ぶ）はまだ
3. 傾き 8 以降（定理E の $c_m$ が $m\ge4$ で緩む）、鎖以外の一般 DAG
4. ~~到達可能性~~ → **`Reach.lean` で解決**（2026-08-16）。`decomp_le` / `decomp_exact` の
   仮定は無くなった（`3 ≤ s` と `k` の範囲だけ）
