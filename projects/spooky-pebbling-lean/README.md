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
| **符号反転**: $\delta$ は $n<\theta(s)$ で $+1$、$\theta(s)\le n\le B_4(s)-1$ で $-1$ | **1（Lean）** | `SpookyPebbling/Sign.lean` |
| **$T_{UP}(n,2)=n^2+n-3$**（上限 2 の閉形式） | **1（Lean）** | `SpookyPebbling/Cap2.lean` |
| **$T_{UG}(n,2)=n^2+n-4$** と、$s=2$ では $\delta=-1$ が全ての $n\ge3$ で成立 | **1（Lean）** | `SpookyPebbling/Cap2Exact.lean` |
| **上限 2 では鎖（$n\ge3$）の先端にペブルを置けない**（KSS Cor 4.7 の $\infty$ 条項） | **1（Lean）** | `SpookyPebbling/Cap2Exact.lean` |
| **$T(n,3)=n^2-n-3$**（$n\ge4$） | **1（Lean）** | `SpookyPebbling/Lemma48.lean` |
| **KSS Thm 4.11（上限 3）**: $T_P(n{+}1,3)=T_{UG}(n,2)+1$ | **1（Lean）** | `Bridge.lean` / `Lemma48.lean` |
| **KSS Lemma 3.2**: $T_P(n{+}1,s{+}1)\le T_{UG}(n,s)+1$（全 $s$） | **1（Lean）** | `SpookyPebbling/Bridge.lean` |
| **定理D**: $T_{UG}(n,s)\ge 6n-s(s+3)$（$s\ge2$・無条件） | **1（Lean）** | `SpookyPebbling/Slope6.lean` |
| **定理F**: $T_{UG}(n,s)=6n-s(s+3)$（$\theta(s)\le n\le B_4(s)-1$）と $B_4(s)=B_4(s-1)+\theta(s)-1$ | **1（Lean）** | `SpookyPebbling/Slope6Exact.lean` |
| **定理E**: $T_{UG}(n,s)\ge 2mn-c_m(s)$（任意の傾き $2m$。定理A・定理D を含む） | **1（Lean）** | `SpookyPebbling/SlopeE.lean` |
| **KSS Thm 4.11**: $T_P(n{+}1,s{+}1)=T_{UG}(n,s)+1$（**任意の $s$**） | **1（Lean）** | `Bridge.lean` / `Lemma48Gen.lean` |
| **KSS Lemma 4.5**: 任意の目標配置を作る正準手順（$2M{+}1-|S|$ 手・$|S|{+}1$ ペブル） | **1（Lean）** | `SpookyPebbling/PlaceI.lean` |
| **KSS Lemma 4.9/4.10**: $T_{UG}\le T_{UP}+1$ と $T_{UP}\le T_{UG}+1$、ゆえに差はちょうど 1 | **1（Lean）** | `SpookyPebbling/UGvsUP.lean` |
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
| 傾き 8 以降の**厳密値**（$c_m$ が $m\ge4$ で緩む）、鎖以外の一般 DAG | **3（未解決）** | — |

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
| 変異T（定理F の区間を $B_4(s)$ まで広げる） | **検出**（BFS でも $T_{UG}(9,3)=38\ne36$） |
| 変異U（$B_4$ の漸化から `-1` を落とす） | **検出** |
| 変異V（$T_{UP}\le T_{UG}+1$ の `+1` を落とす） | **検出** |
| 変異W（定理F の左端を $\theta(s)-1$ に広げる） | **検出** |
| 変異X（終端に要る手数を 3→4 に強める） | **検出** |
| 変異Y（$T_{UP}(n,2)$ の値を 1 ずらす） | **検出** |
| 変異Z（上限 2 の構成の手数を $2n$ でなく $2n-1$ と主張） | **検出** |
| 変異AA（$T_{UP}\ge 6n-s(s+3)+1$ の `+1` を `+2` に強める） | **検出**（$\delta=-1$ が緊密である証拠） |
| 変異AB（$\delta$ の符号を逆向きに主張） | **検出** |
| **定理F と BFS の突き合わせ** | `TUG 6 3 = 18`・`TUG 7 3 = 24` が転記した BFS の最適手順の長さと一致。$B_4(3)=9$ は実測どおり（`9,18,32,52,79,114` を `rfl` で照合） |
| **上限 2 の閉形式と BFS** | `TUP 3 2 = 9`・`TUP 4 2 = 17` が転記した最適手順の長さと一致 |
| 変異AC（$T_{UG}(n,2)$ の値を 1 ずらす） | **検出** |
| 変異AD（到達不能性を $n\ge2$ に緩める） | **検出**（$n=2$ では実際に到達できる） |
| 変異AE（不変条件の上限を 2 でなく 3 にする） | **検出**（3 個目が入らないことが本質） |
| **符号反転と BFS** | `n=5=θ(3)-1` で `TUG 5 3 = TUP 5 3 + 1`、`n=6=θ(3)` で `TUP 6 3 = TUG 6 3 + 1`。転記した手順の長さ（14/13 と 19/18）でも同じ向き |
| 変異AF（Lemma 3.2 の `+1` を落とす） | **検出** |
| 変異AG（$T_P(n,3)$ の上界を 1 きつくする） | **検出**（BFS でも $T_P(4,3)=9$） |
| 変異AH（鎖を伸ばすとき上限を増やさない） | **検出**（挿した `pebble v_n` の分が要る） |
| **上限 2 の可否の対比** | 同じ長さ 3 の鎖で、上限 3 なら 5 手の witness（`wP3_3`）が在り、上限 2 では**どんな手順も存在しない**（定理）。`TUG 4 2 = 16` も `wUG4_2` と一致 |
| 変異AI（Lemma 4.8 の `+1` を落とす） | **検出** |
| 変異AJ（$T(n,3)$ の値を 1 ずらす） | **検出** |
| 変異AK（**最後**の手でなく**最初**の手で切る） | **検出**（`Last(v_n)` で切るのが本質）|
| 変異AL（数え上げの置く手を $v_0..v_{n-1}$ に減らす） | **検出**（終端の `place` の 1 手が効く）|
| 変異AM（$c_m$ の漸化式の `+2` を `+1` に） | **検出** |
| 変異AN（底 $c_m(1)$ を 1 小さく） | **検出** |
| 変異AO（傾きを $2m$ でなく $2m+1$ と主張） | **検出** |
| **$T(n,3)$ と BFS** | 定理の値 `TP 4 3 = 9`・`TP 5 3 = 17` が、独立に走らせた BFS の**最適**手数（`wP4_3`・`wP5_3` の長さ）と一致。`TP 6 3 = 27` も BFS と一致 |
| 変異AP（Lemma 4.8 一般版の `+1` を `+2` に強める） | **検出** |
| 変異AQ（正準形の手数を `2M+1` でなく `2M` と主張） | **検出** |
| 変異AR（正準形のペブル上限を `+2` でなく `+1` に） | **検出** |
| 変異AS（数え上げから外す手の寄与を落とす） | **検出** |
| **定理E と定理A・定理D の突き合わせ** | 一般形から $m=2,3$ を取り出すと、**独立に証明した** `TUG_ge_slope4`・`TUG_ge_slope6` とまったく同じ主張になる（`TUG_ge_slope4_of_E` / `TUG_ge_slope6_of_E`）。$c_2(s)=2s$・$c_3(s)=s(s+3)$ も漸化式から導出 |
| **Thm 4.11 の二重証明** | 上限 3 の場合を `Lemma48.lean`（特化版）と `Lemma48Gen.lean`（一般版）で**別々に**証明してある。値も `TP 4 3 = 9`・`TP 5 3 = 17` で BFS と一致 |
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
| `UGvsUP.lean` | **KSS Lemma 4.9/4.10**（`T_UG ≤ T_UP+1` と逆向き。差はちょうど 1） |
| `Slope6.lean` | **定理D**（`T_UG ≥ 6n-s(s+3)`。望遠鏡をもう一段） |
| `Delta.lean` | **定理C**（`T_UP = 4n-2s-1` と `δ = +1`） |
| `Slope6Exact.lean` | **定理F**（傾き 6 の領域の厳密値と折れ目 `B₄(s)`） |
| `Cap2.lean` | **`T_UP(n,2)=n²+n-3`**（終端に 3 手要ることで足りない 2 を取り返す） |
| `Sign.lean` | **δ の符号反転**（`T_UP ≥ 6n-s(s+3)+1` と `δ=-1`） |
| `Cap2Exact.lean` | `T_UG(n,2)=n²+n-4`・`s=2` の `δ=-1`・上限 2 の到達不能性 |
| `Bridge.lean` | **KSS Lemma 3.2**（unghosting → pebbling は 1 手）と `T_P(n,3) ≤ n²-n-3` |
| `Lemma48.lean` | **KSS Lemma 4.8（上限 3→2）**と **`T(n,3) = n²-n-3`** |
| `SlopeE.lean` | **定理E**（任意の傾き `2m`。`c_m(s)` の漸化式と `m=2,3` の閉形式） |
| `PlaceI.lean` | **KSS Lemma 4.5**（任意の目標配置を作る正準手順 `placeUpto`） |
| `Lemma48Gen.lean` | **KSS Lemma 4.8（一般の `s`）**と **Thm 4.11**。`T_P` は `T_UG` で決まる |
| `Tests.lean` | 陽性 13 点・陰性 6 点・両方向の非空虚性・定理B/C/D と BFS の突き合わせ |

## 残っているもの（層3＝未解決）

**紙で証明済みだが未移植（層2）のものは無くなった。** 残るのは未解決問題:

1. **傾き 8 以降の厳密値**。定理E は任意の傾きで**下界**を出すが、$c_m$ は $m\ge4$ で
   緩む（`cc_four_three` で $c_4(3)=38$、実測の折れ目は 34）。$\delta$ の符号反転と
   定理F の主張が $n\le B_4(s)-1$ で止まっているのはこれが理由で、**新しい下界の材料**が要る
2. **鎖以外の一般 DAG**。本リポジトリの `k` の取り方（満室時刻の最下位ペブル）は
   鎖であることをほとんど使っていないので、木への一般化が近い
3. ~~到達可能性~~ → **`Reach.lean` で解決**（2026-08-16）
