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
| **$T_{UG}(n,s) \ne T_{UP}(n,s)$**（パリティ不変量） | **1（Lean）** | `SpookyPebbling/Parity.lean` |
| unpebbling は奇数手・unghosting は偶数手・pebbling は奇数手 | **1（Lean）** | `SpookyPebbling/Parity.lean` |
| **補題G**: 始状態に余分なゴーストが在っても手数は減らない | **1（Lean）** | `SpookyPebbling/Ghost.lean` |
| 意味論が `< n` の値にしか依存しない（射影の土台） | **1（Lean）** | `SpookyPebbling/Defs.lean` |
| $T_{UP}$ 分解の $\ge$ 方向、$\theta(s)=s(s+1)/2$、傾き 4/6 の厳密値、$T(n,3)=n^2-n-3$ | 2（紙＋機械検査） | `notes/spooky-pebbling`（未移植） |

**$T_{UG}\ne T_{UP}$ は KSS が持っていない。** KSS Thm 4.11 の $\pm1$ は Lemma 4.9/4.10 の
両側不等式から出るもので、$0$ の可能性を排除していない。パリティが排除する。

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
| 成果物の実在 | `Defs.olean` `Parity.olean` `Ghost.olean` `Tests.olean` の 4 本を確認 |
| `sorry` / `native_decide` / 追加 `axiom` | **0 件**（4 ファイルすべて） |
| 公理検査 | 主要 8 定理すべて `[propext, Classical.choice, Quot.sound]` のみ（`sorryAx` 無し） |
| 変異A（偽の補題 `probe : False`） | **検出**（ビルドが落ちる） |
| 変異B（`ghost` に前提条件を付ける） | **検出**。うち `Tests.lean` だけで 14 か所（`by decide` が定義の変異を捕まえる） |

再現:

```sh
lake build SpookyPebbling                       # rc=0
grep -cE '\bsorry\b|\bnative_decide\b|^axiom ' SpookyPebbling/*.lean   # すべて 0
echo 'import SpookyPebbling
#print axioms Spooky.TUG_ne_TUP' > /tmp/ax.lean && lake env lean /tmp/ax.lean
```

## 未移植（次にやること）

1. **$T_{UP}$ 分解の $\ge$ 方向**（本丸）。紙の証明は
   $s^\dagger=\max_t|P_t|$、$F=\{t:|P_t|=s^\dagger\}$、$k=\max_{t\in F}\min P_t$ と取る。
   Lean 化には (a) 手順の軌跡、(b) 頭・尻尾への射影（`List.filter` と添字のずらし）、
   (c) 「各 $v_i$ が 1 回は置かれ 1 回は外される」の数え上げ、が要る。
   補題G（済）はその段(2)にあたる
2. 上界側の構成（$\le$ 方向）
3. $\theta(s)=s(s+1)/2$
