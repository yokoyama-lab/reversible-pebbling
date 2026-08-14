# アンカー DP — Rocq で証明し、OCaml へ extraction して回す

**2026-08-13 夜勤。**対象は `~/dev/overleaf/2026_exact_reversible_pebbling` の定理
"certified computable bounds":

```
L(2, w) = 1
L(T, v) = L(T-1, v) + max_{0<w<v} min( L(T-1, v-w), L(T, w) )
L(T0, v*) >= 2^(T0-2)  ならば  c <= 2 * v*^{1/(T0-2)}
```

---

## ⭐ 出発点だった問い: 「メモリが大きいのでファイルに落として圧縮できないか」

**答え: 圧縮は要らない。狙う場所が違った。**

元の `scripts/m5_exact_anchor.py` は既に **2 行しか持っていない**（`Lp = L[:]`）ので、
「t ごとにファイルへ落とす」案は効かない。**実際に食っていたのは索引表 `rd_umap`**
（`rd(v - grid[j])` を全 (i,j) について前計算したもの。$O(n^2)$）。

**単調性を使えば索引表ごと消せる**:

* `L(T-1, v-w)` は $w$ について**非増加**
* `L(T, w)` は $w$ について**非減少**
* その `min` は**単峰** ⟹ **最大は交差点にある** ⟹ 全走査でなく**二分探索**でよい
* 交差点しか見ないので `rd` はその場で二分探索すれば済み、**表が不要**

### 実測（Python 版・同じ答えを出す）

| T0 | 元（`rd_umap` あり） | 二分探索版 | 削減 |
|---|---|---|---|
| 100 | 60 MB / 9.5 s | 12 MB / 0.7 s | 5.0× / 13.6× |
| 200 | 210 MB / 62.5 s | 13 MB / 3.2 s | 16.2× / 19.5× |
| **300** | **458 MB / 302 s** | **13 MB / 13.3 s** | **メモリ 35×・時間 23×** |

**メモリがほぼ定数（12–13MB）になった。**

---

## 構成

| ファイル | 役割 |
|---|---|
| `AnchorDP.v` | **リスト版。数学的性質を証明する**（公理ゼロ） |
| `AnchorArr.v` | **配列版（PArray）。抽出して実用速度で回す** |
| `shim/uint63.ml`, `shim/parray.ml` | 抽出コードが要求する **12 関数だけ**の最小実装 |
| `arrbuild/` | 配列版のビルド一式 |
| `../../rust/anchor/` | Rust 実装（最速。切り下げモードつき） |
| `../../../overleaf/.../scripts/m5_exact_anchor_fast.py` | Python の二分探索版 |

### 証明されていること（`AnchorDP.v`・**公理ゼロ**）

`Print Assumptions` が **`Closed under the global context`**（`propext` すら使わない）。

* `best_scan_ge` / `best_scan_nonneg` — 内側の max は初期値以上
* `step_aux_ge` — **各ステップは値を減らさない**（$L(T,v) \ge L(T-1,v)$）
* `step_aux_length` / `step_row_length` — 長さの保存

---

## ⚠ 実測でわかった罠（3 件）

### ① 「OCaml だから速い」は成り立たない。**データ構造で決まる**

| T0=60 | 時間 |
|---|---|
| Rocq 抽出（**リスト**版 OCaml） | **131.67 s** |
| Python（二分探索） | 0.43 s |
| Rocq 抽出（**配列**版 OCaml） | **0.18 s** |
| Rust | **0.11 s** |

**リスト版は Python より 500 倍遅い**（`nth` が $O(n)$）。
**配列にして初めて Python の 2 倍速くなった。**

### ② PArray の extraction は使える。**最初に諦めたのは誤り**

失敗の原因は「配列が使えない」ではなく、Rocq 本体の `uint63.ml` が
**float 変換の C スタブ**（`rocq_uint63_to_float`）を要求すること。
抽出コードが実際に呼ぶのは **12 関数だけ**なので、自前の shim で足りる:

```
Parray.{make,get,set,t}   Uint63.{equal,l_and,l_or,l_sl,l_sr,of_int,sub,div,t}
```

`parray.ml` は Baker の差分リスト法で**きちんと永続**にした（線形利用なので
実際には最新版しか触らないが、健全性のため）。

⚠ **抽出される型別名が壊れる**（`Big_int_Z.big_int 'a Parray.t`）。
`'a Parray.t` → `Parray.t` の機械的置換で直る。`.mli` は使わない。

### ③ `Z.of_nat` を実行時に呼ぶと二次になる

`nat` を `int` に抽出すると、`Z.of_nat` はマッチャが 1 ずつ減らすので**線形時間**。
DP の内側で呼ぶと全体が二次になる（実測: n=1000 で 0.043s → n=10000 で 4.3s）。
**燃料は引数として OCaml 側から渡す**（Rocq 内に大きな `nat` リテラルを書くと
`of_num_uint` で桁ごとに構築されて同じ問題が起きる）。

---

## 一致の確認

**4 実装（Python / Rocq リスト / Rocq 配列 / Rust）がすべて同じ $v^*$ を出す**ことを
T0 = 20, 24, 28, 40, 60, 100, 160, 200 で確認済み。

## 切り下げモード（Rust `--approx <bits>`）

`max` `min` `+` はすべて単調なので、**L を切り下げても表は真の L の下界**であり、
証明書としては a fortiori 妥当（幾何格子で $v$ を切り下げるのと同じ理屈）。
実測では 128 ビットまで落としても $v^*$ は変わらなかった（T0 ≤ 500）。

## 再現

```bash
# Rocq（証明つき・リスト版）
cd rocq/anchor && coqc AnchorDP.v

# Rocq（配列版）→ OCaml
coqc AnchorArr.v && cd arrbuild
sed -i "s/ 'a Parray\.t/ Parray.t/g" anchor_arr_ml.ml
ocamlfind ocamlopt -package zarith -linkpkg uint63.ml parray.ml anchor_arr_ml.ml run_arr.ml -o run_arr
./run_arr 200 5

# Rust（最速）
cd ../../../rust/anchor && cargo build --release --offline
./target/release/anchor 600 5 --approx 192
```
