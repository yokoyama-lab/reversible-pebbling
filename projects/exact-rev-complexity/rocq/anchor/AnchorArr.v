(**
  アンカー DP の **配列版**（2026-08-13）。

  `AnchorDP.v` はリストで定義したため抽出コードが O(n) 参照になり、
  T0=60 で 131 秒（Python の 500 倍遅い）だった。ここでは Rocq の原始配列
  [PArray] を使い、**抽出した OCaml がそのまま実用速度で動く**ようにする。

  ⚠ 抽出に必要な OCaml 側の支援は `shim/uint63.ml` と `shim/parray.ml`
     （12 関数だけ）。Rocq 本体の `uint63.ml` は float 変換の C スタブを
     要求するので使わない。

  ⚠ **`Z.of_nat` を実行時に呼ばないこと。** `nat` を `int` に抽出すると
     `Z.of_nat` は線形時間になり、DP 全体が二次になる（2026-08-13 に実測）。
     ループ変数は最初から [int]（Uint63）で回す。

  漸化式:
      L(2, w) = 1
      L(T, v) = L(T-1, v) + max_{0<w<v} min( L(T-1, v-w), L(T, w) )
*)

From Stdlib Require Import ZArith Uint63 PArray List Lia.
From Stdlib Require Import ExtrOcamlZBigInt ExtrOCamlInt63 ExtrOCamlPArray ExtrOcamlBasic.
Import ListNotations.
Open Scope Z_scope.

Local Open Scope uint63_scope.

Definition grid_t := array Z.
Definition row_t := array Z.

(** 番人は「範囲外の添字」で表す（[int] は符号なしなので -1 は使えない）。 *)

(** [rd g v] : [g] の中で [v] 以下の最大要素の添字。無ければ [length g]（＝番人）。 *)
Definition rd (g : grid_t) (v : Z) : int :=
  let n := PArray.length g in
  let fix go (fuel : nat) (lo hi : int) {struct fuel} : int :=
    match fuel with
    | O => lo
    | S f =>
        if (hi - lo <=? 1) then lo
        else
          let mid := (lo + hi) / 2 in
          if (PArray.get g mid <=? v)%Z then go f mid hi else go f lo mid
    end in
  if (n =? 0) then n
  else if (v <? PArray.get g 0)%Z then n
  else go 64%nat 0 n.

(** 候補 [min( Lp[rd(v - g_j)], cur_j )]。番人なら 0。 *)
Definition cand (g : grid_t) (lp cur : row_t) (v : Z) (j : int) : Z :=
  let n := PArray.length g in
  let k := rd g (v - PArray.get g j)%Z in
  if (n <=? k) then 0%Z else Z.min (PArray.get lp k) (PArray.get cur j).

Definition WINDOW : int := 3.

(** 内側の max を**交差点の二分探索**で取る。
    `Lp[rd(v-g_j)]` は j について非増加、`cur[j]` は非減少なので min は単峰。 *)
Definition best (g : grid_t) (lp cur : row_t) (v : Z) (jmax : int) : Z :=
  let n := PArray.length g in
  let fix bs (fuel : nat) (lo hi : int) {struct fuel} : int :=
    match fuel with
    | O => lo
    | S f =>
        if (hi <=? lo) then lo
        else
          let mid := (lo + hi + 1) / 2 in
          let k := rd g (v - PArray.get g mid)%Z in
          let a := if (n <=? k) then 0%Z else PArray.get lp k in
          if (PArray.get cur mid <=? a)%Z then bs f mid hi else bs f lo (mid - 1)
    end in
  let c := bs 64%nat 0 jmax in
  let lo := if (c <? WINDOW) then 0 else c - WINDOW in
  let hi := if (jmax <? c + WINDOW) then jmax else c + WINDOW in
  let fix scan (fuel : nat) (j : int) (acc : Z) {struct fuel} : Z :=
    match fuel with
    | O => acc
    | S f => if (hi <? j) then acc
             else scan f (j + 1) (Z.max acc (cand g lp cur v j))
    end in
  scan 16%nat lo 0%Z.

(** 1 行を左から埋める。 *)
(** 燃料は**呼び出し側から渡す**。Rocq 内で大きな [nat] リテラルを書くと
    抽出コードが実行時に桁ごとに構築して遅くなる（2026-08-13 実測）。 *)
Definition step_row (fuel : nat) (g : grid_t) (lp : row_t) : row_t :=
  let n := PArray.length g in
  let fix go (fuel : nat) (i : int) (cur : row_t) {struct fuel} : row_t :=
    match fuel with
    | O => cur
    | S f =>
        if (n <=? i) then cur
        else
          let v := PArray.get g i in
          let b := if (i =? 0) then 0%Z else best g lp cur v (i - 1) in
          go f (i + 1) (PArray.set cur i (PArray.get lp i + b)%Z)
    end in
  go fuel 0 (PArray.make n 0%Z).

Fixpoint run (fuel : nat) (g : grid_t) (l : row_t) (k : nat) : row_t :=
  match k with
  | O => l
  | S k' => run fuel g (step_row fuel g l) k'
  end.

Definition anchor_run (fuel : nat) (g : grid_t) (steps : nat) : row_t :=
  run fuel g (PArray.make (PArray.length g) 1%Z) steps.

(** ⚠ 数学的な性質は [AnchorDP.v]（リスト版）で証明する。
    配列版の目的は**抽出して実用速度で動かすこと**。
    両者が同じ答えを出すことは実行時に照合する。 *)

Extraction Language OCaml.
Extract Inductive nat => "int" [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "anchor_arr_ml.ml" anchor_run step_row rd.
