(* extraction の実験: PArray（原始配列）と Z（多倍長）が OCaml で実用速度になるか *)
From Coq Require Import ZArith List Uint63 PArray.
From Coq Require Extraction.
Import ListNotations.
Open Scope Z_scope.

(* 配列に対する単純な畳み込み: 累積和 *)
Definition demo (n : nat) : Z :=
  let a := PArray.make 1000%uint63 1 in
  let fix go (k : nat) (acc : Z) : Z :=
    match k with
    | O => acc
    | S k' => go k' (acc + PArray.get a 3%uint63)
    end in
  go n 0.

Extraction Language OCaml.
Extract Inductive nat => "int" [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Require Import ExtrOcamlZBigInt.
Extraction "spike_ml.ml" demo.
