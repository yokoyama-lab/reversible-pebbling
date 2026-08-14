From Stdlib Require Import ZArith Uint63 PArray.
From Stdlib Require Import ExtrOcamlZBigInt ExtrOCamlInt63 ExtrOCamlPArray.
Open Scope Z_scope.

(* 配列を線形に埋めて総和を返す（DP の内側と同じ形） *)
Definition fill_sum (n : int) : Z :=
  let a := PArray.make n 0 in
  let fix go (k : nat) (a : array Z) (acc : Z) : Z :=
    match k with
    | O => acc
    | S k' => let i := (Uint63.of_Z (Z.of_nat k')) in
              let a' := PArray.set a i (Z.of_nat k') in
              go k' a' (acc + PArray.get a' i)
    end in
  go (Z.to_nat (Uint63.to_Z n)) a 0.

Extraction Language OCaml.
Extract Inductive nat => "int" [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extraction "spike2_ml.ml" fill_sum.
