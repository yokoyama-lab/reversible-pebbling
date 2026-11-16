(* 抽出コードが要求する分だけの最小実装（2026-08-13）。
   Rocq 本体の uint63.ml は float 変換の C スタブを要求するので使えない。
   ここでは OCaml の native int（63bit）をそのまま使う。 *)
type t = int
let equal (x : t) (y : t) = x = y
let l_and (x : t) (y : t) = x land y
let l_or (x : t) (y : t) = x lor y
let l_sl (x : t) (y : t) = if y >= 63 then 0 else (x lsl y) land max_int
let l_sr (x : t) (y : t) = if y >= 63 then 0 else x lsr y
let of_int (x : int) : t = x
let to_int (x : t) : int = x
let sub (x : t) (y : t) : t = (x - y) land max_int
let add (x : t) (y : t) : t = (x + y) land max_int
let le (x : t) (y : t) = x <= y
let lt (x : t) (y : t) = x < y
let div (x : t) (y : t) : t = if y = 0 then 0 else x / y
let modulo (x : t) (y : t) : t = if y = 0 then x else x mod y
let mul (x : t) (y : t) : t = (x * y) land max_int
let compare (x : t) (y : t) = Stdlib.compare x y
let is_zero (x : t) = x = 0
let one : t = 1
let zero : t = 0
