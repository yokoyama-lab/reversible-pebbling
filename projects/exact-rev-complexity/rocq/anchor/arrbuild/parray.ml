(* 永続配列（Baker の差分リスト法）。抽出コードが要求する 4 つだけ。
   ⚠ 永続性が要るのは「古い版を参照しうる」ため。DP は線形に使うので
   実際には最新版しか触らないが、健全性のためきちんと永続にしておく。 *)
type 'a t = 'a data ref
and 'a data =
  | Arr of 'a array * 'a          (* 実体 + 既定値 *)
  | Diff of int * 'a * 'a t       (* i 番目が v だった版へのリンク *)

let make (n : Uint63.t) (d : 'a) : 'a t =
  let n = if n < 0 then 0 else if n > 4_000_000_000 then 4_000_000_000 else n in
  ref (Arr (Array.make n d, d))

(* 最新版へ「巻き戻す」 *)
let rec reroot (t : 'a t) : 'a array * 'a =
  match !t with
  | Arr (a, d) -> (a, d)
  | Diff (i, v, t') ->
      let (a, d) = reroot t' in
      let old = if i >= 0 && i < Array.length a then a.(i) else d in
      if i >= 0 && i < Array.length a then a.(i) <- v;
      t' := Diff (i, old, t);
      t := Arr (a, d);
      (a, d)

let get (t : 'a t) (i : Uint63.t) : 'a =
  let (a, d) = reroot t in
  if i >= 0 && i < Array.length a then a.(i) else d

let set (t : 'a t) (i : Uint63.t) (v : 'a) : 'a t =
  let (a, d) = reroot t in
  if i < 0 || i >= Array.length a then t
  else begin
    let old = a.(i) in
    a.(i) <- v;
    let res = ref (Arr (a, d)) in
    t := Diff (i, old, res);
    res
  end

let default (t : 'a t) : 'a = let (_, d) = reroot t in d
let length (t : 'a t) : Uint63.t = let (a, _) = reroot t in Array.length a
let copy (t : 'a t) : 'a t = let (a, d) = reroot t in ref (Arr (Array.copy a, d))
