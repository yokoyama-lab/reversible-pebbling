(* Rocq(配列版)から抽出した DP を動かす *)
let build_grid t0 mant =
  let lo = 1 lsl mant and hi = (1 lsl (mant+1)) - 1 in
  let cap = Big_int_Z.power_int_positive_int 2 (t0/2 + 4) in
  let tbl = Hashtbl.create 4096 in
  for b = 0 to t0 - 1 do
    for a = lo to hi do
      let v = Big_int_Z.mult_int_big_int a (Big_int_Z.power_int_positive_int 2 b) in
      if Big_int_Z.le_big_int v cap then Hashtbl.replace tbl (Big_int_Z.string_of_big_int v) v
    done
  done;
  for a = 1 to lo do
    let v = Big_int_Z.big_int_of_int a in
    Hashtbl.replace tbl (Big_int_Z.string_of_big_int v) v done;
  let l = Hashtbl.fold (fun _ v acc -> v :: acc) tbl [] in
  Array.of_list (List.sort Big_int_Z.compare_big_int l)

let () =
  let t0 = int_of_string Sys.argv.(1) and mant = int_of_string Sys.argv.(2) in
  let ga = build_grid t0 mant in
  let n = Array.length ga in
  Printf.printf "T0=%d grid=%d [Rocq配列版]\n%!" t0 n;
  let g = Parray.make n Big_int_Z.zero_big_int in
  let g = ref g in
  Array.iteri (fun i v -> g := Parray.set !g i v) ga;
  let t = Sys.time () in
  let row = Anchor_arr_ml.anchor_run (10*n+100) !g (t0 - 2) in
  let tgt = Big_int_Z.power_int_positive_int 2 (t0 - 2) in
  let rec find i = if i >= n then None
    else if Big_int_Z.ge_big_int (Parray.get row i) tgt then Some ga.(i) else find (i+1) in
  (match find 0 with
   | Some v -> Printf.printf "  v*=%s  (%.3fs)\n" (Big_int_Z.string_of_big_int v) (Sys.time () -. t)
   | None -> Printf.printf "  v* 無し (%.3fs)\n" (Sys.time () -. t))
