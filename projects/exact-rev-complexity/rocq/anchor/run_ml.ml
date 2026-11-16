(* 抽出された参照実装を動かす。格子は Python と同じ規則で作る。 *)
let build_grid t0 mant =
  let lo = 1 lsl mant and hi = (1 lsl (mant+1)) - 1 in
  let cap = Big_int_Z.power_int_positive_int 2 (t0/2 + 4) in
  let tbl = Hashtbl.create 1000 in
  for b = 0 to t0 - 1 do
    for a = lo to hi do
      let v = Big_int_Z.mult_int_big_int a (Big_int_Z.power_int_positive_int 2 b) in
      if Big_int_Z.le_big_int v cap then Hashtbl.replace tbl (Big_int_Z.string_of_big_int v) v
    done
  done;
  for a = 1 to lo do
    let v = Big_int_Z.big_int_of_int a in
    Hashtbl.replace tbl (Big_int_Z.string_of_big_int v) v
  done;
  let l = Hashtbl.fold (fun _ v acc -> v :: acc) tbl [] in
  List.sort Big_int_Z.compare_big_int l

let () =
  let t0 = int_of_string Sys.argv.(1) and mant = int_of_string Sys.argv.(2) in
  let grid = build_grid t0 mant in
  let n = List.length grid in
  Printf.printf "T0=%d grid=%d (mant %d) [Rocq 抽出・参照実装]\n%!" t0 n mant;
  let t = Sys.time () in
  let row = Anchor_ml.anchor_run grid (t0 - 2) in
  let tgt = Big_int_Z.power_int_positive_int 2 (t0 - 2) in
  let ga = Array.of_list grid and ra = Array.of_list row in
  let vstar = ref None in
  Array.iteri (fun i x -> if !vstar = None && Big_int_Z.ge_big_int x tgt then vstar := Some ga.(i)) ra;
  (match !vstar with
   | Some v -> Printf.printf "  v*=%s  (%.2fs)\n" (Big_int_Z.string_of_big_int v) (Sys.time () -. t)
   | None -> Printf.printf "  v* 無し (%.2fs)\n" (Sys.time () -. t))
