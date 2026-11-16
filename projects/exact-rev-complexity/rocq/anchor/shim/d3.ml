let () =
  let n = int_of_string Sys.argv.(1) in
  let t = Sys.time () in
  let r = Spike2_ml.fill_sum n in
  Printf.printf "fill_sum(%d) = %s  (%.3fs)\n" n (Big_int_Z.string_of_big_int r) (Sys.time () -. t)
