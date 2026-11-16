let () =
  let t = Sys.time () in
  let r = Spike2_ml.fill_sum (Uint63.of_int 1_000_000) in
  Printf.printf "fill_sum(1e6) = %s  (%.2fs)\n" (Big_int_Z.string_of_big_int r) (Sys.time () -. t)
