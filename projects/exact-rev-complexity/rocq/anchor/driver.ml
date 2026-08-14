let () =
  let t = Sys.time () in
  let r = Spike_ml.demo 5_000_000 in
  Printf.printf "demo(5e6) = %s  (%.2fs)\n" (Big_int_Z.string_of_big_int r) (Sys.time () -. t)
