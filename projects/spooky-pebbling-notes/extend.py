from spooky import chain, min_time
print(" n | T(n,3) | n^2-n-3 | 一致 | T(n,4) | T(n,5)")
for n in range(4, 16):
    t3 = min_time(chain(n), 3)
    t4 = min_time(chain(n), 4)
    t5 = min_time(chain(n), 5)
    f = n*n - n - 3
    print(f"{n:2d} | {str(t3):>6} | {f:>7} | {'○' if t3==f else '×'} "
          f"| {str(t4):>6} | {str(t5):>6}", flush=True)
