#!/usr/bin/env python3
"""鎖に対する spooky pebble game の厳密表。"""
import sys

from spooky import chain, min_time

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 11
PMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6

print("表A: 最小ペブル数（＝最小量子空間）")
print(" n | spooky | 可逆 | 可逆の限界 2^(p-1)")
for n in range(1, NMAX + 1):
    sp = next((p for p in range(1, PMAX + 2)
               if min_time(chain(n), p) is not None), None)
    rv = next((p for p in range(1, PMAX + 2)
               if min_time(chain(n), p, spooky=False) is not None), None)
    print(f"{n:2d} | {str(sp):>6} | {str(rv):>4} | {2 ** (rv - 1) if rv else '-'}")

print("\n表B: 最短時間 T(n,p)（spooky）／括弧内は可逆")
head = " n \\ p |" + "".join(f"{p:>12}" for p in range(1, PMAX + 1))
print(head)
for n in range(1, NMAX + 1):
    row = f"{n:5d} |"
    for p in range(1, PMAX + 1):
        s = min_time(chain(n), p)
        r = min_time(chain(n), p, spooky=False)
        cell = f"{s if s is not None else '-'}({r if r is not None else '-'})"
        row += f"{cell:>12}"
    print(row)
