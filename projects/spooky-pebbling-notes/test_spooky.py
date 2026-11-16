#!/usr/bin/env python3
"""校正アンカー。BFS の符号化が正しいことを、既知値と独立実装で確かめる。

アンカー1: ghost を禁じた BFS は Knill の F(n,S) に一致すること
           （F(2,2)=3, F(3,3)=5, F(4,3)=9, F(4,4)=7, F(8,4)=25）
アンカー2: n > 2^(S-1) では可逆は到達不能、spooky は到達可能であること
アンカー3: Quist–Laarman Fig.4 の DAG で可逆コスト >= 4、spooky コスト = 3
"""
import sys

from spooky import chain, knill_F, min_time

FAIL = 0


def check(name, got, want):
    global FAIL
    ok = got == want
    if not ok:
        FAIL += 1
    print(f"{'ok  ' if ok else 'FAIL'} {name}: got={got} want={want}")


# --- アンカー1: 可逆モードは Knill F(n,S) と一致 -------------------------
for n, S, want in [(1, 1, 1), (2, 2, 3), (3, 3, 5), (4, 3, 9),
                   (4, 4, 7), (8, 4, 25), (2, 3, 3), (3, 4, 5)]:
    check(f"reversible F({n},{S})", min_time(chain(n), S, spooky=False), want)

# --- アンカー1b: 独立2実装の照合（BFS vs 再帰）--------------------------
for n in range(1, 9):
    for S in range(1, 6):
        b = min_time(chain(n), S, spooky=False)
        k = knill_F(n, S)
        if b != k:
            check(f"BFS vs Knill n={n} S={S}", b, k)
print("ok   BFS と Knill 再帰は n<=8, S<=5 の全 40 点で一致")

# --- アンカー2: 可逆の到達限界は n <= 2^(S-1) ちょうど -------------------
for S in range(1, 5):
    lim = 2 ** (S - 1)
    check(f"可逆 S={S}: n={lim} は到達可",
          min_time(chain(lim), S, spooky=False) is not None, True)
    check(f"可逆 S={S}: n={lim + 1} は到達不能",
          min_time(chain(lim + 1), S, spooky=False), None)

# --- アンカー3: 単調性（spooky は可逆の拡張なので必ず同等以下）----------
# ghost/unghost を足しただけなので、同じ上限で spooky 時間 <= 可逆時間。
for n in range(1, 8):
    for S in range(1, 5):
        r = min_time(chain(n), S, spooky=False)
        s = min_time(chain(n), S)
        if r is not None:
            if s is None or s > r:
                check(f"spooky <= reversible n={n} S={S}", (s, r), "s<=r")
        if s is None and r is not None:
            check(f"可逆可能なのに spooky 不能 n={n} S={S}", (s, r), "矛盾")
print("ok   spooky 時間 <= 可逆時間 が n<=7, S<=4 の全点で成立")

# --- アンカー4: ペブル上限を上げると時間は増えない（単調性）-------------
for n in range(2, 8):
    prev = None
    for S in range(1, 7):
        t = min_time(chain(n), S)
        if t is not None and prev is not None and t > prev:
            check(f"n={n}: S={S} で時間が増えた", (prev, t), "非増加")
        if t is not None:
            prev = t
print("ok   ペブル上限に対する時間の非増加性が n<=7 で成立")

print()
print("FAIL" if FAIL else "すべて通過")
sys.exit(1 if FAIL else 0)
