#!/usr/bin/env bash
# d=4,5 の全葉訪問（--order-lr。B4 が 6 点で成立したので採用）。出力 d4_d5.log
set -u
out=d4_d5.log
: > "$out"
for p in 3 4 5 6; do
  printf "d=4 p=%s 可逆(e=0)  : " "$p" >> "$out"
  python3 abandon.py tree 4 --p "$p" --e 0 --order-lr 2>&1 | tail -1 >> "$out"
done
for p in 3 4 5 6; do
  printf "d=4 p=%s 古典        : " "$p" >> "$out"
  python3 abandon.py tree 4 --p "$p" --e -1 --erase-price 0 --order-lr 2>&1 | tail -1 >> "$out"
done
for p in 4 5 6 7; do
  printf "d=5 p=%s 可逆(e=0)  : " "$p" >> "$out"
  python3 abandon.py tree 5 --p "$p" --e 0 --order-lr 2>&1 | tail -1 >> "$out"
done
echo DONE >> "$out"
