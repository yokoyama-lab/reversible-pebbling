#!/usr/bin/env bash
# h=5・p=8 の最小手数。SAT 側（上から降ろす）は安いので先に橋頭堡を作り、
# 高い k の UNSAT（高価）は境界の近くだけで踏む。出力 sat_h5.log
set -u
out=sat_h5.log
: > "$out"
for k in 600 500 450 430 410 400 390 380 375 370 360 350; do
  printf "k=%-4s: " "$k" >> "$out"
  python3 sat_treeroot.py --h 5 --p 8 --k "$k" --timeout 2400 2>&1 | tail -1 >> "$out"
done
echo DONE >> "$out"
