#!/usr/bin/env bash
# 値段（hold）を動かしたときの最適配分。出力は price_sweep.log。
set -u
out=price_sweep.log
: > "$out"
for d in 2 3; do
  for h in 0 1 2 3 4; do
    for e in 0 -1; do
      lbl=$([ "$e" = "0" ] && echo "e=0" || echo "e=inf")
      printf "d=%s hold=%s %-6s: " "$d" "$h" "$lbl" >> "$out"
      python3 abandon.py tree "$d" --p $((d + 2)) --e "$e" --hold "$h" 2>&1 | tail -1 >> "$out"
    done
  done
done
echo DONE >> "$out"
