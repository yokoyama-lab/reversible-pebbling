#!/bin/bash
# 鎖（line）で時間最適 T=2n-1 を達成できる最小ピーク p_min(n)。
# ⚠ 素の CNF（--fix-first を使わない）なので UNSAT に証明力がある。
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
OUT=data/q2_line_minp.csv
[ -f "$OUT" ] || echo "n,p,result,sec" > "$OUT"
for n in "$@"; do
  T=$((2*n-1))
  for ((p=1; p<=n; p++)); do
    grep -q "^$n,$p," "$OUT" && continue
    S=$(date +%s)
    python3 scripts/q2_cnf.py --family line --n $n --p $p --T $T --out /tmp/ln_${n}_${p}.cnf >/dev/null 2>&1
    R=$(nice -19 timeout 36000 cadical /tmp/ln_${n}_${p}.cnf -q 2>&1 | grep -E "^s " | head -1)
    [ -z "$R" ] && R=打ち切り
    rm -f /tmp/ln_${n}_${p}.cnf
    echo "$n,$p,$R,$(( $(date +%s) - S ))" >> "$OUT"
    [ "$R" = "s SATISFIABLE" ] && break
  done
done
