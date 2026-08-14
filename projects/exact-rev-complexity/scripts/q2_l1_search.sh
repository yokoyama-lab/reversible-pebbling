#!/bin/bash
# 補題 L1 を制約に加えて SAT を探す（**SAT 側専用**。UNSAT の根拠にはしない）
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
OUT=data/q2_l1_p12.csv
[ -f "$OUT" ] || echo "p,n,result,sec,note" > "$OUT"
for n in "$@"; do
  grep -q ",$n," "$OUT" && continue
  T=$((2*n-1)); S=$(date +%s)
  .venv/bin/python scripts/q2_cnf.py --family line --n $n --p 12 --T $T --fix-first --out /tmp/l1_$n.cnf >/dev/null 2>&1
  R=$(timeout 36000 cadical /tmp/l1_$n.cnf -q 2>&1 | grep -E '^s ' | head -1); [ -z "$R" ] && R="打ち切り"
  rm -f /tmp/l1_$n.cnf
  echo "12,$n,$R,$(( $(date +%s) - S )),L1制約つき" >> "$OUT"
  [ "$R" = "s SATISFIABLE" ] && break     # 一番大きい n が SAT なら決着
done
