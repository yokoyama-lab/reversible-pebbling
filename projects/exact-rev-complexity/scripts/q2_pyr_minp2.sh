#!/bin/bash
# ピラミッドの最小ピーク走査（--window 版・再開時も SAT で打ち切る）。
# ⚠ 旧 pyr.sh は再開時に「記録済みの SAT」で止まらず、p_min より上を延々と走査した。
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
cd ~/q2
OUT=~/q2/pyr_minp.csv
[ -f "$OUT" ] || echo "h,p,result,sec" > "$OUT"
for h in "$@"; do
  V=$((h*(h+1)/2)); T=$((2*h-1))
  for ((p=3; p<=V; p++)); do
    prev=$(grep "^$h,$p," "$OUT" | head -1 | cut -d, -f3)
    if [ -n "$prev" ]; then
      [ "$prev" = "s SATISFIABLE" ] && break
      continue
    fi
    S=$(date +%s)
    python3 scripts/q2_cnf.py --family pyramid --n $h --p $p --T $T --window --out /tmp/py_${h}_${p}.cnf >/dev/null 2>&1
    if [ ! -s /tmp/py_${h}_${p}.cnf ]; then R="CNF生成失敗"; else
      R=$(nice -19 timeout 36000 cadical /tmp/py_${h}_${p}.cnf -q 2>&1 | grep -E "^s " | head -1)
      [ -z "$R" ] && R=打ち切り
    fi
    rm -f /tmp/py_${h}_${p}.cnf
    echo "$h,$p,$R,$(( $(date +%s) - S ))" >> "$OUT"
    [ "$R" = "s SATISFIABLE" ] && break
  done
done
