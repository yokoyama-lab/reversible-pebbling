#!/bin/bash
# 各 h について「p_min を達成できる最小の区間数 k」を求める。
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
OUT=data/q2_min_intervals.csv
[ -f "$OUT" ] || echo "h,min_k" > "$OUT"
for h in "$@"; do
  grep -q "^$h," "$OUT" && continue
  for k in 1 2 3 4 5 6; do
    r=$(.venv/bin/python scripts/q2_intervals.py --hmin $h --hmax $h --k $k --timeout 1200 2>&1 | grep -c "✔")
    if [ "$r" = "1" ]; then echo "$h,$k" >> "$OUT"; break; fi
    [ "$k" = "6" ] && echo "$h,>6" >> "$OUT"
  done
done
