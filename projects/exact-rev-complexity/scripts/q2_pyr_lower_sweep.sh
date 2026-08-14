#!/bin/bash
# 拡大性つき下界に DRAT 証明書を付けて掃く。B は「下界-1」（UNSAT になるはず）。
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
OUT=data/q2_pyr_lower_cert.csv
[ -f "$OUT" ] || echo "h,B,result,drat,verify" > "$OUT"
for hb in "$@"; do
  H=${hb%%:*}; B=${hb##*:}
  grep -q "^$H,$B," "$OUT" && continue
  L=$(python3 scripts/q2_pyr_lower_cert.py --h $H --B $B --drat 2>&1 | tail -1)
  st=$(echo "$L" | sed 's/.*: \(s [A-Z]*\) .*/\1/')
  dr=$(echo "$L" | sed 's/.*DRAT \([^ ]*\) .*/\1/')
  ve=$(echo "$L" | sed 's/.*\/ \(s [A-Z]*\)$/\1/')
  echo "$H,$B,$st,$dr,$ve" >> "$OUT"
done
