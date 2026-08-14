#!/bin/bash
export PATH="/home/linuxbrew/.linuxbrew/bin:<home>/.local/bin:$PATH"
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
N="$1"; P="$2"; T=$((2*N-1))
C=data/q2_certs/line_n${N}_p${P}.cnf; D=/tmp/cert_${P}_${N}.drat
.venv/bin/python scripts/q2_cnf.py --family line --n $N --p $P --T $T --out $C >/dev/null 2>&1
S=$(timeout 72000 cadical "$C" "$D" --binary=false -q 2>&1 | grep -E '^s ' | head -1)
if [ "$S" = "s UNSATISFIABLE" ]; then
  SZ=$(du -h "$D" | cut -f1)
  V=$(timeout 72000 drat-trim "$C" "$D" 2>&1 | tr -d '\r' | grep -xE 's (NOT )?VERIFIED' | head -1)
  echo "$P,$N,$S,$SZ,$V" >> data/q2_cert_log.csv
fi
rm -f "$D"
