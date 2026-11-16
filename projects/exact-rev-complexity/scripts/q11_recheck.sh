#!/bin/bash
# Q11 の検算条項（2026-08-18）: h=2..16 の p_min を素の CNF で再現する。出力は recheck.csv（data/q11_recheck.csv に保存）。
# 実行場所は $Q11_WORK（既定 /tmp）。
# 検算条項: h=2..16 の p_min を素の CNF で再現（SAT 側は cadical の判定のみ・解の独立検査は tests/test_q2_descent.py と scripts/q2_profile.py の verify で別途、UNSAT 側は DRAT を drat-trim）
export PATH="/home/linuxbrew/.linuxbrew/bin:<home>/.local/bin:$PATH"
cd "${Q11_WORK:-/tmp}"
REPO="$(cd "$(dirname "$0")/.." && pwd)"
declare -A PM=( [2]=3 [3]=6 [4]=8 [5]=10 [6]=13 [7]=16 [8]=20 [9]=23 [10]=26 [11]=29 [12]=32 [13]=37 [14]=41 [15]=45 [16]=49 )
echo "h,p,kind,result,drat_verify,sec" > recheck.csv
for h in $(seq 2 16); do
  p=${PM[$h]}; T=$((2*h-1))
  for kind in sat unsat; do
    if [ $kind = sat ]; then pp=$p; else pp=$((p-1)); fi
    C=rc_h${h}_p${pp}.cnf; D=rc_h${h}_p${pp}.drat
    python3 $REPO/scripts/q2_cnf.py --family pyramid --n $h --p $pp --T $T --out $C >/dev/null
    S0=$(date +%s)
    if [ $kind = sat ]; then
      R=$(nice -19 timeout 3600 cadical -q $C | grep -E '^s ' | head -1); V=-
    else
      R=$(nice -19 timeout 3600 cadical $C $D --binary=false -q | grep -E '^s ' | head -1)
      V=$(nice -19 timeout 3600 drat-trim $C $D 2>&1 | tr -d '\r' | grep -xE 's (NOT )?VERIFIED' | head -1)
      rm -f $D
    fi
    echo "$h,$pp,$kind,$R,$V,$(( $(date +%s)-S0 ))" >> recheck.csv
    rm -f $C
  done
done
echo DONE >> recheck.csv
