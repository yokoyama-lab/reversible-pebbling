#!/bin/bash
# ピラミッドの p_min を層2へ上げる（DRAT 証明書つき UNSAT）。
# ⚠ **素の CNF** で取る（--window は Lean の定理を CNF 生成器へ写したものなので、
#    証明書がその写しの正しさに依存しないようにする）。
export PATH="/home/linuxbrew/.linuxbrew/bin:<home>/.local/bin:$PATH"
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
mkdir -p data/q2_certs
OUT=data/q2_pyr_cert_log.csv
[ -f "$OUT" ] || echo "h,p,result,drat_size,verify,sec" > "$OUT"
for hp in "$@"; do
  H=${hp%%:*}; P=${hp##*:}; T=$((2*H-1))
  grep -q "^$H,$P," "$OUT" && continue
  C=data/q2_certs/pyr_h${H}_p${P}.cnf; D=/tmp/pcert_${H}_${P}.drat
  S0=$(date +%s)
  python3 scripts/q2_cnf.py --family pyramid --n $H --p $P --T $T --out "$C" >/dev/null 2>&1
  S=$(nice -19 timeout 72000 cadical "$C" "$D" --binary=false -q 2>&1 | grep -E '^s ' | head -1)
  if [ "$S" = "s UNSATISFIABLE" ]; then
    SZ=$(du -h "$D" | cut -f1)
    V=$(nice -19 timeout 72000 drat-trim "$C" "$D" 2>&1 | tr -d '\r' | grep -xE 's (NOT )?VERIFIED' | head -1)
    [ -z "$V" ] && V="検証打ち切り"
  else SZ="-"; V="-"; fi
  echo "$H,$P,${S:-打ち切り},$SZ,$V,$(( $(date +%s) - S0 ))" >> "$OUT"
  rm -f "$D"
done
