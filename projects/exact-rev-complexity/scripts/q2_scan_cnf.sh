#!/bin/bash
# n*(p) を CNF+cadical で走査する。**1 点ごとに追記するので途中から再開できる。**
# ⚠ systemd --user は brew の PATH を失う（cadical が rc=127 になり「打ち切り」に化ける）
export PATH="/home/linuxbrew/.linuxbrew/bin:<home>/.local/bin:$PATH"
command -v cadical >/dev/null || { echo "cadical が無い" >&2; exit 127; }
P="$1"; LO="$2"; HI="$3"; OUT="$4"; TMO="${5:-3600}"
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
[ -f "$OUT" ] || echo "p,n,result,sec" > "$OUT"
for ((n=LO; n<=HI; n++)); do
  grep -q "^$P,$n," "$OUT" && continue          # 済みは飛ばす
  T=$((2*n-1)); S=$(date +%s)
  .venv/bin/python scripts/q2_cnf.py --family line --n $n --p $P --T $T --out /tmp/scan_${P}_${n}.cnf >/dev/null 2>&1
  if [ ! -s /tmp/scan_${P}_${n}.cnf ]; then R="CNF生成失敗"; else
    R=$(timeout $TMO cadical /tmp/scan_${P}_${n}.cnf -q 2>&1 | grep -E '^s ' | head -1)
    [ -z "$R" ] && R="打ち切り"
  fi
  rm -f /tmp/scan_${P}_${n}.cnf
  echo "$P,$n,${R:-打ち切り},$(( $(date +%s) - S ))" >> "$OUT"
done
