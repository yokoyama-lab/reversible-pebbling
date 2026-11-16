#!/bin/bash
# ピラミッドの最小ピークを**二分探索**で求める（2026-08-14）。
#
# 単調性: ピーク <= p の解は ピーク <= p+1 の解でもあるので、SAT/UNSAT は p について単調。
# したがって二分探索が使える。上端は「レベル一様」構成（q2_level_weighted.py、実測で
# p_min <= LU <= p_min+2 が h<=14 で成立）、下端は 3。
# 直線走査は p_min 回 SAT を呼ぶが、二分探索は log2(範囲) 回で済む。
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
cd "$(dirname "$0")/.."
OUT=data/q2_pyr_bisect.csv
[ -f "$OUT" ] || echo "h,p,result,sec,phase" > "$OUT"
ask() {  # h p → 0=SAT, 1=UNSAT, 2=打ち切り
  local h=$1 p=$2 T=$((2*$1-1)) S R
  R=$(grep "^$h,$p," "$OUT" | head -1 | cut -d, -f3)
  if [ -z "$R" ]; then
    S=$(date +%s)
    python3 scripts/q2_cnf.py --family pyramid --n $h --p $p --T $T --window --out /tmp/pb_${h}_${p}.cnf >/dev/null 2>&1
    if [ ! -s /tmp/pb_${h}_${p}.cnf ]; then R="CNF生成失敗"; else
      R=$(nice -19 timeout ${TMO:-36000} cadical /tmp/pb_${h}_${p}.cnf -q 2>&1 | grep -E "^s " | head -1)
      [ -z "$R" ] && R=打ち切り
    fi
    rm -f /tmp/pb_${h}_${p}.cnf
    echo "$h,$p,$R,$(( $(date +%s) - S )),bisect" >> "$OUT"
  fi
  case "$R" in "s SATISFIABLE") return 0;; "s UNSATISFIABLE") return 1;; *) return 2;; esac
}
for h in "$@"; do
  hi=$(.venv/bin/python -c "
import sys; sys.path.insert(0,'scripts')
from q2_level_weighted import solve
v,_ = solve([$h-k for k in range($h)], 600.0); print(v)")
  [ -z "$hi" ] && { echo "$h: 上界が出せない" >&2; continue; }
  lo=3
  # hi は構成があるので SAT のはず。健全性として確かめる。
  if ! ask "$h" "$hi"; then echo "$h: 上界 $hi が SAT でない（構成か符号化が誤り）" >&2; continue; fi
  while [ $((hi - lo)) -gt 0 ]; do
    mid=$(( (lo + hi) / 2 ))
    if ask "$h" "$mid"; then hi=$mid
    elif [ $? -eq 1 ]; then lo=$((mid + 1))
    else echo "$h: p=$mid で打ち切り。範囲 [$lo,$hi] のまま中断" >&2; break; fi
  done
  [ $lo -eq $hi ] && echo "$h,$lo,p_min確定,0,result" >> "$OUT"
done
