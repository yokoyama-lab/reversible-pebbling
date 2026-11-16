#!/bin/bash
# ピラミッド: 時間最適 T=2h-1 を達成できる**最小ピーク p** を求める（再開可能）
export PATH="/home/linuxbrew/.linuxbrew/bin:<home>/.local/bin:$PATH"
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
H1="$1"; H2="$2"; OUT="$3"; TMO="${4:-2400}"
[ -f "$OUT" ] || echo "h,p,result,sec" > "$OUT"
for ((h=H1; h<=H2; h++)); do
  V=$((h*(h+1)/2)); T=$((2*h-1))
  for ((p=3; p<=V; p++)); do
    grep -q "^$h,$p," "$OUT" && continue
    S=$(date +%s)
    .venv/bin/python scripts/q2_cnf.py --family pyramid --n $h --p $p --T $T --out /tmp/py_${h}_${p}.cnf >/dev/null 2>&1
    if [ ! -s /tmp/py_${h}_${p}.cnf ]; then R="CNF生成失敗"; else
      R=$(timeout $TMO cadical /tmp/py_${h}_${p}.cnf -q 2>&1 | grep -E '^s ' | head -1); [ -z "$R" ] && R="打ち切り"
    fi
    rm -f /tmp/py_${h}_${p}.cnf
    echo "$h,$p,$R,$(( $(date +%s) - S ))" >> "$OUT"
    [ "$R" = "s SATISFIABLE" ] && break     # 最小 p が見つかったら次の h へ
  done
done
