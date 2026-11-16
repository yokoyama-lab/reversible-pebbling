#!/usr/bin/env bash
# h=4 の追試（規則を言い当てたら次の H で追試する）。**手数の測定を先に**。出力 h4_probe.log
set -u
out=h4_probe.log
: > "$out"
echo "== treeroot 4 の最小 p と手数（p を下から上げる。最初に値が出た p が最小）==" >> "$out"
for p in 6 7 8 9; do
  printf "p=%s: " "$p" >> "$out"
  python3 abandon.py treeroot 4 --p "$p" --e 0 --final keep 2>&1 | tail -1 >> "$out"
done
echo "== χ'_e(4) を独立計算（時間上限 40 分） ==" >> "$out"
timeout 2400 python3 -c "
import calib_kss as c
print('chi_e(4) =', c.chi_e(4))
" >> "$out" 2>&1 || echo "chi_e(4): 打ち切り（＝未確定。値が無いことを結果と読まない）" >> "$out"
echo DONE >> "$out"
