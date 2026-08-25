#!/usr/bin/env bash
# 校正（h=4 が 155 か）→ 本番（h=5・p=8）。出力 cpsat.log
set -u
VP=<local>/dev/github.com/tetsuo-jp/exact-rev-complexity/.venv/bin/python
out=cpsat.log
: > "$out"
echo "== 校正: h=4 p=7 は 155 のはず ==" >> "$out"
$VP cpsat_treeroot.py --h 4 --p 7 --seconds 3600 --workers 16 2>&1 | tail -2 >> "$out"
echo "== 本番: h=5 p=8（最適ペブル数。χ'_e(5)=7 より）==" >> "$out"
$VP cpsat_treeroot.py --h 5 --p 8 --horizon 500 --seconds 10800 --workers 16 2>&1 | tail -2 >> "$out"
echo DONE >> "$out"
