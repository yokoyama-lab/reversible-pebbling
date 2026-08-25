#!/usr/bin/env bash
set -u
VP=<local>/dev/github.com/tetsuo-jp/exact-rev-complexity/.venv/bin/python
out=cpsat_h4.log
: > "$out"
echo "== 校正やり直し: h=4 p=7、地平線 200（155 より十分大きい）==" >> "$out"
$VP cpsat_treeroot.py --h 4 --p 7 --horizon 200 --seconds 5400 --workers 8 2>&1 | tail -1 >> "$out"
echo DONE >> "$out"
