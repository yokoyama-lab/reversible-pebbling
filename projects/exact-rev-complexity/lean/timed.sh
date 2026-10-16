#!/bin/sh
# `sh lean/timed.sh <file.lean>` — leanc.sh を /usr/bin/time -v つきで走らせる。
# ⚠ Bash ツールが `/usr/bin/time -f ...` を含む行を断片と誤判定するので、スクリプトに包む。
set -u
/usr/bin/time -v -o /tmp/leanc_time.txt sh "$(dirname "$0")/leanc.sh" "$@"
rc=$?
grep -E 'Elapsed \(wall|Maximum resident' /tmp/leanc_time.txt
echo "rc=$rc"
exit $rc
