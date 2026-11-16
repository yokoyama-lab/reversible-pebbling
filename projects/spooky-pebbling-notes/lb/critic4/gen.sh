#!/bin/bash
cd "$(dirname "$0")"
for cfg in "4 5 500 1 0" "4 5 500 2 20" "4 5 500 3 100" "4 5 300 4 400" "4 6 500 5 0" "4 6 500 6 60" "4 8 300 7 40" "3 4 500 8 0" "3 4 500 9 30"; do
  set -- $cfg
  ./optpaths $1 $2 $3 $4 $5 > paths_h$1_c$2_x$5.txt 2> log_h$1_c$2_x$5.txt
  echo "rc=$? $(cat log_h$1_c$2_x$5.txt)"
done
