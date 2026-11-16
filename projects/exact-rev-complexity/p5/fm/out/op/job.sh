#!/usr/bin/env bash
set -u
cd ~/p5fm
for t in 16 bin_17 bin_18; do
  s=$(date +%s)
  ./run_bfs.sh out/trees_$t.txt out/m_$t.txt 20
  echo "$t rc=$? $(( $(date +%s) - s ))s $(wc -l < out/m_$t.txt) lines" >> out/job.log
done
echo DONE >> out/job.log
