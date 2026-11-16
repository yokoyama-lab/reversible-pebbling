#!/usr/bin/env bash
set -u
out=sat_h4.log
: > "$out"
echo "== h=4 p=7: Dijkstra の 155 を SAT で追認し、154 の UNSAT に証明ログを付ける ==" >> "$out"
printf "k=155: " >> "$out"; python3 sat_treeroot.py --h 4 --p 7 --k 155 --timeout 3000 2>&1 | tail -1 >> "$out"
printf "k=154: " >> "$out"; python3 sat_treeroot.py --h 4 --p 7 --k 154 --timeout 3000 2>&1 | tail -1 >> "$out"
echo DONE >> "$out"
