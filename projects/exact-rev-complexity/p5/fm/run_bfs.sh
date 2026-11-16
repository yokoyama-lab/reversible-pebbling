#!/usr/bin/env bash
# 使い方: run_bfs.sh <trees.txt> <out.m> <並列数>
# bfs_m を木の行で分割して並列に走らせ，結果を連結する．
set -euo pipefail
in=$1; out=$2; P=$3
tmp=$(mktemp -d "${out}.parts.XXXX")
split -n l/"$P" -d -a 3 "$in" "$tmp/c_"
pids=()
for f in "$tmp"/c_*; do ./bfs_m < "$f" > "$f.m" & pids+=($!); done
trap 'kill "${pids[@]}" 2>/dev/null || true' EXIT
for p in "${pids[@]}"; do wait "$p"; done
trap - EXIT
cat "$tmp"/c_*.m > "$out"
rm -r "$tmp"
