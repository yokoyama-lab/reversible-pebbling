#!/usr/bin/env bash
# 校正: 実装 A（fbfs）・B（fbfs_b、枝刈りあり／なし）・B の素朴版（fbfs_b_naive）を h<=7 の既知の値で検算し、
# 層ごとの状態数を突き合わせる。F の証人を独立の検査器で再生する。
# 出力は logs/calib/。既知の値と食い違えば非 0 で終わる。
#
#   bash calibrate.sh [スレッド数]      # 既定 4。h=7 を含めて <host> で約 15 分
set -euo pipefail
cd "$(dirname "$0")"
T=${1:-4}
OUT=logs/calib
mkdir -p "$OUT"
gcc -O3 -march=native -fopenmp -Wall -Wextra -o fbfs fbfs.c
gcc -O3 -march=native -fopenmp -Wall -Wextra -o fbfs_b fbfs_b.c
gcc -O3 -march=native -fopenmp -Wall -Wextra -o fbfs_b_naive fbfs_b_naive.c
sha256sum fbfs.c fbfs_b.c fbfs_b_naive.c check_seq.py witness.py > "$OUT/sources.sha256"

# (h p 既知の M。-1 = 到達不能)。h<=6 は P5 の表、h=7 は原稿 §3（p=9 は 51,366,736 状態で到達不能）
CASES="2:3:5 3:4:-1 3:5:17 4:5:-1 4:6:53 5:6:-1 5:7:155 6:7:-1 6:8:429 6:9:339 6:10:295 6:11:261 7:9:-1 7:10:1001"
fail=0
: > "$OUT/summary.txt"
for c in $CASES; do
  IFS=: read -r h p want <<< "$c"
  ./fbfs "$h" "$p" --threads "$T" --stop-at-goal 0 --layers "$OUT/A_h${h}_p${p}.txt" > "$OUT/A_h${h}_p${p}.log"
  ./fbfs_b "$h" "$p" --threads "$T" --stop-at-goal 0 --layers "$OUT/B_h${h}_p${p}.txt" > "$OUT/B_h${h}_p${p}.log"
  if [ "$h" -le 6 ]; then
    ./fbfs_b "$h" "$p" --threads "$T" --stop-at-goal 0 --noprune --layers "$OUT/Bnp_h${h}_p${p}.txt" > "$OUT/Bnp_h${h}_p${p}.log"
    ./fbfs_b_naive "$h" "$p" --threads "$T" --stop-at-goal 0 --layers "$OUT/Bn_h${h}_p${p}.txt" > "$OUT/Bn_h${h}_p${p}.log"
  fi
  gA=$(grep -o 'goal_depth=-\?[0-9]*' "$OUT/A_h${h}_p${p}.log" | cut -d= -f2)
  gB=$(grep -o 'goal_depth=-\?[0-9]*' "$OUT/B_h${h}_p${p}.log" | cut -d= -f2)
  exA=$(grep -o 'exhausted=[01]' "$OUT/A_h${h}_p${p}.log" | cut -d= -f2)
  totA=$(grep -o 'total_states=[0-9]*' "$OUT/A_h${h}_p${p}.log" | cut -d= -f2)
  cmpB=$(python3 compare_layers.py "$OUT/A_h${h}_p${p}.txt" "$OUT/B_h${h}_p${p}.txt" | cut -c1-9)
  extra=""
  if [ "$h" -le 6 ]; then
    c1=$(python3 compare_layers.py "$OUT/A_h${h}_p${p}.txt" "$OUT/Bnp_h${h}_p${p}.txt" | cut -c1-9)
    c2=$(python3 compare_layers.py "$OUT/A_h${h}_p${p}.txt" "$OUT/Bn_h${h}_p${p}.txt" | cut -c1-9)
    extra=" B(noprune)=$c1 B(naive)=$c2"
  fi
  ok=OK
  if [ "$gA" != "$want" ] || [ "$gB" != "$want" ] || [ "$exA" != 1 ] || [ "$cmpB" != IDENTICAL ]; then ok=NG; fail=1; fi
  if [ -n "$extra" ] && [[ "$extra" == *DIFFER* ]]; then ok=NG; fail=1; fi
  echo "$ok h=$h p=$p 既知=$want A=$gA B=$gB 枯渇=$exA 総状態数=$totA 層: B=$cmpB$extra" | tee -a "$OUT/summary.txt"
done

# F の証人（上界）を独立の検査器で再生
for hs in 2:3 3:5 4:6 5:7 6:8 6:11 7:10 8:11; do
  IFS=: read -r h s <<< "$hs"
  python3 witness.py "$h" "$s" > "$OUT/witness_h${h}_p${s}.txt"
  python3 check_seq.py "$h" "$s" "$OUT/witness_h${h}_p${s}.txt" | tee -a "$OUT/summary.txt"
done
if python3 check_seq.py 8 10 "$OUT/witness_h8_p11.txt" > /dev/null; then echo "NG: S=10 で受理された" | tee -a "$OUT/summary.txt"; fail=1; else echo "OK: h=8 の証人は S=10 では棄却（検査器が上限を見ている）" | tee -a "$OUT/summary.txt"; fi
exit $fail
