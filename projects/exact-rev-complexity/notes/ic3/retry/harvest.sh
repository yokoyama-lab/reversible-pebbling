#!/bin/bash
# ic3-retry-* が終わるのを待ち、ログと不変量を notes/ic3/retry/ へ写す。
# scratchpad は揮発するので、これが無いと結果が消える。
S=/work/tmp/claude-1000/-work-a-dev-github-com-tetsuo-jp-exact-rev-complexity-notes-ic3/475e0dbf-41a6-49b8-baeb-071ae7ceb4c1/scratchpad/ic3
D=<local>/dev/github.com/tetsuo-jp/exact-rev-complexity/notes/ic3/retry
mkdir -p "$D"
for i in $(seq 1 480); do
  n=$(systemctl --user list-units --type=service --no-legend | grep -c 'ic3-retry-')
  [ "$n" = 0 ] && break
  python3 -c "import time;time.sleep(60)"
done
for f in retry_h14p40 retry_h15p42; do
  [ -f "$S/$f.log" ] && cp "$S/$f.log" "$D/$f.log"
done
for f in pyr_h14_p40 pyr_h15_p42; do
  [ -f "$S/$f.inv" ] && gzip -c "$S/$f.inv" > "$D/$f.inv.gz"
done
{
  echo "# 再挑戦の回収（$(date '+%Y-%m-%d %H:%M')）"
  echo
  echo "2026-09-06 10:49 に空いた機械（load 3.1）へ再投入した 2 本の結果。"
  echo "初回の UNDECIDED は load 25〜29 の飽和した共用機での壁時計だった。"
  echo
  for f in retry_h14p40 retry_h15p42; do
    [ -f "$D/$f.log" ] || continue
    v=$(grep -hoE "Property proved|Property UNDECIDED|was asserted in frame [0-9]+" "$D/$f.log" | tail -1)
    t=$(grep -hoE "Time = *[0-9.]+ sec" "$D/$f.log" | tail -1)
    inv=$(grep -hoE "Invariant F\[[0-9]+\] : [0-9]+ clauses with [0-9]+ flops" "$D/$f.log" | tail -1)
    fr=$(grep -oE "^ *[0-9]+ :" "$D/$f.log" | tr -d ' :' | sort -n | tail -1)
    echo "- **$f**: ${v:-（判定行なし）} ${t} / 到達 frame ${fr:-?} ${inv:+/ $inv}"
  done
  echo
  echo "⚠ \`Property proved\` なら、\`scripts/ic3_verify.py\` で不変量を独立検査すること"
  echo "（本文 §12 と同じ 3 本。\`--split\` は cube 数 / 1000 くらい）。"
  echo "⚠ \`UNDECIDED\` は**打ち切り**であって「不変量が無い」ではない（本文 §0）。"
} > "$D/RESULTS.md"
