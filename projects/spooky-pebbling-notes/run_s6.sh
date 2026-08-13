#!/usr/bin/env bash
# theta(6)=21 の事前登録した検定を SAT で回す。
# systemd --user は brew の PATH を失うので明示する（cadical / drat-trim が rc=127 になる）。
set -u
export PATH="/home/linuxbrew/.linuxbrew/bin:<home>/.local/bin:/usr/bin:/bin"
cd <local>/dev/notes/spooky-pebbling || exit 1

echo "=== 事前登録した予測（closed.py） ==="
echo "  n=20 s=6: T_UP=67 T_UG=68 (delta=+1)"
echo "  n=21 s=6: T_UP=73 T_UG=72 (delta=-1) ← theta(6)=21 ならここで反転"
echo "  開始: $(date -Iseconds)"

rc=0
for job in "20 6 UP 67" "20 6 UG 68" "21 6 UP 73" "21 6 UG 72"; do
  echo; echo "--- $job ---"
  # shellcheck disable=SC2086  # $job は 4 引数に分割させたい
  timeout 20000 python3 sat_spooky.py --exact $job --proofs proofs || rc=1
done

echo; echo "終了: $(date -Iseconds) / rc=$rc"
exit "$rc"
