#!/bin/bash
# 複数の n を並列に解く（1 点 1 ユニット）。素の CNF なので SAT/UNSAT どちらも証明力がある。
export PATH="/home/linuxbrew/.linuxbrew/bin:$PATH"
cd <local>/dev/github.com/tetsuo-jp/exact-rev-complexity
P="$1"; shift
for n in "$@"; do
  OUT=data/q2_pt_${P}_${n}.txt
  [ -s "$OUT" ] && continue
  u="q2pt${P}n${n}"
  systemctl --user reset-failed "$u" 2>/dev/null
  # ⚠ systemd ユニットは親の cwd も PATH も継がない。両方明示する
  systemd-run --user --unit="$u" -p RuntimeMaxSec=150000 -p MemoryMax=8G \
    --working-directory=<local>/dev/github.com/tetsuo-jp/exact-rev-complexity \
    -E PATH="/home/linuxbrew/.linuxbrew/bin:/usr/bin:/bin" \
    bash -c "T=\$((2*$n-1)); S=\$(date +%s)
      .venv/bin/python scripts/q2_cnf.py --family line --n $n --p $P --T \$T --out /tmp/pt_${P}_${n}.cnf >/dev/null 2>&1
      R=\$(timeout 144000 cadical /tmp/pt_${P}_${n}.cnf -q 2>&1 | grep -E '^s ' | head -1); [ -z \"\$R\" ] && R=打ち切り
      rm -f /tmp/pt_${P}_${n}.cnf
      echo \"$P,$n,\$R,\$(( \$(date +%s) - S ))\" > $OUT" >/dev/null 2>&1
  echo "  投入 p=$P n=$n"
done
