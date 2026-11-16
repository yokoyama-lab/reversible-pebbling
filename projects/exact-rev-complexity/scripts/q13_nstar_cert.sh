#!/bin/bash
# Q13（n*(p) の上限側）の証明書を 1 点作る。
#   使い方: q13_nstar_cert.sh <p> <n>   （n は n*(p)+1、つまり**不可能**な側）
# 主張: 鎖 n 頂点は p ペブルでは T=2n-1（並列時間最適）に到達できない。
# ⚠ DRAT は /work/tmp へ書く（/tmp は 31GB の tmpfs で溢れる）。検査後に消す。
# ⚠ 0 行の DRAT は「検査した」が「中身が無い」ので行数を必ず記録する。
set -u
export PATH="/home/linuxbrew/.linuxbrew/bin:<home>/.local/bin:$PATH"
REPO=<local>/dev/github.com/tetsuo-jp/exact-rev-complexity
cd "$REPO" || exit 1
P="$1"; N="$2"; T=$((2*N-1))
WORK=/work/tmp/q13cert; mkdir -p "$WORK"
C="$WORK/line_n${N}_p${P}.cnf"; D="$WORK/cert_p${P}_n${N}.drat"
LOG=data/q13_nstar_cert.csv
[ -f "$LOG" ] || echo "p,n,T,vars,clauses,cnf_sha256,solve_sec,sat,drat_bytes,drat_lines,check_sec,verdict" > "$LOG"

GEN=$(PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/q2_cnf.py --family line --n "$N" --p "$P" --T "$T" --out "$C" 2>&1) || { echo "CNF 生成に失敗: $GEN"; exit 1; }
VARS=$(echo "$GEN" | sed -n 's/.*: \([0-9]*\) 変数.*/\1/p')
CLS=$(echo "$GEN" | sed -n 's/.*\/ \([0-9]*\) 節.*/\1/p')
SHA=$(sha256sum "$C" | cut -d' ' -f1)

t0=$(date +%s)
S=$(timeout "${SOLVE_TIMEOUT:-3600}" cadical "$C" "$D" --binary=false -q 2>&1 | grep -E '^s ' | head -1)
t1=$(date +%s); SOLVE=$((t1-t0))
if [ "$S" != "s UNSATISFIABLE" ]; then
  echo "$P,$N,$T,$VARS,$CLS,$SHA,$SOLVE,\"${S:-打ち切り}\",,,,未検査" >> "$LOG"
  echo "p=$P n=$N: $S（${SOLVE}秒）— UNSAT でないので証明書は作れない"; rm -f "$D"; exit 2
fi
BYTES=$(stat -c%s "$D"); LINES=$(wc -l < "$D")
t2=$(date +%s)
V=$(timeout "${CHECK_TIMEOUT:-7200}" drat-trim "$C" "$D" 2>&1 | tr -d '\r' | grep -xE 's (NOT )?VERIFIED' | head -1)
t3=$(date +%s); CHECK=$((t3-t2))
echo "$P,$N,$T,$VARS,$CLS,$SHA,$SOLVE,UNSAT,$BYTES,$LINES,$CHECK,\"${V:-打ち切り}\"" >> "$LOG"
echo "p=$P n=$N T=$T: UNSAT（${SOLVE}秒）/ DRAT ${BYTES}B・${LINES}行 / ${V:-打ち切り}（${CHECK}秒）"
rm -f "$D"
