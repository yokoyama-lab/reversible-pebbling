#!/usr/bin/env bash
# 族アトラス・ループ 1 反復の合否判定。**これが唯一の合否**である。
#
#   0 で終了 → その反復の変更を残してよい（commit する）
#   非 0     → 変更を捨てる（git checkout -- . && git clean -fdq data/families scripts tests）
#
# 設計: **探索は合否に入れない。証書の再生だけを入れる。**
# 探索（`family_atlas.py --build`）は反復の中で 1 回だけ走らせ、
# 出た値は証書つきで台帳に残る。以後の反復はその証書を再生するだけでよい（1 秒未満）。
# こうしないと台帳が伸びるほど合否が遅くなり、ループが止まる。
#
# 使い方:  tools/loopcheck.sh          # 全部（約 10 秒）
#          tools/loopcheck.sh --fast   # 族まわりだけ（既存エンジンを触っていないとき）
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2

PY=.venv/bin/python
[ -x "$PY" ] || PY=python3

fast=0
[ "${1:-}" = "--fast" ] && fast=1

fail() {
  echo "NG: $1"
  [ -n "${2:-}" ] && printf '%s\n' "$2" | tail -40
  exit 1
}

out=$("$PY" tests/test_families.py 2>&1) || fail "tests/test_families.py" "$out"
out=$("$PY" scripts/family_atlas.py --verify 2>&1) || fail "family_atlas --verify" "$out"
out=$("$PY" tests/test_families_atlas.py 2>&1) || fail "tests/test_families_atlas.py" "$out"
out=$("$PY" scripts/family_cpsat.py --verify 2>&1) || fail "family_cpsat --verify" "$out"

if [ "$fast" -eq 0 ]; then
  # 台帳が乗っているエンジンそのものの回帰（族を足しても壊れていないこと）
  out=$("$PY" tests/test_revpebble.py 2>&1) || fail "tests/test_revpebble.py" "$out"
  out=$("$PY" tests/test_exp01b.py 2>&1) || fail "tests/test_exp01b.py" "$out"
fi

rows=$(( $(wc -l < data/families/atlas.csv) - 1 ))
echo "OK  台帳 ${rows} 行"
