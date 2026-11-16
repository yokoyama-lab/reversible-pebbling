#!/bin/sh
# 単一の .lean を、**本チェックアウトに既にビルドされている mathlib** を使って型検査する。
#
#   sh lean/leanc.sh lean/Revgarbage/HullLemma.lean
#
# ⚠ 参照先（<home>/dev/github.com/tetsuo-jp/exact-rev-complexity/lean/.lake）は
#   **読むだけ**。worktree 側に .lake を作らないし、本チェックアウトを一切書き換えない。
#   `lake build` は使わない（依存解決で本チェックアウトに書きに行くため）。
# ⚠ ネットワーク不使用（`lake exe cache get` などは呼ばない）。
set -u
MAIN=<home>/dev/github.com/tetsuo-jp/exact-rev-complexity/lean/.lake
# ⚠ lake v4.31 は olean を `.lake/build/lib/lean/` に置く（`lib/` 直下ではない）。
P="$MAIN/build/lib/lean"
for pkg in mathlib batteries aesop Qq proofwidgets importGraph Cli LeanSearchClient plausible; do
  for d in "$MAIN/packages/$pkg/.lake/build/lib/lean" "$MAIN/packages/$pkg/.lake/build/lib"; do
    [ -f "$d/$pkg.olean" ] || [ -d "$d" ] && { P="$P:$d"; break; }
  done
done
export LEAN_PATH="$P"
exec <home>/.elan/bin/lean "$@"
