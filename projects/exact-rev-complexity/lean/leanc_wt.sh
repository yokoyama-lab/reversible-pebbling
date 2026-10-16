#!/bin/sh
# `leanc.sh` と同じだが、**worktree 側の `lean/build`** も LEAN_PATH に足す。
#
#   sh lean/leanc_wt.sh lean/Revgarbage/LevelCertAut.lean -o lean/build/LevelCertAut.olean
#
# `LevelCert` / `LevelCertQuot` 系は bare import（lake のモジュール名ではない）なので、
# `lake build` では `unknown module prefix` で落ちる（第79夜 周2 の実測）。
# 本チェックアウトの `.lake` は**読むだけ**。ネットワーク不使用。
set -u
MAIN=<home>/dev/github.com/tetsuo-jp/exact-rev-complexity/lean/.lake
WT=$(cd "$(dirname "$0")" && pwd)/build
P="$MAIN/build/lib/lean"
for pkg in mathlib batteries aesop Qq proofwidgets importGraph Cli LeanSearchClient plausible; do
  for d in "$MAIN/packages/$pkg/.lake/build/lib/lean" "$MAIN/packages/$pkg/.lake/build/lib"; do
    [ -f "$d/$pkg.olean" ] || [ -d "$d" ] && { P="$P:$d"; break; }
  done
done
export LEAN_PATH="$P:$WT"
exec <home>/.elan/bin/lean "$@"
