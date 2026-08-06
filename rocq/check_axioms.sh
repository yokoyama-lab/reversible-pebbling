#!/bin/sh
# Print Assumptions over EVERY window of the cover, not a hand-picked
# sample: the audit is generated from the theorems that exist, so a
# window that was added and forgotten cannot slip past it.
#
# One prover run per part -- loading all 24 parts at once would need
# about 10 GB -- and the parts run in parallel.  Exits 1 if any axiom
# outside the whitelist appears.
#
# Usage: sh check_axioms.sh [JOBS]      (from rocq/, after `make`)
# Cost:  about 1.2 s per window; ~3 min wall at JOBS=8.

set -e
ROCQ=${ROCQ:-rocq}
JOBS=${JOBS:-8}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# the classical reals, plus the primitive machine ints / floats / arrays
# that CoqInterval computes on
WHITELIST='^(Axioms|Closed|ClassicalDedekindReals|Classical_Prop|FunctionalExtensionality|ClassicalUniqueChoice|Uint63Axioms|Sint63Axioms|PrimInt63|FloatAxioms|PrimFloat|SpecFloat|PArray|PrimArray)$'

running=0
total=0
for part in LedgerCoverP*.v; do
  mod=${part%.v}
  f="$TMP/$mod.v"
  {
    echo "From RevPebblingRocq Require Import CoverGlue $mod."
    grep -o '^Theorem window_[0-9]*' "$part" | sed 's/^Theorem //' \
      | while read -r th; do echo "Print Assumptions $mod.$th."; done
  } > "$f"
  n=$(grep -c '^Print Assumptions' "$f")
  total=$((total + n))
  (
    # shellcheck disable=SC2086  # the loadpath flags must word-split
    bad=$($ROCQ c -Q . RevPebblingRocq "$f" 2>&1 \
          | grep -oE '^[A-Za-z_][A-Za-z0-9_]*' | sort -u \
          | grep -Ev "$WHITELIST" || true)
    if [ -n "$bad" ]; then
      echo "FAIL $mod: $bad" > "$TMP/$mod.bad"
    else
      echo "ok $mod ($n windows)"
    fi
  ) &
  running=$((running + 1))
  if [ "$running" -ge "$JOBS" ]; then wait; running=0; fi
done
wait

if ls "$TMP"/*.bad >/dev/null 2>&1; then
  cat "$TMP"/*.bad
  echo "AUDIT FAILED"
  exit 1
fi
echo "TOTAL: $total windows audited, no assumption outside the whitelist"
