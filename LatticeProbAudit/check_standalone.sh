#!/bin/bash
# Elaborate one file standalone with the audit library's exact lean options (the
# same flags lakefile.lean sets for LatticeProbAudit), reporting the compiler's
# output verbatim.  For a Challenge file the expected outcome is rc=0 with
# exactly one `declaration uses 'sorry'` warning (the intentional target);
# for every other file, rc=0 with empty output.
#
# Usage (from the repository root or from LatticeProbAudit/):
#   bash LatticeProbAudit/check_standalone.sh LatticeProbAudit/Kingman/Challenge.lean
#   bash LatticeProbAudit/check_standalone.sh --vocabulary
# The second form checks, for every challenge that has a vocabulary block, that the block
# between VOCABULARY-BEGIN and VOCABULARY-END is byte-identical in
# LatticeProbAudit/<Pair>/Challenge.lean and in LatticeProbAudit/<Pair>/SolutionBasic.lean.
# A challenge without a block defines nothing beyond Mathlib's and has no SolutionBasic.
set -u
cd "$(dirname "$0")/.."
if [ "${1:-}" = "--vocabulary" ]; then
  block() { sed -n '/^-- VOCABULARY-BEGIN$/,/^-- VOCABULARY-END$/p' "$1"; }
  RC=0
  for c in LatticeProbAudit/*/Challenge.lean; do
    d="$(dirname "$c")/SolutionBasic.lean"
    if ! grep -q '^-- VOCABULARY-BEGIN$' "$c"; then
      if [ -e "$d" ]; then echo "DIFFERENT  $c  $d (the challenge has no vocabulary block)"; RC=1
      else echo "no block   $c"; fi
      continue
    fi
    if [ ! -e "$d" ]; then echo "MISSING    $c  $d"; RC=1; continue; fi
    H1=$(block "$c" | sha256sum | cut -d' ' -f1)
    H2=$(block "$d" | sha256sum | cut -d' ' -f1)
    if [ "$H1" = "$H2" ]; then echo "identical  $c  $d"; else echo "DIFFERENT  $c  $d"; RC=1; fi
  done
  exit $RC
fi
SRC="$1"
OUTPUT=$(lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -Dlinter.unusedVariables=true -Dlinter.unusedSectionVars=true \
  -Dlinter.unusedSimpArgs=true -Dlinter.unnecessarySimpa=true \
  -Dlinter.deprecated=true "$SRC" 2>&1)
RC=$?
printf '%s\n' "$OUTPUT"
echo "rc=$RC output-bytes=$(printf '%s' "$OUTPUT" | wc -c) file=$SRC"
exit $RC
