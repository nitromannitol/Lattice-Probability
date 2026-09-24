#!/bin/bash
# Elaborate one file standalone with the audit library's exact lean options (the
# same flags lakefile.lean sets for LatticeProbAudit), reporting the compiler's
# output verbatim.  For a Challenge file the expected outcome is rc=0 with
# exactly one `declaration uses 'sorry'` warning (the intentional target);
# for every other file, rc=0 with empty output.
#
# Usage (from the repository root or from Audit/):
#   bash Audit/check_standalone.sh Audit/LatticeProbAudit/Kingman/Challenge.lean
#   bash Audit/check_standalone.sh --vocabulary
# The second form checks that the vocabulary block between VOCABULARY-BEGIN and
# VOCABULARY-END is byte-identical in every challenge that has one and in
# Audit/LatticeProbAudit/Support/Vocabulary.lean.
set -u
cd "$(dirname "$0")/.."
if [ "${1:-}" = "--vocabulary" ]; then
  block() { sed -n '/^-- VOCABULARY-BEGIN$/,/^-- VOCABULARY-END$/p' "$1"; }
  REF=$(block Audit/LatticeProbAudit/Support/Vocabulary.lean | sha256sum | cut -d' ' -f1)
  RC=0
  for f in Audit/LatticeProbAudit/*/Challenge.lean; do
    grep -q '^-- VOCABULARY-BEGIN$' "$f" || { echo "no block   $f"; continue; }
    H=$(block "$f" | sha256sum | cut -d' ' -f1)
    if [ "$H" = "$REF" ]; then echo "identical  $f"; else echo "DIFFERENT  $f"; RC=1; fi
  done
  echo "vocabulary sha256=$REF rc=$RC"
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
