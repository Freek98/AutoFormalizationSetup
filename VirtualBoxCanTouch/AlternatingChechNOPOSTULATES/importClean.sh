#!/usr/bin/env bash
# importClean.sh — Remove unused imports from Agda files.
# Usage: ./importClean.sh <file.agda> [timeout_seconds]
#
# For each "open import ..." line, temporarily removes it and checks
# if the file still compiles. If it does, the import stays removed.
# If compilation fails, the removal is undone via file restore.

set -euo pipefail

FILE="${1:?Usage: $0 <file.agda> [timeout_seconds]}"
TIMEOUT="${2:-120}"

if [ ! -f "$FILE" ]; then
  echo "Error: $FILE not found"
  exit 1
fi

AGDA="/project/agda"
BACKUP="${FILE}.importClean.bak"
TMPFILE="${FILE}.importClean.tmp"

# Use unaliased cp to avoid -i prompts
CP="/usr/bin/cp"

# Save a safety backup
$CP -f "$FILE" "$BACKUP"

echo "=== importClean: $FILE (timeout=${TIMEOUT}s) ==="

# First verify the file compiles as-is
echo "Verifying file compiles before cleaning..."
if ! timeout "$TIMEOUT" "$AGDA" "$FILE" >/dev/null 2>&1; then
  echo "Error: $FILE does not compile in its current state. Aborting."
  exit 1
fi
echo "OK — file compiles."

# Find the first "module <Name>" line to identify pre-module imports
MODULE_LN=$(grep -n '^module ' "$FILE" | head -1 | cut -d: -f1 || echo "")

# Collect line numbers of import lines, processed in reverse order
# so that deletions don't shift the line numbers of earlier entries
IMPORT_LINES=$(grep -n '^\(open \)\?import ' "$FILE" | cut -d: -f1 | sort -rn)

if [ -z "$IMPORT_LINES" ]; then
  echo "No import lines found."
  rm -f "$BACKUP"
  exit 0
fi

REMOVED=0
KEPT=0

for LN in $IMPORT_LINES; do
  # Read the line content for display
  LINE=$(sed -n "${LN}p" "$FILE")

  # Skip pre-module imports (needed for module parameters)
  if [ -n "$MODULE_LN" ] && [ "$LN" -lt "$MODULE_LN" ]; then
    echo "  SKIP (pre-module): $LINE"
    continue
  fi

  # Save current good state
  $CP -f "$FILE" "$TMPFILE"

  # Remove the line
  sed -i "${LN}d" "$FILE"

  # Try to compile
  if timeout "$TIMEOUT" "$AGDA" "$FILE" >/dev/null 2>&1; then
    echo "  REMOVED: $LINE"
    REMOVED=$((REMOVED + 1))
  else
    # Restore from saved copy
    $CP -f "$TMPFILE" "$FILE"
    echo "  KEPT:    $LINE"
    KEPT=$((KEPT + 1))
  fi
done

# Clean up temp file
rm -f "$TMPFILE"

echo ""
echo "=== Done: removed $REMOVED, kept $KEPT imports ==="
echo "Safety backup at: $BACKUP"
