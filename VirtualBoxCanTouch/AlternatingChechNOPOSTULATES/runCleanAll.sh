#!/usr/bin/env bash
# Run importClean.sh on all Agda files in dependency order

FILES=(
  Trichotomy.agda
  CechBase.agda
  CechPermutations.agda
  CechFaceMaps.agda
  CechSorting.agda
  CechProperties.agda
  CechDSquared.agda
  work.agda
)

for f in "${FILES[@]}"; do
  echo ""
  echo "########################################"
  echo "# Cleaning: $f"
  echo "########################################"
  ./importClean.sh "$f" 120 || echo "(script exited with error for $f)"
done

echo ""
echo "========================================"
echo "ALL FILES DONE"
echo "========================================"
