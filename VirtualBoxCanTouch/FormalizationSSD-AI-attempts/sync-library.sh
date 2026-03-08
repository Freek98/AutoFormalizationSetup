#!/bin/bash
# Sync script: copies files from /FormalizationSSD/ to formalization/Library/
# and updates module names/imports to use formalization.Library.* prefix.
#
# This ensures the project works even when /FormalizationSSD/ is not mounted
# (e.g., on another host machine via git).
#
# Also applies known fixes for compatibility with the current cubical library.

SRC="/FormalizationSSD"
DST="/CanTouch/FormalizationSSD-AI-attempts/formalization/Library"

if [ ! -d "$SRC" ]; then
  echo "Source $SRC not found (not mounted?). Skipping sync."
  exit 0
fi

rewrite_imports() {
  local f="$1"
  # Rewrite bare imports to use formalization.Library.* prefix
  # Each prefix is handled separately to avoid sed alternation issues
  sed -i -E 's/(open import|import) AntiEquivalence/\1 formalization.Library.AntiEquivalence/g' "$f"
  sed -i -E 's/(open import|import) Axioms\./\1 formalization.Library.Axioms./g' "$f"
  sed -i -E 's/(open import|import) BasicDefinitions/\1 formalization.Library.BasicDefinitions/g' "$f"
  sed -i -E 's/(open import|import) BooleanRing\./\1 formalization.Library.BooleanRing./g' "$f"
  sed -i -E 's/(open import|import) CategoryTheory\./\1 formalization.Library.CategoryTheory./g' "$f"
  sed -i -E 's/(open import|import) CommRingQuotients\./\1 formalization.Library.CommRingQuotients./g' "$f"
  sed -i -E 's/(open import|import) CountablyPresentedBooleanRings\./\1 formalization.Library.CountablyPresentedBooleanRings./g' "$f"
  sed -i -E 's/(open import|import) OmnisciencePrinciples\./\1 formalization.Library.OmnisciencePrinciples./g' "$f"
  sed -i -E 's/(open import|import) PropositionalTopology\./\1 formalization.Library.PropositionalTopology./g' "$f"
  sed -i -E 's/(open import|import) QuickFixes/\1 formalization.Library.QuickFixes/g' "$f"
  sed -i -E 's/(open import|import) StoneSpaces\./\1 formalization.Library.StoneSpaces./g' "$f"
  # TerminalBA is in BooleanRing/ subdir but module name says just TerminalBA
  sed -i -E 's/(open import|import) TerminalBA/\1 formalization.Library.BooleanRing.TerminalBA/g' "$f"
  # Prevent double-prefixing
  sed -i 's/formalization\.Library\.formalization\.Library\./formalization.Library./g' "$f"
}

apply_fixes() {
  local f="$1"
  local base
  base=$(basename "$f")

  # Fix unsolved meta in StuffThatWasInStoneAndShouldBeOrganized.agda
  if [ "$base" = "StuffThatWasInStoneAndShouldBeOrganized.agda" ]; then
    sed -i 's/h ⋆⟨ D ⟩ _) (F \.F-seq f (η ⟦ y ⟧))/h ⋆⟨ D ⟩ (ε ⟦ F ⟅ y ⟆ ⟧)) (F .F-seq f (η ⟦ y ⟧))/' "$f"
  fi

  # Add public re-exports for Axioms/StoneDuality.agda
  if [ "$base" = "StoneDuality.agda" ] && echo "$f" | grep -q "Axioms"; then
    sed -i '/^open import formalization\.Library\./s/$/ public/' "$f"
    # Remove double public
    sed -i 's/ public public$/ public/' "$f"
  fi
}

copy_and_rewrite() {
  local rel="$1"
  local src_file="$SRC/$rel"
  local dst_file="$DST/$rel"

  mkdir -p "$(dirname "$dst_file")"
  cp "$src_file" "$dst_file"

  # Derive module name from path
  local bare_module
  bare_module=$(echo "$rel" | sed 's|\.agda$||; s|/|.|g')
  local new_module="formalization.Library.$bare_module"

  # Rewrite module declaration
  sed -i "s|^module ${bare_module}|module ${new_module}|" "$dst_file"

  # Handle mismatched module names
  local current_module
  current_module=$(grep -oP '^module \K[^ ]+' "$dst_file" | head -1)
  if [ -n "$current_module" ] && [ "$current_module" != "$new_module" ]; then
    sed -i "s|^module ${current_module}|module ${new_module}|" "$dst_file"
  fi

  rewrite_imports "$dst_file"
  apply_fixes "$dst_file"
}

echo "Syncing from $SRC to $DST..."

find "$SRC" -name "*.agda" | while read -r src_file; do
  rel="${src_file#$SRC/}"
  dst_file="$DST/$rel"

  if [ -f "$dst_file" ]; then
    if ! diff -q "$src_file" "$dst_file" > /dev/null 2>&1; then
      if grep -q "^module formalization\.Library\." "$dst_file" 2>/dev/null; then
        # Already rewritten - check if source changed by comparing rewritten version
        tmpfile=$(mktemp)
        cp "$src_file" "$tmpfile"
        bare_module=$(echo "$rel" | sed 's|\.agda$||; s|/|.|g')
        new_module="formalization.Library.$bare_module"
        sed -i "s|^module ${bare_module}|module ${new_module}|" "$tmpfile"
        current_module=$(grep -oP '^module \K[^ ]+' "$tmpfile" | head -1)
        if [ -n "$current_module" ] && [ "$current_module" != "$new_module" ]; then
          sed -i "s|^module ${current_module}|module ${new_module}|" "$tmpfile"
        fi
        rewrite_imports "$tmpfile"
        apply_fixes "$tmpfile"

        if ! diff -q "$tmpfile" "$dst_file" > /dev/null 2>&1; then
          echo "UPDATE: $rel (source changed)"
          copy_and_rewrite "$rel"
        fi
        rm -f "$tmpfile"
      else
        echo "SKIP (local mods): $rel"
      fi
    fi
  else
    echo "NEW: $rel"
    copy_and_rewrite "$rel"
  fi
done

# Clean up stale .agdai files
find "$DST" -name "*.agdai" -delete 2>/dev/null

echo "Sync complete."
