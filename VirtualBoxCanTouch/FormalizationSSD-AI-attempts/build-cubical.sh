#!/usr/bin/env bash
#
# Build script for the Cubical Agda library.
#
# Layout:
#   /Cubical/              — read-only VirtualBox shared folder (source, updated from host)
#   ~/CubicalBuild/        — local writable copy:
#       cubical.agda-lib   (copied from /Cubical/)
#       Cubical/           (source, rsynced from /Cubical/Cubical/)
#       _build/            (agdai files, generated locally)
#
# When you update the cubical library on the host machine, run:
#   ./build-cubical.sh --sync        # rsync source then rebuild
#
# Usage:
#   ./build-cubical.sh               # build (sync source first)
#   ./build-cubical.sh --sync-only   # just sync source, don't compile
#   ./build-cubical.sh --no-sync     # build without syncing (use existing local source)
#   ./build-cubical.sh --clean       # wipe agdai cache for current Agda version
#

set -euo pipefail

CUBICAL_SRC="/Cubical"
CUBICAL_DIR="$HOME/CubicalBuild"
AGDA_BIN="${AGDA_BIN:-agda}"
AGDA_VERSION=$("$AGDA_BIN" --version | head -1 | grep -oP '[0-9]+\.[0-9]+\.[0-9]+(\.[0-9]+)?')
DO_SYNC=true
SYNC_ONLY=false
CLEAN=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --sync-only) SYNC_ONLY=true; shift ;;
    --no-sync)   DO_SYNC=false; shift ;;
    --clean)     CLEAN=true; shift ;;
    *) echo "Usage: $0 [--sync-only|--no-sync|--clean]"; exit 1 ;;
  esac
done

echo "=== Cubical Library Build ==="
echo "Agda version:  $AGDA_VERSION"
echo "Source (host):  $CUBICAL_SRC/ (read-only shared folder)"
echo "Local copy:     $CUBICAL_DIR/"
echo ""

BUILD_DIR="$CUBICAL_DIR/_build/$AGDA_VERSION"

if $CLEAN; then
  echo "Cleaning agdai cache for Agda $AGDA_VERSION..."
  rm -rf "$BUILD_DIR"
  echo "Done."
  exit 0
fi

# Sync source from shared folder
if $DO_SYNC; then
  if [[ ! -d "$CUBICAL_SRC/Cubical" ]]; then
    echo "ERROR: Cubical source not found at $CUBICAL_SRC/Cubical/"
    exit 1
  fi
  echo "Syncing source from $CUBICAL_SRC/ ..."
  mkdir -p "$CUBICAL_DIR"
  rsync -a --delete --exclude='_build' "$CUBICAL_SRC/Cubical/" "$CUBICAL_DIR/Cubical/"
  cp -f "$CUBICAL_SRC/cubical.agda-lib" "$CUBICAL_DIR/cubical.agda-lib"
  echo "Synced. Local source: $(find "$CUBICAL_DIR/Cubical" -name '*.agda' | wc -l) agda files"
  echo ""
fi

if $SYNC_ONLY; then
  echo "Sync complete (--sync-only). Not compiling."
  exit 0
fi

cd "$CUBICAL_DIR"

# Check existing build
if [[ -d "$BUILD_DIR" ]]; then
  EXISTING_COUNT=$(find "$BUILD_DIR" -name "*.agdai" | wc -l)
  TOTAL_AGDA=$(find Cubical/ -name "*.agda" | wc -l)
  echo "Cached: $EXISTING_COUNT agdai,  Source: $TOTAL_AGDA agda"

  if [[ "$EXISTING_COUNT" -ge "$TOTAL_AGDA" ]]; then
    echo "Library appears fully built. Use --clean to force rebuild."
    exit 0
  fi
  echo "Partial build, continuing..."
else
  echo "No existing build for Agda $AGDA_VERSION."
fi

# Generate Everything.agda
echo ""
echo "Generating Everything.agda..."
{
  printf 'module Everything where\n\n'
  find Cubical/ -type f -name "*.agda" | sort | \
    sed -e 's/\//./g' -e 's/\.agda$//g' -e 's/^/import /'
} > Everything.agda

MODULE_COUNT=$(grep -c '^import ' Everything.agda)
echo "$MODULE_COUNT modules to compile."

echo ""
echo "Compiling (this will take a while)..."

AGDA_OPTS="--safe --cubical --no-import-sorts -WnoUnsupportedIndexedMatch --guardedness"
RTS_OPTS="+RTS -M8G -RTS"

time "$AGDA_BIN" $AGDA_OPTS $RTS_OPTS Everything.agda

RC=$?
if [[ $RC -eq 0 ]]; then
  FINAL_COUNT=$(find "$BUILD_DIR" -name "*.agdai" 2>/dev/null | wc -l)
  echo ""
  echo "=== BUILD SUCCESSFUL ==="
  echo "$FINAL_COUNT agdai files in $BUILD_DIR"
  du -sh "$BUILD_DIR"
else
  echo ""
  echo "=== BUILD FAILED (exit code $RC) ==="
  exit $RC
fi
