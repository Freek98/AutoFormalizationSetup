#!/bin/bash
# Mount a writable _build overlay for the read-only Cubical Agda library.
# Run after each VM reboot: sudo ~/MountAgdaI.sh

set -e

SRC="/home/prison/CubicalWritable/_build"
DST="/Cubical/_build"

mkdir -p "$SRC"

# Copy existing cache if the writable dir is empty
if [ -z "$(ls -A "$SRC" 2>/dev/null)" ] && [ -d "$DST" ]; then
    echo "Copying existing build cache from $DST ..."
    cp -a "$DST"/* "$SRC"/
fi

# Check if already mounted
if mountpoint -q "$DST" 2>/dev/null; then
    echo "$DST is already bind-mounted."
else
    mount --bind "$SRC" "$DST"
    echo "Bind-mounted $SRC -> $DST"
fi

# Verify
touch "$DST/testwrite" && rm "$DST/testwrite" && echo "OK: $DST is writable."
