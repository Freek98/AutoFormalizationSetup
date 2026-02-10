#!/bin/bash
# SSH into the headless Arch VM with clipboard support.
# Usage:
#   ./connect.sh              # interactive shell
#   ./connect.sh ls -la       # run a command
#   echo "text" | ./connect.sh clip   # copy text to VM clipboard (if xclip installed)

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SSH_KEY="$SCRIPT_DIR/vm-key"
SSH_PORT=2222
VM_USER="prison"
VM_HOST="localhost"

if [ ! -f "$SSH_KEY" ]; then
    echo "Error: SSH key not found at $SSH_KEY"
    echo "Run ./create-vm.sh first to generate the key and create the VM."
    exit 1
fi

ssh -p "$SSH_PORT" -i "$SSH_KEY" \
    -o StrictHostKeyChecking=no \
    -o UserKnownHostsFile=/dev/null \
    -o LogLevel=ERROR \
    "$VM_USER@$VM_HOST" "$@"
