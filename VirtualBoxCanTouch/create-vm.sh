#!/bin/bash
# create-vm.sh - Create a headless Arch Linux VM for development.
#
# This script:
#   1. Downloads the official Arch Linux cloud image
#   2. Creates a VirtualBox VM with NAT + SSH port forwarding
#   3. Uses cloud-init for initial OS configuration
#   4. Runs provision.sh inside the VM to install dev tools
#
# Prerequisites: VirtualBox, qemu-img, mkisofs/genisoimage/xorriso, curl
# Usage: ./create-vm.sh

set -euo pipefail

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Configuration - edit these for your laptop
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

VM_NAME="ArchDev"
VM_RAM=2048          # MB - lower to 1024 if laptop is very weak
VM_CPUS=2            # Number of CPU cores
VM_DISK_SIZE=20480   # MB (20 GB)
SSH_PORT=2222        # Host port forwarded to guest SSH (port 22)
VM_USER="prison"     # Username inside the VM

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Derived paths
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CACHE_DIR="$SCRIPT_DIR/cache"
CLOUD_IMG_URL="https://geo.mirror.pkgbuild.com/images/latest/Arch-Linux-x86_64-cloudimg.qcow2"
CLOUD_IMG="$CACHE_DIR/arch-cloudimg.qcow2"
VM_DIR="$SCRIPT_DIR/vm"
VM_DISK="$VM_DIR/$VM_NAME.vdi"
SEED_ISO="$VM_DIR/seed.iso"
SSH_KEY="$SCRIPT_DIR/vm-key"
PROVISION_SCRIPT="$SCRIPT_DIR/provision.sh"
SHARED_FOLDERS_CONF="$SCRIPT_DIR/shared-folders.conf"

# ── Helpers ──────────────────────────────────────────────────────────────────

log()  { echo -e "\n\033[1;34m==> $*\033[0m"; }
ok()   { echo -e "\033[1;32m    ... done\033[0m"; }
err()  { echo -e "\033[1;31mError: $*\033[0m" >&2; exit 1; }
warn() { echo -e "\033[1;33mWarning: $*\033[0m"; }

cleanup_on_error() {
    if [ "${VM_CREATED:-}" = "1" ]; then
        warn "Cleaning up VM '$VM_NAME' due to error..."
        VBoxManage controlvm "$VM_NAME" poweroff 2>/dev/null || true
        sleep 2
        VBoxManage unregistervm "$VM_NAME" --delete 2>/dev/null || true
    fi
}
trap cleanup_on_error ERR

# ── 1. Check dependencies ───────────────────────────────────────────────────

log "Checking dependencies"

MISSING=()
command -v VBoxManage  &>/dev/null || MISSING+=("virtualbox")
command -v qemu-img    &>/dev/null || MISSING+=("qemu-img")
command -v curl        &>/dev/null || MISSING+=("curl")

# Check for any ISO creation tool
MKISO=""
if command -v mkisofs &>/dev/null; then
    MKISO="mkisofs"
elif command -v genisoimage &>/dev/null; then
    MKISO="genisoimage"
elif command -v xorriso &>/dev/null; then
    MKISO="xorriso -as genisoimage"
else
    MISSING+=("cdrtools (provides mkisofs)")
fi

if [ ${#MISSING[@]} -gt 0 ]; then
    echo "Missing dependencies: ${MISSING[*]}"
    echo ""
    echo "Install them with:"
    echo "  sudo pacman -S ${MISSING[*]}"
    echo ""
    read -rp "Install now? [Y/n] " answer
    if [ "${answer,,}" != "n" ]; then
        sudo pacman -S --noconfirm --needed "${MISSING[@]}"
        # Re-detect mkiso tool
        if [ -z "$MKISO" ]; then
            if command -v mkisofs &>/dev/null; then MKISO="mkisofs";
            elif command -v genisoimage &>/dev/null; then MKISO="genisoimage";
            fi
        fi
    else
        err "Cannot continue without dependencies."
    fi
fi
ok

# ── 2. Check if VM already exists ───────────────────────────────────────────

if VBoxManage showvminfo "$VM_NAME" &>/dev/null; then
    warn "VM '$VM_NAME' already exists."
    echo "Options:"
    echo "  1) Delete and recreate"
    echo "  2) Abort"
    read -rp "Choice [1/2]: " choice
    if [ "$choice" = "1" ]; then
        log "Removing existing VM"
        VBoxManage controlvm "$VM_NAME" poweroff 2>/dev/null || true
        sleep 2
        VBoxManage unregistervm "$VM_NAME" --delete 2>/dev/null || true
        ok
    else
        echo "Aborted."
        exit 0
    fi
fi

# ── 3. Generate SSH keypair ─────────────────────────────────────────────────

log "Setting up SSH key"
if [ ! -f "$SSH_KEY" ]; then
    ssh-keygen -t ed25519 -f "$SSH_KEY" -N "" -C "$VM_NAME-vm"
    echo "    Generated new SSH key at $SSH_KEY"
else
    echo "    Using existing SSH key at $SSH_KEY"
fi
SSH_PUB_KEY="$(cat "$SSH_KEY.pub")"
ok

# ── 4. Download Arch cloud image ────────────────────────────────────────────

log "Downloading Arch Linux cloud image"
mkdir -p "$CACHE_DIR"
if [ -f "$CLOUD_IMG" ]; then
    echo "    Using cached image at $CLOUD_IMG"
    echo "    (Delete $CACHE_DIR to force re-download)"
else
    echo "    Downloading from $CLOUD_IMG_URL ..."
    curl -fSL -o "$CLOUD_IMG" "$CLOUD_IMG_URL"
fi
ok

# ── 5. Create VM disk from cloud image ──────────────────────────────────────

log "Creating VM disk"
mkdir -p "$VM_DIR"

# Convert qcow2 -> vdi
qemu-img convert -f qcow2 -O vdi "$CLOUD_IMG" "$VM_DISK"

# Resize to desired size
VBoxManage modifymedium disk "$VM_DISK" --resize "$VM_DISK_SIZE"
echo "    Disk: $VM_DISK ($VM_DISK_SIZE MB)"
ok

# ── 6. Create cloud-init seed ISO ───────────────────────────────────────────

log "Creating cloud-init seed ISO"
SEED_DIR="$(mktemp -d)"

cat > "$SEED_DIR/meta-data" << EOF
instance-id: ${VM_NAME}-001
local-hostname: ${VM_NAME,,}
EOF

cat > "$SEED_DIR/user-data" << EOF
#cloud-config
hostname: ${VM_NAME,,}

users:
  - name: ${VM_USER}
    sudo: ALL=(ALL) NOPASSWD:ALL
    shell: /bin/bash
    ssh_authorized_keys:
      - ${SSH_PUB_KEY}
    groups: wheel

ssh_pwauth: false
disable_root: true

growpart:
  mode: auto
  devices: ['/']
resize_rootfs: true

runcmd:
  - systemctl enable --now sshd
  - echo 'KEYMAP=us' > /etc/vconsole.conf
  - sed -i 's/^#en_US.UTF-8 UTF-8/en_US.UTF-8 UTF-8/' /etc/locale.gen
  - locale-gen
  - echo 'LANG=en_US.UTF-8' > /etc/locale.conf
  - pacman-key --init
  - pacman-key --populate archlinux
EOF

$MKISO -output "$SEED_ISO" -volid cidata -joliet -rock \
    "$SEED_DIR/user-data" "$SEED_DIR/meta-data" 2>/dev/null

rm -rf "$SEED_DIR"
echo "    Seed ISO: $SEED_ISO"
ok

# ── 7. Create VirtualBox VM ─────────────────────────────────────────────────

log "Creating VirtualBox VM '$VM_NAME'"

VBoxManage createvm --name "$VM_NAME" --ostype "ArchLinux_64" --register
VM_CREATED=1

VBoxManage modifyvm "$VM_NAME" \
    --memory "$VM_RAM" \
    --cpus "$VM_CPUS" \
    --nic1 nat \
    --nat-pf1 "ssh,tcp,,$SSH_PORT,,22" \
    --audio-driver none \
    --graphicscontroller vmsvga \
    --vram 16 \
    --boot1 disk \
    --boot2 none \
    --boot3 none \
    --boot4 none \
    --uart1 0x3F8 4 \
    --uart-mode1 disconnected

# SATA controller for the main disk
VBoxManage storagectl "$VM_NAME" --name "SATA" --add sata --controller IntelAhci --portcount 2

VBoxManage storageattach "$VM_NAME" \
    --storagectl "SATA" --port 0 --device 0 \
    --type hdd --medium "$VM_DISK"

# IDE controller for cloud-init ISO
VBoxManage storagectl "$VM_NAME" --name "IDE" --add ide

VBoxManage storageattach "$VM_NAME" \
    --storagectl "IDE" --port 0 --device 0 \
    --type dvddrive --medium "$SEED_ISO"

echo "    RAM: ${VM_RAM}MB, CPUs: ${VM_CPUS}"
echo "    SSH: localhost:${SSH_PORT} -> guest:22"
ok

# ── 8. Add shared folders ───────────────────────────────────────────────────

log "Configuring shared folders"
if [ -f "$SHARED_FOLDERS_CONF" ]; then
    FOLDER_COUNT=0
    while IFS='=' read -r name hostpath; do
        # Skip comments and empty lines
        [[ "$name" =~ ^[[:space:]]*# ]] && continue
        [[ -z "$name" ]] && continue

        name="$(echo "$name" | xargs)"      # trim whitespace
        hostpath="$(echo "$hostpath" | xargs)"

        if [ -z "$hostpath" ]; then
            warn "Skipping folder '$name': no path specified"
            continue
        fi

        if [ ! -d "$hostpath" ]; then
            warn "Skipping folder '$name': path '$hostpath' does not exist"
            continue
        fi

        VBoxManage sharedfolder add "$VM_NAME" \
            --name "$name" --hostpath "$hostpath" --automount
        echo "    + $name -> $hostpath"
        FOLDER_COUNT=$((FOLDER_COUNT + 1))
    done < "$SHARED_FOLDERS_CONF"

    if [ "$FOLDER_COUNT" -eq 0 ]; then
        echo "    No shared folders configured."
        echo "    Edit shared-folders.conf and re-run, or add folders manually."
    fi
else
    echo "    No shared-folders.conf found, skipping."
fi
ok

# ── 9. Start VM ─────────────────────────────────────────────────────────────

log "Starting VM (headless)"
VBoxManage startvm "$VM_NAME" --type headless
ok

# ── 10. Wait for SSH ────────────────────────────────────────────────────────

log "Waiting for SSH to become available (this may take 1-3 minutes)"

SSH_OPTS=(-p "$SSH_PORT" -i "$SSH_KEY" \
    -o StrictHostKeyChecking=no \
    -o UserKnownHostsFile=/dev/null \
    -o LogLevel=ERROR \
    -o ConnectTimeout=5 \
    -o BatchMode=yes)

MAX_WAIT=300  # seconds
ELAPSED=0
while [ $ELAPSED -lt $MAX_WAIT ]; do
    if ssh "${SSH_OPTS[@]}" "$VM_USER@localhost" "echo ok" &>/dev/null; then
        echo ""
        ok
        break
    fi
    echo -n "."
    sleep 5
    ELAPSED=$((ELAPSED + 5))
done

if [ $ELAPSED -ge $MAX_WAIT ]; then
    err "Timed out waiting for SSH. The VM may still be booting.
    Check: VBoxManage showvminfo '$VM_NAME' --machinereadable | grep VMState
    Try again: ssh -p $SSH_PORT -i $SSH_KEY $VM_USER@localhost"
fi

# ── 11. Run provisioning ────────────────────────────────────────────────────

log "Running provisioning script inside VM"

if [ ! -f "$PROVISION_SCRIPT" ]; then
    err "provision.sh not found at $PROVISION_SCRIPT"
fi

# Copy and run provision.sh
scp "${SSH_OPTS[@]}" "$PROVISION_SCRIPT" "$VM_USER@localhost:/tmp/provision.sh"
ssh "${SSH_OPTS[@]}" "$VM_USER@localhost" "sudo bash /tmp/provision.sh $VM_USER"
ok

# ── 12. Eject cloud-init ISO ────────────────────────────────────────────────

log "Ejecting cloud-init seed ISO"
VBoxManage storageattach "$VM_NAME" \
    --storagectl "IDE" --port 0 --device 0 \
    --type dvddrive --medium emptydrive
ok

# ── 13. Done! ────────────────────────────────────────────────────────────────

VM_CREATED=""  # disable error cleanup

cat << EOF

$(tput bold)$(tput setaf 2)
    ┌─────────────────────────────────────────────────────────┐
    │              VM CREATED SUCCESSFULLY!                    │
    └─────────────────────────────────────────────────────────┘
$(tput sgr0)

    VM Name:    $VM_NAME
    SSH:        ssh -p $SSH_PORT -i $SSH_KEY $VM_USER@localhost
    Shortcut:   ./connect.sh

    First time setup (run inside the VM):
      claude setup-token
      (Paste the token you get from https://console.anthropic.com)

    Start/Stop the VM:
      VBoxManage startvm $VM_NAME --type headless
      VBoxManage controlvm $VM_NAME acpipowerbutton

    Add shared folders:
      Edit shared-folders.conf, then:
      VBoxManage sharedfolder add $VM_NAME --name "name" --hostpath "/path" --automount
      (Restart VM after adding folders)

EOF
