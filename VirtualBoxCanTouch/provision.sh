#!/bin/bash
# provision.sh - Configure an Arch Linux guest for headless development.
# Run inside the VM (either via cloud-init or manually via SSH).
# Idempotent: safe to re-run.

set -euo pipefail

# ── Helpers ──────────────────────────────────────────────────────────────────

log() { echo -e "\n==> $*"; }
ok()  { echo "    ... done"; }

need_root() {
    if [ "$(id -u)" -ne 0 ]; then
        echo "Error: provision.sh must be run as root (use sudo)."
        exit 1
    fi
}

TARGET_USER="${1:-prison}"
TARGET_HOME="/home/$TARGET_USER"

need_root

# ── 1. System update ────────────────────────────────────────────────────────

log "Updating system packages"
pacman -Syu --noconfirm
ok

# ── 2. Install packages ─────────────────────────────────────────────────────

log "Installing packages"
pacman -S --noconfirm --needed \
    base-devel git openssh zsh \
    neovim \
    stack \
    htop rsync wget curl \
    ttf-hack-nerd \
    man-db man-pages
ok

# Install virtualbox-guest-utils-nox only if we're inside VirtualBox
# and no variant is already installed
if systemd-detect-virt -q 2>/dev/null && [ "$(systemd-detect-virt)" = "oracle" ]; then
    log "Detected VirtualBox - installing guest utilities"
    if pacman -Qi virtualbox-guest-utils &>/dev/null; then
        echo "    virtualbox-guest-utils (with X11) already installed, skipping."
    elif pacman -Qi virtualbox-guest-utils-nox &>/dev/null; then
        echo "    virtualbox-guest-utils-nox already installed, skipping."
    else
        pacman -S --noconfirm --needed virtualbox-guest-utils-nox
    fi
    systemctl enable --now vboxservice.service || true
    modprobe vboxsf 2>/dev/null || true
    ok
fi

# ── 3. Keyboard (no dead keys!) ─────────────────────────────────────────────

log "Setting keyboard layout to 'us' (no dead keys)"
echo 'KEYMAP=us' > /etc/vconsole.conf
ok

# ── 4. Locale ────────────────────────────────────────────────────────────────

log "Configuring locale (en_US.UTF-8 + sv_SE.UTF-8)"
sed -i 's/^#en_US.UTF-8 UTF-8/en_US.UTF-8 UTF-8/' /etc/locale.gen
sed -i 's/^#sv_SE.UTF-8 UTF-8/sv_SE.UTF-8 UTF-8/' /etc/locale.gen
locale-gen

cat > /etc/locale.conf << 'EOF'
LANG=en_US.UTF-8
LC_ADDRESS=sv_SE.UTF-8
LC_IDENTIFICATION=sv_SE.UTF-8
LC_MEASUREMENT=sv_SE.UTF-8
LC_MONETARY=sv_SE.UTF-8
LC_NAME=sv_SE.UTF-8
LC_NUMERIC=sv_SE.UTF-8
LC_PAPER=sv_SE.UTF-8
LC_TELEPHONE=sv_SE.UTF-8
LC_TIME=sv_SE.UTF-8
EOF
ok

# ── 5. SSH hardening ────────────────────────────────────────────────────────

log "Configuring SSH (key-based auth only, no passwords)"
SSHD_CONF="/etc/ssh/sshd_config"

# Disable password authentication
sed -i 's/^#\?PasswordAuthentication .*/PasswordAuthentication no/' "$SSHD_CONF"
sed -i 's/^#\?KbdInteractiveAuthentication .*/KbdInteractiveAuthentication no/' "$SSHD_CONF"

systemctl enable --now sshd
systemctl restart sshd
ok

# ── 6. User setup ───────────────────────────────────────────────────────────

log "Setting up user '$TARGET_USER'"

# Ensure user exists
if ! id "$TARGET_USER" &>/dev/null; then
    useradd -m -G wheel -s /usr/bin/zsh "$TARGET_USER"
fi

# Add to vboxsf group if it exists
if getent group vboxsf &>/dev/null; then
    usermod -aG vboxsf "$TARGET_USER"
fi

# Set zsh as default shell
chsh -s /usr/bin/zsh "$TARGET_USER"

# Ensure sudoers allows wheel group
if ! grep -q '^%wheel ALL=(ALL:ALL) NOPASSWD: ALL' /etc/sudoers; then
    echo '%wheel ALL=(ALL:ALL) NOPASSWD: ALL' >> /etc/sudoers
fi
ok

# ── 7. Zsh config ───────────────────────────────────────────────────────────

log "Setting up zsh configuration"
ZSHRC="$TARGET_HOME/.zshrc"
if [ ! -f "$ZSHRC" ]; then
    cat > "$ZSHRC" << 'ZSHEOF'
# Prompt
autoload -Uz promptinit && promptinit
PROMPT='%F{green}%n@%m%f:%F{blue}%~%f %# '

# History
HISTFILE=~/.zhistory
HISTSIZE=10000
SAVEHIST=10000
setopt appendhistory sharehistory hist_ignore_dups

# Completion
autoload -Uz compinit && compinit
zstyle ':completion:*' menu select

# Key bindings
bindkey -e

# Aliases
alias ls='ls --color=auto'
alias ll='ls -lah'
alias vi='nvim'
alias vim='nvim'

# PATH
export PATH="$HOME/.local/bin:$PATH"
ZSHEOF
    chown "$TARGET_USER:$TARGET_USER" "$ZSHRC"
fi
ok

# ── 8. Neovim plugin manager ────────────────────────────────────────────────

log "Installing vim-plug for Neovim"
PLUG_DIR="$TARGET_HOME/.local/share/nvim/site/autoload"
if [ ! -f "$PLUG_DIR/plug.vim" ]; then
    sudo -u "$TARGET_USER" mkdir -p "$PLUG_DIR"
    curl -fsSL -o "$PLUG_DIR/plug.vim" \
        https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim
    chown "$TARGET_USER:$TARGET_USER" "$PLUG_DIR/plug.vim"
fi
ok

# ── 9. Shared folder mount points ───────────────────────────────────────────

log "Creating shared folder mount points"
# VirtualBox automounts shared folders to /media/sf_<name>
# We also create symlinks in the home directory for convenience
mkdir -p /media

# The nvim config shared folder
if [ -d /media/sf_nvimConfig ] || true; then
    sudo -u "$TARGET_USER" mkdir -p "$TARGET_HOME/.config"
    # Symlink will be created when the shared folder is actually mounted
    if [ -d /media/sf_nvimConfig ] && [ ! -L "$TARGET_HOME/.config/nvim" ]; then
        ln -sf /media/sf_nvimConfig "$TARGET_HOME/.config/nvim"
    fi
fi

# The Cubical library shared folder
if [ -d /media/sf_Cubical ] || true; then
    mkdir -p /Cubical
    if [ -d /media/sf_Cubical ] && [ ! -L /Cubical ]; then
        # Symlink /Cubical -> /media/sf_Cubical for compatibility
        rmdir /Cubical 2>/dev/null || true
        ln -sf /media/sf_Cubical /Cubical
    fi
fi
ok

# ── 10. Agda configuration ──────────────────────────────────────────────────

log "Setting up Agda library configuration"
sudo -u "$TARGET_USER" mkdir -p "$TARGET_HOME/.agda"
cat > "$TARGET_HOME/.agda/libraries" << 'EOF'
/Cubical/cubical.agda-lib
EOF
chown -R "$TARGET_USER:$TARGET_USER" "$TARGET_HOME/.agda"

# MountAgdaI.sh - writable overlay for Cubical _build directory
cat > "$TARGET_HOME/MountAgdaI.sh" << 'MOUNTEOF'
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
MOUNTEOF
chmod +x "$TARGET_HOME/MountAgdaI.sh"
chown "$TARGET_USER:$TARGET_USER" "$TARGET_HOME/MountAgdaI.sh"
ok

# ── 11. Install Claude Code ─────────────────────────────────────────────────

log "Installing Claude Code CLI"
if [ ! -f "$TARGET_HOME/.local/bin/claude" ]; then
    sudo -u "$TARGET_USER" bash -c 'curl -fsSL https://claude.ai/install.sh | sh'
else
    echo "    Claude Code already installed, skipping."
fi
ok

# ── 12. Summary ──────────────────────────────────────────────────────────────

log "Provisioning complete!"
cat << 'SUMMARY'

    ┌─────────────────────────────────────────────────────────┐
    │                   SETUP COMPLETE                        │
    │                                                         │
    │  Next steps:                                            │
    │                                                         │
    │  1. Authenticate Claude Code (first time only):         │
    │     $ claude setup-token                                │
    │     (paste the token from your browser)                 │
    │                                                         │
    │  2. Start Claude Code:                                  │
    │     $ claude                                            │
    │                                                         │
    │  3. If using Cubical Agda, mount the writable overlay:  │
    │     $ sudo ~/MountAgdaI.sh                              │
    │                                                         │
    │  Clipboard: OSC 52 works automatically if your          │
    │  terminal supports it (kitty, alacritty, foot,          │
    │  iTerm2, Windows Terminal).                              │
    └─────────────────────────────────────────────────────────┘

SUMMARY
