#!/bin/sh
set -eu

project_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_root"

for required in git curl python3; do
  if ! command -v "$required" >/dev/null 2>&1; then
    printf 'Required program not found: %s\n' "$required" >&2
    exit 1
  fi
done

python3 -c 'import sys; sys.version_info >= (3, 11) or sys.exit("Python 3.11 or newer is required.")'
python3 -c 'import sys; from pathlib import Path; sys.path.insert(0, "scripts"); from audit import validate_dependency_pins; validate_dependency_pins(Path.cwd())'

project_elan_home=${ELAN_HOME:-"$HOME/.elan"}
if [ -d "$project_elan_home/bin" ]; then
  PATH="$project_elan_home/bin:$PATH"
  export PATH
fi

if ! command -v elan >/dev/null 2>&1; then
  installer_file=$(mktemp)
  trap 'rm -f "$installer_file"' EXIT HUP INT TERM
  printf '%s\n' 'Installing the official Lean version manager...'
  curl --fail --location --silent --show-error --connect-timeout 20 \
    https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    -o "$installer_file"
  sh "$installer_file" -y --no-modify-path --default-toolchain none
  PATH="$project_elan_home/bin:$PATH"
  export PATH
fi

if ! command -v elan >/dev/null 2>&1; then
  printf '%s\n' 'The version manager installation did not produce an executable elan.' >&2
  exit 1
fi

project_toolchain=$(tr -d '\r\n' < lean-toolchain)
elan toolchain install "$project_toolchain"
lean --version
lake --version

# Resolve the existing lockfile and download compiled Mathlib files without
# replacing its pinned revisions with a dependency upgrade.
lake exe cache get
lake build

printf '%s\n' 'Setup and build succeeded. Verify the manuscript with: sh scripts/audit.sh --terminal'
