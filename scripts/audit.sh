#!/bin/sh
set -eu

project_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
project_elan_home=${ELAN_HOME:-"$HOME/.elan"}
if [ -d "$project_elan_home/bin" ]; then
  PATH="$project_elan_home/bin:$PATH"
  export PATH
fi
exec python3 "$project_root/scripts/audit.py" "$@"
