#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
if [[ -x "$project_root/.tools/elan/bin/lake" ]]; then
  export ELAN_HOME="$project_root/.tools/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
export MATHLIB_CACHE_DIR="$project_root/.tools/mathlib-cache"
exec lake "$@"
