#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
mkdir -p .tools
if ! command -v elan >/dev/null && [[ ! -x .tools/elan/bin/elan ]]; then
  curl -fsSL --retry 3 https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    -o .tools/elan-init.sh
  ELAN_HOME="$project_root/.tools/elan" sh .tools/elan-init.sh \
    -y --no-modify-path --default-toolchain none
fi
bash scripts/lake.sh exe cache get
