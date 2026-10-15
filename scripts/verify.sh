#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
mkdir -p artifacts
python3 scripts/check_sources.py
bash scripts/lake.sh env lean --version | tee artifacts/lean-version.txt
bash scripts/lake.sh build 2>&1 | tee artifacts/build.log
bash scripts/lake.sh env lean Audit.lean 2>&1 | tee artifacts/axioms.log
python3 scripts/check_axioms.py artifacts/axioms.log
python3 scripts/sanity_check.py | tee artifacts/numerical-check.txt
