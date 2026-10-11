#!/usr/bin/env bash
# Rebuild this project's own Lean artifacts from scratch and audit the axioms of one check file.
# Usage: ./check_fresh.sh [SharpSwitchGap/B5Checks.lean]
# Upstream and Mathlib builds under .lake are kept; only SharpSwitchGap* artifacts are removed.
set -euo pipefail
cd "$(dirname "$0")"
AUDIT="${1:-SharpSwitchGap/B5Checks.lean}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
for dir in .lake/build/lib/lean .lake/build/ir; do
  if [ -d "$dir" ]; then
    find "$dir" -maxdepth 1 -name 'SharpSwitchGap*' -exec rm -rf {} +
  fi
done
start=$(date +%s)
lake build
echo "Fresh lake build: exit 0, $(( $(date +%s) - start )) s"
start=$(date +%s)
lake env lean "$AUDIT"
echo "Axiom audit: exit 0, $(( $(date +%s) - start )) s"
