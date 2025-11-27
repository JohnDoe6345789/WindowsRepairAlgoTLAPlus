#!/usr/bin/env bash
set -euo pipefail

MODULE=${1:-STLRepairAlgo}
CFG=${2:-models/STLRepairAlgo.cfg}

scripts/bootstrap.sh

mkdir -p ci-results

LOG_FILE="ci-results/${MODULE}.tlc.log"

# Capture TLC output to a log file, while still showing it in CI output
java -cp tools/tla2tools.jar tlc2.TLC -config "${CFG}" "spec/${MODULE}.tla" \
  2>&1 | tee "${LOG_FILE}"
