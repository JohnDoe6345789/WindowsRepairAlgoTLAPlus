#!/usr/bin/env bash
set -euo pipefail

MODULE=${1:-STLRepairAlgo}
CFG=${2:-models/STLRepairAlgo.cfg}

# Ensure tools are present
scripts/bootstrap.sh

java -cp tools/tla2tools.jar tlc2.TLC -config "${CFG}" "spec/${MODULE}.tla"
