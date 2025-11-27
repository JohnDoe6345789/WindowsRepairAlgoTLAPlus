#!/usr/bin/env bash
set -euo pipefail

VERSION="1.8.0"   # pin the version
URL="https://github.com/tlaplus/tlaplus/releases/download/v${VERSION}/tla2tools.jar"
TARGET_DIR="tools"
TARGET_FILE="${TARGET_DIR}/tla2tools.jar"

mkdir -p "${TARGET_DIR}"

if [ ! -f "${TARGET_FILE}" ]; then
    echo "Downloading tla2tools.jar ${VERSION}..."
    curl -fL "${URL}" -o "${TARGET_FILE}.tmp"
    mv "${TARGET_FILE}.tmp" "${TARGET_FILE}"
    chmod 644 "${TARGET_FILE}"
else
    echo "tla2tools.jar already present."
fi
