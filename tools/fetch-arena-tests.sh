#!/usr/bin/env bash
# Compatibility entry point; the Node implementation reads structured metadata
# and discovers nested static tests at a pinned upstream revision.
set -euo pipefail
cd "$(dirname "$0")/.."
exec node tools/fetch-arena-tests.js "$@"
