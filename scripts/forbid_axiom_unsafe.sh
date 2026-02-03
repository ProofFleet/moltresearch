#!/usr/bin/env bash
set -euo pipefail

# forbid axiom/unsafe in verified targets
# (can be refined later)

grep -RIn --line-number -E "^[[:space:]]*(axiom|unsafe)" MoltResearch Solutions && {
  echo "ERROR: found axiom/unsafe in verified targets" >&2
  exit 1
} || true
