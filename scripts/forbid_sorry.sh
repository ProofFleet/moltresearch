#!/usr/bin/env bash
set -euo pipefail

grep -RIn --line-number --exclude-dir=Tasks --exclude-dir=Conjectures "\bsorry\b" MoltResearch Solutions && {
  echo "ERROR: found 'sorry' in verified targets" >&2
  exit 1
} || true
