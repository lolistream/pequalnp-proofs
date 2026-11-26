#!/bin/bash
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project=$(CDPATH= cd -- "$here/../../../lean" && pwd)
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
# Keep the proof modules outside the upstream Lake build and import only from this run.
lake -d "$project" env bash -eu -c '
  src=$1; work=$2; shift 2; export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
  for m in "$@"; do
    lean -R "$src" -o "$work/$m.olean" "$src/$m.lean"
    printf "Lean OK: %s\n" "$m"
  done
' _ "$here" "$work" RepSizePerm RepresentativeOrbitCoverage RepresentativeUpperBounds WorstCase SharpBound
