#!/bin/bash
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project=$(CDPATH= cd -- "$here/../../../lean" && pwd)
case ${1:-sharp} in
  sharp) modules=(RepSizePerm RepresentativeOrbitCoverage RepresentativeUpperBounds WorstCase SharpBound);;
  selected) modules=(RepSizePerm RepresentativeUpperBounds WorstCase RepresentativeLowerBounds SelectedOptima);;
  *) printf 'Usage: bash %s [sharp|selected]\n' "$0" >&2; exit 2;;
esac
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
# Keep the proof modules outside the upstream Lake build and import only from this run.
lake -d "$project" env bash -eu -c '
  src=$1; work=$2; shift 2; export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
  for m in "$@"; do
    lean -R "$src" -o "$work/$m.olean" "$src/$m.lean"
    printf "Lean OK: %s\n" "$m"
  done
' _ "$here" "$work" "${modules[@]}"
