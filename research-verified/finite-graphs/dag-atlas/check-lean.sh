#!/bin/bash
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project=$(CDPATH= cd -- "$here/../../../lean" && pwd)
jobs=${ATLAS_JOBS:-1}
[[ $jobs =~ ^[1-8]$ ]] || { printf 'ATLAS_JOBS must be in 1..8\n' >&2; exit 2; }
case ${1:-sharp} in
  sharp) groups=('RepSizePerm RepresentativeOrbitCoverage RepresentativeUpperBounds WorstCase' 'SharpBound');;
  selected) groups=('RepSizePerm RepresentativeUpperBounds WorstCase RepresentativeLowerBounds' 'SelectedOptima');;
  full) groups=('RepSizePerm RepresentativeOrbitCoverage RepresentativeUpperBounds WorstCase RepresentativeLowerBounds' 'SelectedOptima')
        while IFS= read -r level; do [[ -z $level ]] || groups+=("$level"); done < "$here/lower-certificates/build-order.txt";;
  *) printf 'Usage: bash %s [sharp|selected|full]\n' "$0" >&2; exit 2;;
esac
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
# Compile in dependency order. Modules on a single line share no dependencies on that line.
lake -d "$project" env bash -eu -c '
  src=$1; work=$2; jobs=$3; shift 3; export src work LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
  build_one() {
    local m=$1 root=$src
    [[ $m =~ ^[A-Za-z][A-Za-z0-9_]*$ ]] || return 2
    if [[ ! -f $root/$m.lean ]]; then root=$src/lower-certificates; fi
    lean -j 1 -R "$root" -o "$work/$m.olean" "$root/$m.lean" || return $?
    printf "Lean OK: %s\n" "$m"
  }
  export -f build_one
  for group in "$@"; do
    read -r -a mods <<< "$group"
    printf "%s\n" "${mods[@]}" | xargs -P "$jobs" -n 1 bash -eu -c '\''build_one "$1"'\'' _
  done
' _ "$here" "$work" "$jobs" "${groups[@]}"
