# Two points lit: mask 100268 has exact minimum 10

For `L-meta-24746`, the input for the pair `(i,j)` lights the six input wires `i` and `j` (one wire when `i=j`). The exact monotone size of the function with mask `100268` is **10 gates, not 9**, proved with the full project semantics: arbitrary AND/OR gates of fan-in two, shared wires, and NOT gates.

- [`ten-100268.lean`](ten-100268.lean) proves `∃ C, FanInTwo C ∧ C.size ≤ 10 ∧ …` on all 36 ordered inputs.
- [`NoNine100268.lean`](NoNine100268.lean) proves `¬ has 9` for the same statement. `has 9` is given literally by the desk's L-meta-24746 statement.

## How the lower bound is checked

The signed live-wire argument is adapted from upstream `PEqualNP.Outside.L_meta_1007`: soundness is in [`SignedSearch.lean`](SignedSearch.lean), which reduces the problem to finitely many `Live` derivations (`Impossible k t s`). Circuit normalization shows every at-most-nine-gate circuit yields either a monotone derivation (excluded by a finite search with no inversions) or one with one to four inversions (`four_profiles`). The zero-inversion and four-inversion profiles are closed inside `SignedSearch.lean` by kernel evaluation; a `#print axioms` audit reports only `propext`, `Classical.choice` and `Quot.sound`.

The remaining three profiles are proved by two layers of independently checked cuts:

| Layer | Modules | What is proved |
|---|---|---|
| 1 | `Second*.lean` (80) | 576 distinct residual states are impossible by the signed frontier search |
| 2 | `Ob*.lean` (16 heavier ones over a second-gate cut) | the 16 first-gate contexts that were too large for one kernel reduction |
| 3 | `Ob*.lean` (116 lighter ones) | the remaining first-gate contexts, one kernel search each |
| 4 | `Profile1..3.lean` | each profile fails at its first gate |
| 5 | `NoNine100268.lean` | `¬ has 9` |

Approx. 500 KB of sources; every module was accepted by Lean 4.36.0 during construction. To replay everything from scratch, from the repository's `lean/` directory with the pinned toolchain and Mathlib cache:

```bash
lake build PEqualNP.Defs
work=$(mktemp -d)
while read -r line; do
  for m in $line; do
    lean -j 1 -M 8000 -R . -o "$work/$m.olean" "$m.lean"
  done
  export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
done < build-order.txt
```

Some `Ob*.lean`/`Second*.lean` modules are deliberately sized just under the kernel's memory ceiling; run them one at a time (as above) if `ATLAS_JOBS`-style parallelism exhausts memory. A timeout or memory stop is not evidence; only a completed build is.
