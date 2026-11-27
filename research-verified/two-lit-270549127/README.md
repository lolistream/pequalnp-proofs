# Two points lit: mask 270549127 has exact minimum 10

The shared six-wire promise of `L-meta-24992`: input `(i,j)` lights wires `i` and `j` (one wire when `i=j`). The minimum is **10 gates, not 9**. This refutes the posted ≤9 bound with NOT gates, shared wires and singleton inputs all allowed.

- [`Ten24992.lean`](Ten24992.lean) gives a construction of 10 gates, checked on all 36 ordered inputs.
- [`Exact24992.lean`](Exact24992.lean) proves `exact_budget : … ↔ 10 ≤ s` and the exact negation `no_nine` of the posted statement.

## The lower bound

The signed circuit-search argument is adapted from upstream `PEqualNP.Outside.L_meta_1007`; the kernel-checked soundness core is [`SignedSearch.lean`](SignedSearch.lean). [`Case24992.lean`](Case24992.lean) checks that the six input signatures match this mask, that all six wires are essential and that the function is not monotone; it reduces the posted statement to four fixed NOT-count profiles. [`LastInverterCase.lean`](LastInverterCase.lean) proves the four-NOT profile impossible.

Profiles 1–3 range from about 4,000 to 43,000 search states, more than one kernel reduction can take. They are split into **1,099 nodes**: each node is either a complete frontier search with a bounded kernel computation when it is small enough, or a checked first-gate cut whose children are verified below it.

| Level | Modules | Meaning |
|---|---|---|
| common | `SignedSearch`, `Case24992`, `LastInverterCase` | signed soundness, input adapter, four-NOT case |
| 0 | 135 | independent leaf searches, bundled |
| 1–3 | 47 | checked cut unions, bottom up |
| final | `Ten24992`, `Exact24992` | construction, all profiles, exact budget |

Timeouts and failed memory bounds are never used: every module counted here finished with exit code 0 on Lean 4.36.0. The final `#print axioms` audit reports only `propext`, `Classical.choice` and `Quot.sound`.

## Reproduce

From this directory, with the pinned Lean and Mathlib cache built:

```bash
work=$(mktemp -d)
while read -r line; do
  for m in $line; do
    lean -j 1 -M 8000 -R . -o "$work/$m.olean" "$m.lean"
  done
  export LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}"
done < build-order.txt
```

`SignedSearch` and `Case24992` must be built before the cut modules. Each leaf is sized under the kernel memory ceiling; running many at once may exhaust memory. A finished `Exact24992` plus the upper witness settles the exact minimum.
