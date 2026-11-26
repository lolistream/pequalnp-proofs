# A 5×5 relation with minimum 11 gates

For the one-hot promise, the target is bit `5*u+v` of mask **3195660**. The rows have neighborhoods `{2,3}`, `{3,4}`, `{4}`, `{0}`, `{0,1}`. Desk task L-meta-19528 asks whether allowing NOT permits a circuit of size 10.

**Upper bound: 11**, with 3 AND, 8 OR and no NOT. The [explicit witness](witness11.json) has first computed wire 10 and output 20. Both the [AND/OR proof](monotone11.lean) and the [AND/OR/NOT-model proof](general11.lean) passed Lean 4.36.0. Under the monotone basis, the previously recorded [L-meta-9186](../../../lean/PEqualNP/Outside/L_meta_9186.lean) already rules out ten gates.

**Lower bound with NOT: computational, not kernel-certified.** A separate [exhaustive program](search.cc) covers circuits of size at most ten that use one or more NOT gates. It found no such circuit. Together with the monotone lower bound this establishes an exact minimum of 11, with the negated-gate part resting on the search and its completeness argument, **not** on a Lean refutation of the full desk statement.

## Why the profiles suffice

All row neighborhoods and all column neighborhoods are distinct. If two inputs from one side are absent, those two one-hot choices look identical to the circuit on that side. Thus at least four wires from each side participate. Trim unused gates, constants, copies and duplicate-valued wires in the output cone. Missing operands read false; unary AND/OR are copies, and a NOT with a missing input is constant. These simplifications do not increase size. If no NOT survives, use the monotone result.

For `n` distinct live primary inputs and `h` remaining unary NOT gates, a connected output cone needs at least `n−1` binary gates. In size ten this gives `n ≥ 8` and `1 ≤ h ≤ 11−n`. Fanout is allowed: in a circuit with `B` binary gates the number of operand uses beyond a wire’s last use is exactly `B−n+1`, at most `k=11−n−h`. The search starts with each eligible input support, chooses any AND/OR on two live operands or any NOT on one, and chooses independently which operands remain live. An operand kept for another use consumes one unit of `k`. Every trimmed circuit admits this order, and circuits using fewer than ten gates or fewer retentions need not use up the budget.

Wire values are full 25-bit tables. A frontier where two inputs with different target labels have equal live-wire tuples cannot produce the target later. Equal states can be memoized by their available truth tables, remaining retention budget and remaining NOT budget: the used depth is determined by these values and the live count. Accept immediately if an available wire is the target. A timeout or state cap is reported as **LIMIT**, never as a negative result.

| NOTs `h` | Retentions `k` | Input supports completed | Visited states |
|---:|---:|---:|---:|
| 3 | 0 | 25/25 | 22,579 |
| 2 | 0 | 10/10 | 35,894 |
| 2 | 1 | 25/25 | 528,073 |
| 1 | 0 | 1/1 | 18,907 |
| 1 | 1 | 10/10 | 614,590 |
| 1 | 2 | 25/25 | 3,472,208 |

Each profile independently finished with `UNSAT`, not `LIMIT`. A separate control differing only in the target and output filename reconstructed a shared ten-gate, two-NOT circuit for mask 33415133; its output was replayed on all 25 assignments. The negative result for 3195660 is not evidence about any other mask.

From this directory, reproduce (a `LIMIT` on a slower host is inconclusive; allocate more seconds):

```bash
set -eu
work=$(mktemp -d)
g++ -O3 -std=c++17 -ftrapv -D_GLIBCXX_ASSERTIONS search.cc -o "$work/search"
for profile in '3 0 25' '2 0 10' '2 1 25' '1 0 1' '1 1 10' '1 2 25'; do
  set -- $profile
  "$work/search" "$1" "$2" 150 "$work" > "$work/last"
  grep -F "UNSAT seedsets=$3/$3 " "$work/last"
done
```
