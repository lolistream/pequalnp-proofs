# Verified circuit results

This branch of the participant’s fork archives reproducible results. It is **not** the project’s list of accepted proofs. The exact proof for the assigned 8×8 graph was submitted in [upstream PR #27287](https://github.com/open-goat/pequalnp-proofs/pull/27287). The intake bot closed it without merging: [another proof, PR #26975](https://github.com/open-goat/pequalnp-proofs/pull/26975), had already been merged.

## Rectangular one-hot graphs: exact minima

Input `(u,v)` has one set bit on each side. For a graph with `m` columns, bit `m*u+v` of the integer mask gives the value for that pair. The gates are monotone AND/OR of fan-in at most two.

| Desk step | Dimensions | Mask | Minimum | Upper bound | Lower bound |
|---|---|---:|---:|---|---|
| L-meta-20396 | 3×4 | 53 | **5**, not 4 | [5-gate witness](finite-graphs/five-53.lean) | [no circuit of size ≤4](finite-graphs/no-four-53.lean) |
| L-meta-20463 | 3×5 | 1091 | **5**, not 4 | [5-gate witness](finite-graphs/five-1091.lean) | [no circuit of size ≤4](finite-graphs/no-four-1091.lean) |
| L-meta-20498 | 3×5 | 3239 | **6**, not 5 | [6-gate witness](finite-graphs/six-3239.lean) | [no circuit of size ≤5](finite-graphs/no-five-3239.lean) |
| L-meta-20743 | 5×5 | 24608768 | **7**, not 6 | [7-gate witness](finite-graphs/seven-24608768.lean) | [no circuit of size ≤6](finite-graphs/no-six-24608768.lean) |
| L-meta-21075 | 4×5 | 106399 | **10**, not 9 | [10-gate witness](finite-graphs/ten-106399.lean) | [no circuit of size ≤9](finite-graphs/no-nine-106399.lean) |
| L-meta-21813 | 4×6 | 275263 | **8**, not 7 | [8-gate witness](finite-graphs/eight-275263.lean) | [no circuit of size ≤7](finite-graphs/no-seven-275263.lean) |

Each minimum in the table has both sides checked by the Lean 4.36.0 kernel. The lower-bound files specialize the finite-word completeness argument and checker from upstream [`L_meta_5473.lean`](../lean/PEqualNP/Outside/L_meta_5473.lean), under the repository’s Apache-2.0 license. The original tasks asked for the opposite inequalities. The results here refute those inequalities; they are **not** upstream PRs claiming to prove them.

In the 4×5 example, deleting its all-true first row leaves the 3×5 mask 3324. The explicit 10-gate construction uses the first row bit directly and shares the `column 0 OR column 1` signal between the last two rows. The proof that nine gates cannot suffice covers **all** permitted circuits, not just circuits with this layout.

A separate [5×5 result for mask 3195660](finite-graphs/mask-3195660) also allows NOT. An 11-gate shared circuit was verified in Lean. For size ≤10 the zero-NOT case has an upstream Lean proof of impossibility; the six positive-NOT profiles have an independent exhaustive computational replay, not a Lean proof.

The [3×5 circuit atlas](finite-graphs/dag-atlas) is now [fully classified in Lean](finite-graphs/dag-atlas/ExactClassification.lean). For every labeled 3×5 Boolean relation, the kernel-certified catalogue provides a representative, independent row/column permutations, and a budget `k` such that a circuit fits budget `s` **if and only if `k ≤ s`**. All **190 of 190** representative minima are certified; the classification covers **all 32,768 relations**, with arbitrary sharing of intermediate wires. [Nine is the least uniform budget](finite-graphs/dag-atlas/SharpBound.lean). The [kernel-checked labeled histogram](finite-graphs/dag-atlas/LabeledHistogram.lean#L54) proves that exactly **7,770 of the 32,768** relations require all nine gates. Compared with the [formula-tree atlas](finite-graphs/formula-atlas), sharing saves a gate on 3,510 nonconstant masks and saves two gates on another 540.

## Shared wires: exactly one or two points lit

For `L-meta-23255` (six points, mask `2115487`), the exact size is **7 gates, not 6**, even with NOT gates allowed. The input for the pair `(i,j)` lights wires `i` and `j`; when `i=j` it lights just one. The [seven-gate construction](two-lit/seven-2115487.lean) checks the project’s proposed upper witness against this promise. The [lower bound](two-lit/no-six-2115487.lean) rules out all circuits of size at most six, including circuits with shared wires and NOT; it specializes the signed finite-word argument from upstream `L_meta_1007`.

A short reason for the obstruction: all six inputs affect the answer. Connecting them requires at least five binary gates, and the target is not monotone. At size six, this leaves one NOT and no spare input use: the live circuit would be a read-once tree. Inputs 0 and 1 each have a change from 0 to 1 that raises the output; each of 2, 3, 4, 5 has one that lowers it. Thus exactly the latter four must lie under the NOT, reaching the rest of the tree through one bit. With 0 and 1 off, singleton 2 is accepted while singletons 4 and 5 are rejected, so that bit must be the same for 4 and 5. Turning on input 0 cannot distinguish them now, but the target accepts `{0,4}` and rejects `{0,5}`.

For `L-meta-23222` (mask `35895` on the same six wires), the exact minimum is also **7 gates**. The [seven-gate witness](two-lit/seven-35895.lean) and the [impossibility of six or fewer](two-lit/no-six-35895.lean) were checked separately by Lean. This is not just a failed formula search: the lower theorem includes arbitrary permitted AND/OR/NOT circuits with sharing. Here input 3 can change the output in both directions: adding it to `{2}` changes false to true, whereas adding it to `{0}` changes true to false. All six inputs are essential, so at size six there would be only five binary gates and one NOT, making the output cone a read-once tree. Such a tree cannot have both polarities for input 3.

## Search ranges: 3×3 Boolean matrix product

- [Range 4: at most eleven ANDs, exactly one NOT](matrix-range4/README.md). A restriction reduces a hypothetical witness to two dot products on nine inputs. All five placements of NOT in the relaxed problem have checked UNSAT certificates. The desk acknowledged `exhausted` for range 4. This is not a Lean proof that no 44-gate circuit exists in every range.
- [Range 2: zero NOTs, from 23 to 33 ANDs](matrix-range2/README.md). Paterson’s exact monotone lower bound rules out **this** range. The script verifies applicability to the target function; it does not claim a new proof of the classical theorem or exclude nonmonotone circuits.

## Other Lean-checked results

- [Triangle on six vertices, ≤45 gates](upper-bounds/triangle-45.lean): a two-gate improvement over the 47-gate witness in upstream [`L_meta_18217.lean`](../lean/PEqualNP/Outside/L_meta_18217.lean). The former target of 36 gates was **not** reached.
- [41-vertex edge function, ≤119 gates](upper-bounds/edge-119.lean): certifies the known construction. The target of 118 was **not** reached.
- [Order-three plane geometry](upper-bounds/plane-geometry.lean) and [completeness of the monotone tests under the stated hypotheses](upper-bounds/monotone-tests.lean): partial results only, **not** a proof of the proposed 50-OR lower bound.

To recheck a Lean file, from the repository’s `lean/` directory with the pinned toolchain and Mathlib cache available:

```bash
lake build PEqualNP.Defs
lake env lean --stdin < ../research-verified/finite-graphs/no-four-1091.lean
lake env lean --stdin < ../research-verified/finite-graphs/five-1091.lean
```

The same commands work with the other paths substituted. None of these results resolves P versus NP.
