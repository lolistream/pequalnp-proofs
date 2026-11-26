# Exact 3×5 monotone circuit sizes

**Every one of the 32,768 labeled 3×5 relations has a one-hot AND/OR circuit with at most nine gates. Exactly 7,770 require nine.** This is a finite result for single-output circuits on a promise, not a result about unrestricted Boolean functions or P versus NP.

The [table](atlas.json) gives 190 representatives up to independent row/column relabeling, an optimal witness for each, and its multiplicity. The checker reconstructs a witness for **any** 15-bit mask. Bit `5*u+v` of the mask is the required output on the pair `(u,v)`. Input wires 0–2 specify the selected row; 3–7 specify the selected column. Gate `j` writes wire `8+j`. Only AND and OR, fan-in at most two, are allowed; a wire may be reused arbitrarily. Costs count gates, not wires. For the two constants only: under the project's semantics an out-of-range output is false (zero gates); an empty AND is true (one gate).

| Minimum gates | Classes up to relabeling | Labeled relations |
|---:|---:|---:|
| 0 | 3 | 9 |
| 1 | 5 | 44 |
| 2 | 7 | 190 |
| 3 | 11 | 605 |
| 4 | 17 | 1,500 |
| 5 | 24 | 3,180 |
| 6 | 30 | 5,460 |
| 7 | 39 | 6,150 |
| 8 | 26 | 7,860 |
| 9 | 28 | 7,770 |
| **Total** | **190** | **32,768** |

Compared with the [formula-tree atlas](../formula-atlas), sharing a computed wire strictly improves the best formula for **4,050 nonconstant labeled masks**: 3,510 save one gate and 540 save two. The 540 double savings come from two isomorphism classes (representatives 3518 and 7548): size 11 as trees, size 9 as circuits. The two constant masks are excluded from this comparison because the tree atlas starts with raw inputs and no free constants.

## What verifies what

- **Witnesses and coverage:** [`check.py`](check.py) evaluates every witness on all 15 inputs after each of the 720 row/column permutations. It checks that the orbits have the claimed sizes, are disjoint, and together cover every mask. Relabeling raw input wires preserves size in both directions (use the inverse permutation); fanout is unchanged. The table covers all masks, not only examples sampled from the project's queue.
- **Lower bounds:** the [C++ checker](frontier.cc) and a [separate Python implementation](audit_lowers.py) searched for a smaller circuit for **every representative**, not only cases where the tree and circuit bounds differ. Neither trusts the supplied formula sizes when replaying the lower bounds. The full Python audit reported 190 classes, 40,338 input supports, 540,016 visited states, and zero counterexamples. A time-limited or partial C++ run does not pass the verifier.
- **Lean, universal bound:** [`SharpBound.lean`](SharpBound.lean) proves `PEqualNP.Rep35Atlas.sharp_uniform_bound`: for any natural `s`, `(∀ A : Fin 3 → Fin 5 → Bool, RepSizeAtMost A s) ↔ 9 ≤ s`. This is a theorem about **every labeled relation**, not just about the entries in a finite list. [`RepresentativeUpperBounds.lean`](RepresentativeUpperBounds.lean) certifies all 190 circuits. [`RepresentativeOrbitCoverage.lean`](RepresentativeOrbitCoverage.lean) proves that every Boolean matrix is a relabeling of some listed mask, using the 792 possible sorted multisets of column types. [`RepSizePerm.lean`](RepSizePerm.lean) proves that row and column permutations preserve the minimum size (for arbitrary dimensions). [`WorstCase.lean`](WorstCase.lean) proves the matching obstruction for mask **7549** by specializing the finite-word argument from upstream `PEqualNP.Outside.L_meta_5473`. The kernel-checked sharp theorem depends only on the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
- **Lean, all individual optima:** [`ExactClassification.lean`](ExactClassification.lean) proves both directions for **all 190 catalogue entries** (`entry_budget_iff`), then transfers them to **every labeled relation** (`exact_classification`). For an arbitrary `A : Fin 3 → Fin 5 → Bool`, it produces a catalogue entry `e` and relabelings under which `A` has precisely that adjacency table; a circuit for `A` fits budget `s` if and only if `e.budget ≤ s`, and `repSize A` equals the entry’s budget. Querying the compiled theorem with `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. It does not assume the results of the C++ or Python search.
- **How the last 86 were certified:** the full theorem reuses the [previous 104 checked entries](SelectedOptima.lean). The [additional lower-bound modules](lower-certificates) cover the rest. The smaller cases use ordinary kernel reduction. For cases where one reduction exceeded memory limits, [`AtlasCut.lean`](lower-certificates/AtlasCut.lean) verifies that no admissible first transition has been omitted; the continuations are discharged by separate kernel-checked lemmas. On the three largest split proofs, another cut is used only for individual branches that needed it. The final module checks that each catalogue pair actually occurs in the proved blocks. A timeout, incomplete search or generated table without a proof is never used as evidence.
- **Lean, labeled counts:** [`exact_histogram`](LabeledHistogram.lean#L54) counts the Boolean relations themselves, not representatives or circuit descriptions. [`exactly_nine`](LabeledHistogram.lean#L75) proves `Nat.card {A : Fin 3 → Fin 5 → Bool // repSize A = 9} = 7770`; `count_above_nine` gives zero for every larger size. For each representative the proof [checks permutations fixing its adjacency table](HistogramFixers.lean) and [bounds its orbit](HistogramOrbits.lean). These upper bounds sum to 32,768. Since the orbits already cover all 32,768 relations, [the counting lemma](HistogramCounting.lean) makes the bound exact in each size class: any overcount would leave some relation uncovered. The kernel audit of the histogram reports only `propext`, `Classical.choice` and `Quot.sound`. The separate comparison with formula-tree costs remains an executable count.

## Why the exhaustive lower-bound search is complete

For a nonconstant target, constants and copy gates can be propagated, repeated operands simplified, and unused gates dropped. Equal-valued wires on the promise can be merged into the earlier wire. This never increases gate count. A connected output cone with `k` binary gates can depend on at most `k+1` distinct raw inputs: at least `k−1` of its `2k` operand slots connect gates to one another. The two constants and the zero-gate raw projections are handled separately.

Start with each candidate support of size ≤`k+1`. Track the full 15-bit truth columns of its live wires. At each gate choose any two live wires, intersect or unite them, and independently decide which operands to retain for later gates. A trimmed circuit is represented by retaining each operand exactly until its last use. If it starts with `n` wires, uses `b` binary gates, retains operands `r` additional times, and finishes with one wire, then `n−b+r=1`, giving the upper bound `r≤k+1−n`. Both searches check the target before discarding a state. They can prune a frontier only when a resource constraint fails, it duplicates an equivalent search state, or when some positive/negative pair no longer has a live wire that is 1 on the positive and 0 on the negative. Without such a wire, monotonicity forbids separating the pair later. The C++ implementation uses explicit remaining retentions; the Python implementation carries the depth and the live set. Neither imposes a tree-only restriction.

## Reproduce

From this directory, using Python 3 and a C++17 compiler:

```bash
python3 -I check.py                         # all upper bounds and relabelings
python3 -I check.py --query 7548            # JSON witness for an arbitrary labeled mask
python3 -I audit_lowers.py atlas.json       # independent full lower-bound computation
work=$(mktemp -d)
g++ -O3 -std=c++17 -ftrapv -D_GLIBCXX_ASSERTIONS frontier.cc -o "$work/frontier"
python3 -I check.py --frontier "$work/frontier" --seconds 40
```

To reproduce the Lean theorems, from the repository’s `lean/` directory using the pinned Lean and Mathlib versions:

```bash
lake build PEqualNP.Defs
bash ../research-verified/finite-graphs/dag-atlas/check-lean.sh histogram # full classification and exact labeled counts
bash ../research-verified/finite-graphs/dag-atlas/check-lean.sh full      # full classification without the counting modules
bash ../research-verified/finite-graphs/dag-atlas/check-lean.sh sharp    # quicker: only the sharp uniform bound of 9
bash ../research-verified/finite-graphs/dag-atlas/check-lean.sh selected # earlier 104-class subset
```

Each command uses a fresh temporary module directory; no certificates are installed into the project’s Lake build. For `histogram` the final line is `Lean OK: LabeledHistogram`; for `full` it is `Lean OK: ExactClassification`. The full replay is substantially longer than the subset check: it includes all the closed `decide` computations, some of which need several GB of RAM per Lean process. The default is sequential. For a machine with sufficient memory, `ATLAS_JOBS=2` (up to 8) allows independent modules on the same line of [`build-order.txt`](lower-certificates/build-order.txt) to compile concurrently. A nonzero exit means the run has not verified the final theorem.
