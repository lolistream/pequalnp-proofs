# Formula sizes for all 3×5 one-hot relations

The atlas covers all **32,768** binary relations on `Fin 3 × Fin 5`. A formula starts with the three row indicators and five column indicators. Its internal nodes are binary AND or OR, with no NOT or free constants. Raw input occurrences may repeat. `formula-atlas.json.gz` records a minimum **tree** size and a reconstructible formula for each relation, indexed by its row-major 15-bit truth mask. Identical subexpressions may be shared when emitting a circuit: its size may be **smaller** than the listed tree cost. A tree lower bound does not automatically apply to circuits with sharing.

`solve.py` solves the layers up to the requested cost using row/column relabelings. `verify.py` recomputes all layers **without symmetry**, checks the size of every mask and the truth function of every stored predecessor, and checks the example for mask 3239. Its largest minimum tree size is 11. The circuit lower bounds for masks 1091 and 3239 are proved separately in the parent directory.

```bash
python3 -I verify.py
python3 -I solve.py 1091 3239 --max-gates 11 --use-atlas
```

The second command writes a `candidate-<mask>.json` next to the solver for each result within the requested budget. To recompute the atlas from scratch in a new directory, copy `solve.py` there and run `python3 -I solve.py 3239 --max-gates 11 --write-atlas`.
