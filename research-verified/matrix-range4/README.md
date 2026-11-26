# One-NOT, at most eleven-AND range of the 3×3 product

**Result for L-meta-18919, range 4/16.** There is no circuit computing all nine entries of the 3×3 Boolean matrix product with exactly one NOT and at most eleven ANDs. The conclusion even allows free ORs, so the additional 44-total-gate limit does not help. This is a mathematical restriction with independently checked finite UNSAT certificates, not a Lean formalization of the restriction argument or an exclusion of every 44-gate circuit.

1. Each output has a two-bit assignment on which it alone is true. Flatten its final OR network, stopping at inputs, constants, ANDs, or the unique NOT. Each boundary wire is bounded above by this output on every input. No raw input can appear nontrivially, as the output vanishes on all singleton assignments. The NOT sees a monotone prefix: its result is either true at the all-zero input or identically false, so it cannot give a nonzero term. Therefore each output has a boundary AND firing on its private pair. These nine ANDs are distinct.
2. Retain only one row of the left matrix and two columns of the right; set everything else to zero. Seven outputs vanish, so their seven distinct boundary ANDs can be replaced everywhere by zero. With eleven ANDs originally, at most four remain for two three-term dot products `a·b, a·c` on nine bits. Gate sharing is allowed.
3. Collapse every intervening OR circuit to an arbitrary OR of selected earlier sources, allowing constants. Enumerate the five positions of NOT among four ANDs; unused gates allow all smaller cases. Each input of each special gate and each output independently chooses any subset of earlier sources. Already on 204 of the 512 input assignments, no choice yields the required outputs. A contradiction on this subset excludes any circuit correct on the entire cube.

| Order | Required input rows | RUP clause additions verified |
|---|---:|---:|
| NAAAA | 204 | 98,033 |
| ANAAA | 204 | 85,992 |
| AANAA | 204 | 50,241 |
| AAANA | 204 | 31,525 |
| AAAAN | 204 | 30,773 |

The [generator](matmul-free.py) builds the five CNFs and calls CaDiCaL. Its SHA-256, `5b3db43daca8e512f429be1558bac04a5927aadb5ad56eb2f9d2299331dc2d9d`, is the hash reported to the desk. An independent [RUP checker](check-lrat.py) verified each trace down to the empty clause. To replay the saved formulas and certificates, from this directory:

```bash
work=$(mktemp -d)
tar -xzf certificates.tar.gz -C "$work"
python3 -I check-lrat.py "$work"/*.lrat
```

`certificates.tar.gz` SHA-256: `4843b3c8430eb11b42434a234482481bf1bc5c8bb6ccc445307afab3974d6954`. The unchanged historical generator uses the absolute path of the original Lean 4.36.0 installation to find CaDiCaL. To regenerate elsewhere, copy the generator to an empty directory and substitute the absolute path of your own LRAT-capable CaDiCaL binary. Run `python3 -I matmul-free.py ORDER 100 small` for each order above, then replay with `check-lrat.py`. No SAT solver is needed to check the published certificates.
