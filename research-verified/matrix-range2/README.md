# Zero-NOT range of the 3×3 product

**Range 2/16 of L-meta-18919:** at most 44 binary gates in total, 23 through 33 ANDs, and no NOT. All nine entries of the product must be correct for every choice of the eighteen input bits.

Michael S. Paterson, [*Complexity of monotone networks for Boolean matrix product*](https://wrap.warwick.ac.uk/46302/), Warwick Theory of Computation Report CS-RR-002 (July 1974), §5, Theorem 1, proves separate lower bounds of `I*J*K` conjunctions and `I*J*(K−1)` disjunctions in an acyclic binary AND/OR network computing the full `I×K` by `K×J` Boolean product. The proof is for networks, not just formulas or semiring polynomials. The report itself allows constants as an eliminable convenience (§3). See also the [published article](https://doi.org/10.1016/0304-3975(75)90009-2).

The project circuit model permits empty and unary fan-in, repeated wire references, and returns false for wires that do not yet exist. To apply the theorem, scan gates in evaluation order: replace a missing operand by false, an empty AND/OR by true/false, a unary gate by its operand, and equal operands by the same wire. Propagate constants by the Boolean identities. Preserve fanout and map each of the nine designated output wires through the substitutions. Each replacement preserves all nine outputs on every input and never increases either gate count. No output of the matrix product is constant. The remaining network is in Paterson’s model.

At `I=J=K=3`, at least **27 AND** and **18 OR** gates are needed, hence at least **45 in total**. With 23–26 ANDs the conjunction bound already fails. With 27–33 ANDs at most 17 ORs fit under 44. This does not exclude circuits with NOT gates.

[`exclude.py`](exclude.py) checks the exact [public statement](statement.txt), compares the nine target truth columns with Boolean matrix multiplication on all 262,144 inputs, and applies the cited bound to every allowed integer gate count. It is not an exhaustive generator of circuits or a Lean formalization of Paterson’s theorem.

```bash
python3 -I exclude.py statement.txt
```
