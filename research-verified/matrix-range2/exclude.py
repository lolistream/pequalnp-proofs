"""Eliminate the zero-NOT shard of this exact BMM statement using Paterson, Theorem 1.

Source: M. S. Paterson, Complexity of monotone networks for Boolean matrix product,
Warwick CS-RR-002, §5, https://wrap.warwick.ac.uk/46302/ . This is a theorem-based
search-space prune, not an enumeration of all circuits or a Lean proof of Paterson.
Usage: python3 -I exclude.py /path/to/L_meta_18919.lean
"""
import re
import sys
from pathlib import Path

MASK = (1 << (1 << 18)) - 1
A = range(23, 34)  # range 2 of 16; zero NOT, at most 44 total

def main(path):
    proof = Path(path).read_text(encoding='utf-8')
    match = re.search(r'^theorem PEqualNP\.Outside\.L_meta_18919\s*:\s*(.*?)\s*:=\s*by', proof, re.M | re.S)
    if not match:
        raise ValueError('not the expected theorem')
    prefix = '(∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 9 → ℕ), PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 44 ∧ ∀ x : Fin 18 → Bool, '
    rows = [[(3*i+k, 9+3*k+j) for k in range(3)] for i in range(3) for j in range(3)]
    body = ' ∧ '.join('(C.wires (List.ofFn x)).getD (o ' + str(q) + ') false = (' + ' || '.join(f'x {a} && x {b}' for a,b in row) + ')' for q,row in enumerate(rows))
    if ''.join(match[1].split()) != ''.join((prefix+body+')').split()):
        raise ValueError('matrix indexing, arity, gate model or budget changed')

    # Independent semantic check: build the nine full truth columns using the direct
    # Lean expression and by fixing each of the 512 right matrices in turn.
    x = [(MASK // ((1 << (1 << t)) + 1)) << (1 << t) for t in range(18)]
    for o, terms in enumerate(rows):
        i,j = divmod(o,3)
        got = 0
        for a,b in terms:
            got |= x[a] & x[b]
        table = bytearray()
        for b in range(512):
            col = sum(((b >> (3*k+j)) & 1) << k for k in range(3))
            word = sum(bool(((a >> (3*i)) & 7) & col) << a for a in range(512))
            table.extend(word.to_bytes(64,'little'))
        if got != int.from_bytes(table,'little'):
            raise AssertionError(f'wrong matrix output {o}')

    # After removing constant gates, unary copies and invalid wire reads, every
    # qualifying circuit is a Paterson network with NO MORE gates of either kind.
    I, K, J = 3, 3, 3
    min_and, min_or = I*J*K, I*J*(K-1)
    survivors = [a for a in A if a >= min_and and 44-a >= min_or]
    if survivors:
        raise AssertionError(f'not an exhausted shard: {survivors}')
    print('Verified all 9 outputs on all 262144 inputs. Published lower bound: '
          f'{min_and} AND + {min_or} OR. Survivors for 23..33 AND, 0 NOT, total <=44: 0.')

if __name__ == '__main__':
    main(sys.argv[1])
