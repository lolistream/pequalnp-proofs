"""Minimum monotone *tree* sizes on one-hot Fin 3 × Fin 5, for raw binary gates.
Run: python3 -I solve.py 3239 1091 --max-gates 10 [--write-atlas].
A full atlas may also be queried using --use-atlas; no executable data is loaded.
"""
import argparse
import collections
import gzip
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MAX_MASK = (1 << 15) - 1
ATOM = [sum(1 << p for p in range(15) if (p//5 == i if i < 3 else p%5 == i-3)) for i in range(8)]
ATLAS = ROOT / 'formula-atlas.json.gz'


def permutations():
    # Independent row and column renamings preserve operation and tree cost.
    answer = []
    for cols in itertools.permutations(range(5)):
        c = [sum(1 << cols[j] for j in range(5) if i >> j & 1) for i in range(32)]
        moved = [[val << (5*r) for val in c] for r in range(3)]
        for rows in itertools.permutations(range(3)):
            answer.append(tuple(moved[i] for i in rows))
    return answer


def move(m, p):
    return p[0][m & 31] | p[1][(m >> 5) & 31] | p[2][m >> 10]


def solve(bound):
    # A vector entry is [cost, operator, first, second]; operator -1 denotes an input.
    db = [None] * (MAX_MASK + 1)
    levels = [ATOM.copy()]; representatives = [[ATOM[0], ATOM[3]]]
    for i, m in enumerate(ATOM): db[m] = (0, -1, i, 0)
    perms = permutations()
    for cost in range(1, bound+1):
        layer, reps = [], []
        for i in range((cost-1)//2+1):
            j = cost-1-i
            # For any left/right pair, rename the left formula to its orbit representative;
            # the renamed right formula is still one of ALL masks in levels[j].
            for left in representatives[i]:
                for right in levels[j]:
                    for op, result in enumerate((left & right, left | right)):
                        if db[result] is not None: continue
                        reps.append(result)
                        for p in perms:
                            w = move(result, p)
                            if db[w] is None:
                                a, b = move(left, p), move(right, p)
                                assert db[a][0] == i and db[b][0] == j
                                db[w] = (cost, op, a, b)
                                layer.append(w)
        levels.append(layer); representatives.append(reps)
        if sum(map(len, levels)) == len(db): break
    return db


def witness(db, mask):
    gates = []; shared = {}; constructed = {}
    def visit(m):
        if m in constructed: return constructed[m]
        cost, op, a, b = db[m]
        if op == -1:
            assert cost == 0 and ATOM[a] == m
            return a
        assert cost == 1+db[a][0]+db[b][0]
        assert ((a & b) if op == 0 else (a | b)) == m
        qa, qb = visit(a), visit(b)
        key = ('or' if op else 'and', *sorted((qa,qb)))
        if key not in shared:
            shared[key] = 8+len(gates); gates.append(key)
        constructed[m] = shared[key]
        return constructed[m]
    out = visit(mask)
    return {'rows':3, 'cols':5, 'gates':gates, 'output':out}


def verify(c, mask):
    assert (c['rows'], c['cols']) == (3,5) and 0 <= c['output'] < 8+len(c['gates'])
    for u in range(3):
        for v in range(5):
            val = [i==u for i in range(3)]+[j==v for j in range(5)]
            for op,a,b in c['gates']:
                assert op in ('and','or') and 0 <= a < len(val) and 0 <= b < len(val)
                val.append(val[a] & val[b] if op == 'and' else val[a] | val[b])
            assert val[c['output']] == bool((mask >> (5*u+v)) & 1)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('masks', nargs='+', type=lambda s:int(s,0))
    ap.add_argument('--max-gates', type=int, default=6)
    ap.add_argument('--write-atlas', action='store_true')
    ap.add_argument('--use-atlas', action='store_true')
    args = ap.parse_args()
    if args.max_gates < 0 or any(m < 0 or m > MAX_MASK for m in args.masks):
        ap.error('gate bound must be nonnegative; each mask must be in 0..32767')
    if args.use_atlas:
        with gzip.open(ATLAS, 'rt') as f: db = json.load(f)
        if len(db) != 32768 or any(row is None for row in db): ap.error('invalid or incomplete atlas')
    else: db = solve(args.max_gates)
    hist = collections.Counter(a[0] for a in db if a is not None)
    print('tree counts by size', dict(sorted(hist.items())), 'covered', sum(hist.values()))
    if args.write_atlas:
        if sum(hist.values()) != len(db): ap.error('write an atlas only after covering all masks')
        # Store according to increasing truth-mask index, so future queries are array lookups.
        with gzip.open(ATLAS, 'wt') as f: json.dump(db,f,separators=(',',':'))
        print('complete atlas', ATLAS)
    for m in args.masks:
        if db[m] is None or db[m][0] > args.max_gates:
            print(m, 'no tree within the requested budget (not a DAG lower bound)'); continue
        c = witness(db,m); verify(c,m)
        path = ROOT / f'candidate-{m}.json'
        path.write_text(json.dumps(c,separators=(',',':'))+'\n')
        print(m, 'minimum tree size', db[m][0], 'actual DAG gates',len(c['gates']), 'verified 15/15',path)

if __name__ == '__main__': main()
