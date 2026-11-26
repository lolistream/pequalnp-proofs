#!/usr/bin/env python3
"""Independently check all 3x5 one-hot monotone binary-DAG lower bounds.

Usage: python3 -I audit_lowers.py atlas.json [--result audit.json]
Only 'mask', 'size', and (for the separate orbit audit) 'orbit' are read.
No claimed support, formula bound, upper witness, or other search is used.
"""
import argparse
from collections import Counter
from itertools import combinations, permutations
import json
from pathlib import Path

ROWS, COLS = 3, 5
CELLS = range(ROWS * COLS)
FULL = (1 << (ROWS * COLS)) - 1
INPUTS = tuple([sum(1 << (COLS*r+c) for c in range(COLS)) for r in range(ROWS)] +
               [sum(1 << (COLS*r+c) for r in range(ROWS)) for c in range(COLS)])


def orbit_audit(data):
    owners = {}
    perms = list(permutations(range(COLS)))
    for row in data:
        target = row['mask']
        oldrows = [(target >> (COLS*r)) & ((1 << COLS)-1) for r in range(ROWS)]
        orbit = set()
        for perm in perms:
            rt = [sum(((s >> perm[c]) & 1) << c for c in range(COLS)) for s in oldrows]
            for p in permutations(rt):
                orbit.add(sum(v << (COLS*i) for i, v in enumerate(p)))
        if len(orbit) != row['orbit'] or min(orbit) != target:
            raise ValueError(f'incorrect canonical representative or orbit size: {target}')
        for member in orbit:
            if member in owners:
                raise ValueError(f'overlapping orbits of {owners[member]} and {target}')
            owners[member] = target
    if set(owners) != set(range(FULL+1)):
        raise ValueError(f'orbits cover only {len(owners)} masks')
    return len(owners)


def find_below(target, lower):
    """Search depth <= lower-1; return explicit truth-column trace if SAT.

    A coordinate is a complete 15-bit function. A transition consumes two,
    inserts their union or intersection, and independently retains zero, one
    or both consumed operands. A minimal DAG orders its gates topologically
    and retains an operand iff it has a future use, so its useful live set
    occurs in this search. Constant, repeated, and identity gates can be
    dropped without increasing size. For a nonconstant function on <=k
    binary gates, its trimmed connected graph uses at most k+1 input names.
    """
    checked = Counter()
    if not 0 <= target <= FULL or not isinstance(lower, int) or lower < 0:
        raise ValueError((target, lower))
    k = lower - 1
    if k < 0:
        return None, checked
    if target in (0, FULL):
        minimum = int(target == FULL)   # 0: missing output; 1: empty AND (no raw input is 1).
        return (('constant', target, minimum) if k >= minimum else None), checked
    if target in INPUTS:
        return ('input', INPUTS.index(target)), checked

    # Each set bit is one ordered (target-positive, target-negative) pair.
    # w separates the pair if w(positive)=1 and w(negative)=0. Every monotone
    # recombination needs at least one such surviving coordinate for every pair.
    pairs = [(p,n) for p in CELLS if target >> p & 1 for n in CELLS if not target >> n & 1]
    must_cover = (1 << len(pairs)) - 1
    sep = {}
    def separates(w):
        if w not in sep:
            sep[w] = sum(1 << t for t, (p,n) in enumerate(pairs) if w >> p & 1 and not w >> n & 1)
        return sep[w]

    dead = set()
    def dfs(columns, steps):
        if target in columns:
            return ()
        if steps == 0 or len(columns) > steps + 1:
            return None
        key = (steps, columns)
        if key in dead:
            return None
        dead.add(key)  # safe before the call: steps strictly decreases on each edge.
        checked['states'] += 1
        ss = 0
        for w in columns:
            ss |= separates(w)
        if ss != must_cover:
            return None
        if steps == 1:
            for a,b in combinations(columns,2):
                if a & b == target:
                    return (('and',a,b,target),)
                if a | b == target:
                    return (('or',a,b,target),)
            return None
        for a,b in combinations(columns,2):
            remaining = columns.difference((a,b))
            for op, z in (('or',a|b), ('and',a&b)):
                if z in columns or z == 0 or z == FULL:
                    continue
                if z == target:
                    return ((op,a,b,z),)
                base = remaining.union((z,))
                for keep in ((), (a,), (b,), (a,b)):
                    if len(base)+len(keep) <= steps:
                        res = dfs(base.union(keep), steps-1)
                        if res is not None:
                            return ((op,a,b,z),) + res
        return None

    # Enumerate *every* allowed initial support, without using the catalog's
    # support hints. A one-hot circuit using no input is constant.
    for cardinality in range(1,min(len(INPUTS),k+1)+1):
        for choice in combinations(INPUTS,cardinality):
            checked['supports'] += 1
            result = dfs(frozenset(choice), k)
            if result is not None:
                return (choice, result), checked
    return None, checked


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('catalog', type=Path)
    ap.add_argument('--result', type=Path)
    args = ap.parse_args()
    catalog = json.loads(args.catalog.read_text())
    n = orbit_audit(catalog)
    total, histogram = Counter(), Counter()
    records, mismatch = [], []
    for row in catalog:
        target, lower = row['mask'], row['size']
        sat, counts = find_below(target, lower)
        status = 'NO_SMALLER' if sat is None else 'COUNTEREXAMPLE'
        records.append({'mask':target,'lower':lower,'status':status,**counts})
        if sat is not None:
            records[-1]['trace'] = sat
            mismatch.append((target,lower,sat))
        total.update(counts)
        histogram[lower] += 1
    run = {'classes':len(catalog),'labeled_masks':n,'mismatches':len(mismatch),
           'class_histogram':dict(sorted(histogram.items())),**total,'records':records}
    if args.result:
        args.result.write_text(json.dumps(run,indent=1)+'\n')
    print(json.dumps({k:v for k,v in run.items() if k!='records'},sort_keys=True))
    for x in mismatch:
        print('COUNTEREXAMPLE', x)
    return bool(mismatch)


if __name__ == '__main__':
    raise SystemExit(main())
