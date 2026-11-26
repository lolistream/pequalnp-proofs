"""Verify every 3×5 witness, query a labeled mask, or replay every lower bound.

  python3 -I check.py
  python3 -I check.py --query 7548
  python3 -I check.py --frontier /absolute/path/to/frontier
"""
import argparse
from collections import Counter
from itertools import permutations
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
RAW = [31, 992, 31744, 1057, 2114, 4228, 8456, 16912]
PERMS = [list(r) + [3+j for j in c]
         for r in permutations(range(3)) for c in permutations(range(5))]
X = [(1 << (p//5)) | (1 << (3+p%5)) for p in range(15)]


def verify_upper(row, ren):
    vals = [RAW[i] for i in ren]
    for op, *ids in row['gates']:
        assert op in ('or', 'and') and len(ids) <= 2
        assert all(type(j) is int and 0 <= j < len(vals) for j in ids)
        result = 0 if op == 'or' else 32767
        for j in ids:
            result = result | vals[j] if op == 'or' else result & vals[j]
        vals.append(result)
    out = row['output']
    assert type(out) is int and out >= 0
    return vals[out] if out < len(vals) else 0


def allowed_supports(mask, budget):
    required = {X[p] & ~X[q] for p in range(15) if mask >> p & 1
                for q in range(15) if not mask >> q & 1}
    return {s for s in range(1, 256) if s.bit_count() <= budget+1 and all(s & t for t in required)}


def verify_lower(row, program, seconds):
    m, n = row['mask'], row['size']
    if n == 0: return  # the cost is a natural number
    if m == 32767:
        assert n == 1 and 32767 not in RAW  # no zero-gate output, including out of range, is true everywhere
        return
    budget = n-1
    run = subprocess.run([str(program), str(m), str(budget), str(seconds)],
                         capture_output=True, text=True, timeout=seconds+30)
    if run.returncode != 0:
        raise RuntimeError(f'lower bound INCOMPLETE for mask {m} at {budget}: exit {run.returncode}')
    obj = json.loads(run.stdout); profiles = obj['profiles']; allowed = allowed_supports(m, budget)
    assert obj['mask'] == m and obj['budget'] == budget and obj['status'] == 'unsat', (m, obj)
    assert obj['feasible_supports'] == len(allowed) == len(profiles)
    assert {s for s,*_ in profiles} == allowed and all(line[-1] == 'unsat' for line in profiles)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--query', type=lambda s:int(s,0), help='produce a witness for a particular 15-bit mask')
    ap.add_argument('--frontier', type=Path, help='also run a compiled frontier.cc for every one-gate-smaller bound')
    ap.add_argument('--seconds', type=int, default=30, help='time allowance per lower-bound search')
    args = ap.parse_args()
    if args.seconds < 1 or (args.query is not None and not 0 <= args.query <= 32767): ap.error('invalid budget or mask')
    binary = args.frontier.resolve(strict=True) if args.frontier else None
    rows = json.loads((HERE/'atlas.json').read_text()); assert len(rows) == len({r['mask'] for r in rows}) == 190
    histogram = Counter(); covered = set(); answer = None
    for row in rows:
        m, n = row['mask'], row['size']; assert type(m) is int and 0 <= m < 32768 and len(row['gates']) == n
        orbit = set()
        for ren in PERMS:
            target = sum(((m >> (5*u+v)) & 1) << (5*ren[u]+ren[3+v]-3) for u in range(3) for v in range(5))
            assert verify_upper(row, ren) == target  # checks all 15 assignments, including every relabeling
            orbit.add(target)
            if target == args.query and answer is None:
                def wire(j): return ren[j] if j < 8 else j
                answer = {'rows':3,'cols':5,'mask':target,'size':n,'canonical_mask':m,
                          'gates':[[op, *(wire(j) for j in ids)] for op,*ids in row['gates']],
                          'output':wire(row['output'])}
                assert verify_upper(answer, list(range(8))) == target
        assert len(orbit) == row['orbit'] and min(orbit) == m and orbit.isdisjoint(covered)
        covered.update(orbit); histogram[n] += len(orbit)
        if binary: verify_lower(row, binary, args.seconds)
    assert covered == set(range(32768))
    if answer is not None: print(json.dumps(answer, separators=(',',':')))
    else:
        print('Verified witnesses for 190 orbits, all 32768 labeled relations. Labeled sizes:', sorted(histogram.items()))
        if binary: print('All one-gate-smaller bounds independently rerun from the archived search source; no timeouts or incomplete profiles.')
        else: print('Upper-bound and orbit checks only. Pass --frontier to replay the lower bounds.')

if __name__ == '__main__': main()
