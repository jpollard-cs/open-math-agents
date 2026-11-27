"""Reproduce the prime-11 witnesses and the pool bounds using Python 3.

Run in period-budget. Use --seeds to replay the cap-60 deletion checks.
Use --all-seeds once the earlier cap-96 verifier is compiled to repeat every seed irreducibility check.
Pass --export DIRECTORY to write the complete residue assignments.
"""
import argparse
import json
from math import gcd, lcm
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--seeds', action='store_true')
parser.add_argument('--all-seeds', action='store_true')
parser.add_argument('--export', type=Path)
args = parser.parse_args()
sys.path.append(str(here.parent / 'reciprocal-sums'))
from enumerate_covers import modulus_pool

data = json.loads((here / 'prime11-seeds.json').read_text())
cofactors = [*range(1, 11), 12]
assert lcm(*cofactors) == 2520
branches = {11*c: (2520*i) % (11*c) for i, c in enumerate(cofactors)}
assert len({r % 11 for r in branches.values()}) == 11
assert all(r % (d//11) == 0 for d, r in branches.items())

published_bases = {
    26: 'witness26.jsonl', 27: 'witness27-fast.jsonl', 28: 'witness28-second.jsonl',
    29: 'witness29.jsonl', 30: 'witness30.jsonl', 31: 'witness31-upper108.jsonl',
    32: 'witness32-upper108.jsonl', 33: 'witness33-upper108.jsonl',
}


def support(rows, period):
    hit = bytearray(period)
    for d, r in rows.items():
        assert period % d == 0 and 0 <= r < d
        hit[r::d] = bytes([1]) * (period // d)
    return hit


def verify_small_seed(moduli):
    from section_solver import reduced
    for i in range(len(moduli)):
        assert not reduced(tuple(moduli[:i] + moduli[i+1:]))


def verify_larger_seed(size, seed):
    from decide96 import decide
    base = set(seed)
    if size >= 31:
        assert {n for n in base if n % 27 == 0} == {27, 54, 108}
        assert 36 not in base
        base = (base - {27, 54, 108}) | {36}
        # The saturated ternary contraction preserves irreducibility and
        # gives one of the previously checked distinct old sets.
        oldfile = {31:'witness29.jsonl', 32:'witness30.jsonl', 33:'witness31-96.jsonl'}[size]
        assert base == set(dict(json.loads((here / oldfile).read_text().splitlines()[0])))
    if base in verified_bases:
        return
    for n in base:
        assert not decide(tuple(sorted(base - {n})))
    verified_bases.append(base)


verified_bases = []
assert [record['size'] for record in data] == list(range(18, 34))
if args.export:
    args.export.mkdir(parents=True, exist_ok=True)
for record in data:
    size, d = record['size'], record['removed']
    seed = dict(record['rows'])
    assert len(record['rows']) == len(seed) == size
    assert seed[d] == 0 and 2520 % d == 0
    if size in published_bases:
        existing = dict(json.loads((here / published_bases[size]).read_text().splitlines()[0]))
        assert set(seed) == set(existing)
        if args.all_seeds:
            verify_larger_seed(size, seed)
    elif args.seeds or args.all_seeds:
        verify_small_seed(sorted(seed))
    ordinary = seed.copy()
    ordinary.pop(d)
    period = lcm(2520, *ordinary)
    assert gcd(11, period) == 1
    holes = [x for x, hit in enumerate(support(ordinary, period)) if not hit]
    assert holes and all(x % 2520 == 0 for x in holes)
    assert all(support(seed, period))
    rows = ordinary | branches
    assert len(rows) == size + 10 and max(rows) == 132
    full_period = lcm(*rows)
    assert all(support(rows, full_period))
    if args.export:
        (args.export / f'size-{len(rows)}.json').write_text(json.dumps(sorted(rows.items())) + '\n')
    print(f'size {len(rows):2}: seed {size}, distinguished {d:2}, '
          f'{len(holes)} ordinary holes per {period}, full period {full_period}')

if args.all_seeds:
    print(f'Seed irreducibility: {sum(range(18,26))} cap-60 deletions and '
          f'{sum(map(len, verified_bases))} larger-base deletions checked.')

pool108 = set(modulus_pool(108))
for cap, expected in [(111, []), (119, [112]), (125, [112, 120]), (131, [112, 120, 126])]:
    extra = sorted(set(modulus_pool(cap)) - pool108)
    assert extra == expected
    print(f'cap {cap}: additions {extra}, excludes sizes from {36+len(extra)}')
assert set(modulus_pool(132)) - set(modulus_pool(131)) == set(branches)
assert modulus_pool(134) == modulus_pool(132)
assert len(set(modulus_pool(134)) - pool108) == 14
print('cap 134: fourteen additions, excludes sizes from 50')

# Confirm the exact "every 36-subset contains a cover" inference from the
# cited old noncover classification and the 33-row proper cover of G.
from itertools import combinations
p96 = set(json.loads((here / 'census31-32.json').read_text())['pool96'])
p105 = p96 | {105}
h = (p105 - {2, 3, 4})
witness = dict(json.loads((here / 'size36-proper-subset.json').read_text()))
assert len(h) == 33 and all(support(witness, lcm(*witness)))
for excluded in combinations(pool108, len(pool108)-36):
    candidate = pool108 - set(excluded)
    old = candidate & p105
    assert len(old) >= 33
    assert len(old) > 33 or old != h or set(witness) < candidate
print('Every 36-subset of the cap-108 pool passes the cited lower-bound alternatives.')
