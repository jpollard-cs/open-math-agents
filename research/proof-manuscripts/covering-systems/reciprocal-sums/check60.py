"""Verify the size 24 and 25 witnesses and finite exclusions using the catalog."""
from collections import Counter
from itertools import combinations
from math import lcm
from pathlib import Path
import json

import enumerate_covers as general
from section_solver import reduced

def candidate_counts(catalog, cap, size):
    pool = general.modulus_pool(cap)
    bits = {n: 1 << i for i, n in enumerate(pool)}
    def mask(row):
        return sum(bits[n] for n in row)
    smaller = [mask(row) for row in catalog if len(row) < size]
    return sum(not any((m & s) == s for s in smaller)
               for m in map(mask, combinations(pool, size)))

def main():
    catalog = json.loads(Path('full-60.json').read_text())
    counts = Counter(map(len, catalog))
    assert (len(catalog), counts[24], counts[25], max(counts)) == (10149,11,1,25)
    assert all(len(row) <= 23 for row in catalog if max(row)<60)
    old = json.loads(Path('full-56.json').read_text())
    assert {tuple(s) for s in old} == {tuple(s) for s in catalog if max(s)<=56}
    examples = json.loads(Path('witnesses-24-25.json').read_text())
    general.can_cover = reduced
    for k, data in examples.items():
        moduli, residues = data['moduli'],data['residues']
        assert len(set(moduli)) == len(moduli) == len(residues) == int(k)
        assert moduli in catalog and max(moduli) == 60
        period = lcm(*moduli)
        assert period == data['period']
        assert all(any((x-a)%n == 0 for n,a in zip(moduli,residues)) for x in range(period))
        for i in range(len(moduli)):
            assert not reduced(tuple(moduli[:i] + moduli[i+1:]))
        print('Verified full period and every one-modulus deletion for size',k)
    for cap, k in [(69,26),(71,27),(79,28),(83,29),(89,30),(95,31)]:
        remaining=candidate_counts(catalog,cap,k)
        assert remaining == 0
        print('Every',k,'subset at cap',cap,'contains a smaller cover.')
if __name__=='__main__':
    main()
