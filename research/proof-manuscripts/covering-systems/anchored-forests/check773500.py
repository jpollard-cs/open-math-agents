"""Independently check the public residue certificate both by CRT and by an integer bit mask."""
import json
from itertools import product
from pathlib import Path
from math import prod

def verify():
    data = json.loads(Path(__file__).with_name("candidate773500.json").read_text())
    period = 773500
    assert data['period'] == period
    congruences = data['modulus_residue']
    divisors = {n for n in range(2, period+1) if period%n == 0}
    assert len(congruences) == len(divisors) == 95
    assert {n for n,a in congruences} == divisors
    assert all(0 <= a < n for n,a in congruences)
    full = (1 << period)-1
    covered = 0
    for n,a in congruences:
        covered |= ((full // ((1 << n)-1)) << a)
    missing = full ^ covered
    recorded = data['uncovered']
    assert sum(1 << i for i in recorded) == missing and len(set(recorded)) == 8

    # Project each surviving old class separately onto the 13 by 17 grid.
    pure = [(n,a) for n,a in congruences if 3500%n == 0]
    old = [u for u in range(3500) if all(u%n != a for n,a in pure)]
    assert len(old) == 35
    crt_holes = []
    for x in old:
        admissible = []
        for n,a in congruences:
            d = n // prod(p for p in (13,17) if n%p == 0)
            if x%d == a%d:
                admissible.append((n,a))
        for y,z in product(range(13),range(17)):
            if any((n%13 or y == a%13) and (n%17 or z == a%17) for n,a in admissible):
                continue
            crt_holes.append((x*221*pow(221,-1,3500)
                              + y*59500*pow(59500,-1,13)
                              + z*45500*pow(45500,-1,17)) % period)
    assert sorted(crt_holes) == sorted(recorded)
    # The residues with modulus not divisible by 125 leave 166 points of
    # the remaining 7-by-13-by-17 grid above the single base-25 residue.
    low = [(n,a) for n,a in congruences if n%125]
    parents = [v for v in range(period//5) if all(v%n != a for n,a in low)]
    assert len(parents)==166 and {v%25 for v in parents}=={0}
    print('95 distinct moduli; 773492 covered; eight explicitly verified holes:',sorted(recorded))
    print('Two independent checks agree; the lower 5-adic levels leave 166 holes modulo 154700.')
if __name__=='__main__':
    verify()
